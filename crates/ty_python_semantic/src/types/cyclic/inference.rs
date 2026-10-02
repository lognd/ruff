//! Preserve recursive inputs that generic argument inference must destructure.
//!
//! Inferring `T` from a recursive marker passed to `tuple[T]` normally produces `Never`:
//! there are no tuple elements to inspect yet. That loses the back-reference needed to
//! normalize a call such as `grow[T](x: tuple[T]) -> tuple[list[T]]` in a loop.
//!
//! A projection records the formal input and the parameter that would be extracted from it.
//! We carry that symbolic parameter through calls until the original query recovers. Comparing
//! the complete result with the formal input distinguishes accumulating structure from a finite
//! permutation, a reset, or cancellation such as `unwrap(wrap(x))`. Only a parameter-flow cycle
//! containing a nested edge is recovered to a recursive marker.

use std::cell::RefCell;

use rustc_hash::FxHashSet;

use super::{FlowEdge, FlowKind, SourceParameterCollector, SpecializationFlowGraph};
use crate::types::generics::GenericContext;
use crate::types::visitor::any_over_type_including_alias_arguments;
use crate::types::{
    BoundTypeVarIdentity, BoundTypeVarInstance, DivergentFlags, DivergentOrigin, DivergentType,
    Type, TypeContext, TypeMapping, UnionType,
};
use crate::{Db, FxOrderMap, ProgramEnvironment};

/// A parameter extracted from a recursive query result whose structure is not yet available.
#[salsa::interned(debug, heap_size=ruff_memory_usage::heap_size)]
pub(in crate::types) struct RecursiveInferenceProjection<'db> {
    #[returns(copy)]
    root: DivergentType<'db>,
    #[returns(copy)]
    context: GenericContext<'db>,
    #[returns(copy)]
    formal: Type<'db>,
    #[returns(copy)]
    parameter: BoundTypeVarInstance<'db>,
}

// The Salsa heap is tracked separately.
impl get_size2::GetSize for RecursiveInferenceProjection<'_> {}

/// Return corresponding arguments only when both types have the same constructor and shape.
/// Declaration bounds, members, and callable parameter lists are not structural arguments here.
fn matching_arguments<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    left: Type<'db>,
    right: Type<'db>,
) -> Option<(Vec<Type<'db>>, Vec<Type<'db>>)> {
    match (left, right) {
        (Type::NominalInstance(_), Type::NominalInstance(_)) => {
            match (
                left.exact_tuple_instance_spec(db),
                right.exact_tuple_instance_spec(db),
            ) {
                (Some(left), Some(right)) => {
                    let left = left.as_fixed_length()?;
                    let right = right.as_fixed_length()?;
                    return (left.len() == right.len()).then(|| {
                        (
                            left.elements_slice().to_vec(),
                            right.elements_slice().to_vec(),
                        )
                    });
                }
                (None, None) => {}
                _ => return None,
            }
        }
        (Type::GenericAlias(left), Type::GenericAlias(right)) => {
            let left_args = left.specialization(db);
            let right_args = right.specialization(db);
            return (left.origin(db) == right.origin(db)
                && left_args.tuple(db).is_none()
                && right_args.tuple(db).is_none()
                && left_args.materialization_kind(db) == right_args.materialization_kind(db))
            .then(|| (left_args.types(db).to_vec(), right_args.types(db).to_vec()));
        }
        (Type::TypedDict(_), Type::TypedDict(_)) => {}
        (Type::TypeGuard(left), Type::TypeGuard(right)) => {
            return (left.place_info(db) == right.place_info(db))
                .then(|| (vec![left.return_type(db)], vec![right.return_type(db)]));
        }
        (Type::TypeIs(left), Type::TypeIs(right)) => {
            return (left.place_info(db) == right.place_info(db)
                && left.materialization_kind(db) == right.materialization_kind(db))
            .then(|| (vec![left.return_type(db)], vec![right.return_type(db)]));
        }
        (Type::Callable(left), Type::Callable(right)) => {
            let ([left_signature], [right_signature]) = (
                left.signatures(db).overloads.as_slice(),
                right.signatures(db).overloads.as_slice(),
            ) else {
                return None;
            };
            return (left.kind(db) == right.kind(db)
                && left_signature.generic_context.is_none()
                && right_signature.generic_context.is_none()
                && left_signature.parameters().is_standard()
                && right_signature.parameters().is_standard()
                && left_signature.parameters().as_slice().is_empty()
                && right_signature.parameters().as_slice().is_empty())
            .then(|| {
                (
                    vec![left_signature.return_ty],
                    vec![right_signature.return_ty],
                )
            });
        }
        _ => return None,
    }
    let (left_class, left_args) = left.class_specialization(db, env)?;
    let (right_class, right_args) = right.class_specialization(db, env)?;
    (left_class == right_class
        && left_args.tuple(db).is_none()
        && right_args.tuple(db).is_none()
        && left_args.materialization_kind(db) == right_args.materialization_kind(db))
    .then(|| (left_args.types(db).to_vec(), right_args.types(db).to_vec()))
}

/// Match a query's symbolic result against its recursive input, collecting parameter flow.
fn collect_flow<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    parameters: &FxHashSet<BoundTypeVarIdentity<'db>>,
    formal: Type<'db>,
    returned: Type<'db>,
    edges: &mut FxHashSet<FlowEdge<'db>>,
) -> bool {
    if let Type::Union(union) = returned {
        return union
            .elements(db)
            .iter()
            .all(|returned| collect_flow(db, env, parameters, formal, *returned, edges));
    }
    if let Type::TypeVar(parameter) = formal {
        let to = parameter.identity(db);
        if !parameters.contains(&to) {
            return formal == returned;
        }
        edges.extend(
            SourceParameterCollector::classify(db, env, parameters, returned)
                .map(|(from, kind)| FlowEdge { from, to, kind }),
        );
        return true;
    }
    let Some((left, right)) = matching_arguments(db, env, formal, returned) else {
        return formal == returned;
    };
    left.len() == right.len()
        && left
            .into_iter()
            .zip(right)
            .all(|(left, right)| collect_flow(db, env, parameters, left, right, edges))
}

/// Find parameters that gain structure when the result is fed back into a destructured argument.
pub(in crate::types) fn structurally_growing_parameters<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    context: GenericContext<'db>,
    formal: Type<'db>,
    returned: Type<'db>,
) -> FxHashSet<BoundTypeVarIdentity<'db>> {
    // Direct type-variable arguments already preserve recursive markers without projections.
    if matches!(formal, Type::TypeVar(_)) {
        return FxHashSet::default();
    }
    let parameters: FxHashSet<_> = context
        .variables(db)
        .map(|parameter| parameter.identity(db))
        .collect();
    let mut graph = SpecializationFlowGraph::default();
    if !collect_flow(db, env, &parameters, formal, returned, &mut graph.edges) {
        return FxHashSet::default();
    }
    let components = graph.strongly_connected_parameter_components(parameters.clone());
    parameters
        .into_iter()
        .filter(|parameter| {
            graph.edges.iter().any(|edge| {
                edge.kind == FlowKind::Nested
                    && components.get(&edge.from) == components.get(&edge.to)
                    && components.get(&edge.from) == components.get(parameter)
            })
        })
        .collect()
}

/// Recover a finite parameter from concrete alternatives beside its symbolic projection.
/// This preserves unchanged fields when another field in the same argument grows.
fn projection_evidence<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    formal: Type<'db>,
    returned: Type<'db>,
    parameter: BoundTypeVarInstance<'db>,
) -> Type<'db> {
    if let Type::Union(union) = returned {
        return UnionType::from_elements_cycle_recovery(
            db,
            env,
            union
                .elements(db)
                .iter()
                .map(|returned| projection_evidence(db, env, formal, *returned, parameter)),
        );
    }
    if formal == Type::TypeVar(parameter) {
        return if any_over_type_including_alias_arguments(db, env, returned, |ty| ty.is_divergent())
        {
            Type::Never
        } else {
            returned
        };
    }
    if let Some((left, right)) = matching_arguments(db, env, formal, returned) {
        return UnionType::from_elements_cycle_recovery(
            db,
            env,
            left.into_iter()
                .zip(right)
                .map(|(left, right)| projection_evidence(db, env, left, right, parameter)),
        );
    }
    Type::Never
}

/// Find argument components that a call returns unchanged, including their concrete constraints.
/// An invariant component can bound another component that grows in the same argument.
pub(in crate::types) fn unchanged_recursive_arguments<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    formal: Type<'db>,
    actual: Type<'db>,
    returned: Type<'db>,
) -> Vec<(Type<'db>, Type<'db>)> {
    if let Type::Union(union) = actual {
        return union
            .elements(db)
            .iter()
            .flat_map(|actual| unchanged_recursive_arguments(db, env, formal, *actual, returned))
            .collect();
    }
    if formal == returned && !matches!(formal, Type::TypeVar(_)) {
        return vec![(formal, actual)];
    }
    let Some((left, output)) = matching_arguments(db, env, formal, returned) else {
        return Vec::new();
    };
    let input = if actual.is_divergent() {
        vec![actual; left.len()]
    } else if let Some((_, input)) = matching_arguments(db, env, formal, actual) {
        input
    } else {
        return Vec::new();
    };
    if left.len() != input.len() || left.len() != output.len() {
        return Vec::new();
    }
    left.into_iter()
        .zip(input)
        .zip(output)
        .flat_map(|((formal, actual), returned)| {
            unchanged_recursive_arguments(db, env, formal, actual, returned)
        })
        .collect()
}

/// Seed parameters whose formal argument structure is hidden by a recursive marker.
fn project<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    context: GenericContext<'db>,
    parameters: &FxHashSet<BoundTypeVarIdentity<'db>>,
    formal: Type<'db>,
    actual: Type<'db>,
    projections: &mut Vec<(BoundTypeVarInstance<'db>, Type<'db>)>,
) {
    // Ordinary inference already preserves a marker passed directly to a type variable.
    if matches!(formal, Type::TypeVar(_)) {
        return;
    }
    if let Type::Divergent(divergent) = actual
        && let DivergentOrigin::Recursive(_) = divergent.origin
    {
        // Ordinary generic classes retain recursive argument markers. Fixed tuples instead
        // infer their parameters by destructuring elements that are not available yet. Once
        // growth is established, propagate its marker through the resulting nested types too.
        if !divergent.flags.contains(DivergentFlags::GROWING_PROJECTION)
            && formal
                .exact_tuple_instance_spec(db)
                .is_none_or(|tuple| tuple.as_fixed_length().is_none())
        {
            return;
        }
        let sources: FxHashSet<_> = SourceParameterCollector::classify(db, env, parameters, formal)
            .map(|(parameter, _)| parameter)
            .collect();
        // Constraint insertion follows declaration order, independent of hash iteration order.
        for parameter in context
            .variables(db)
            .filter(|parameter| sources.contains(&parameter.identity(db)))
        {
            let origin = if divergent.flags.contains(DivergentFlags::GROWING_PROJECTION) {
                divergent.origin
            } else {
                DivergentOrigin::Projection(RecursiveInferenceProjection::new(
                    db, divergent, context, formal, parameter,
                ))
            };
            projections.push((
                parameter,
                Type::Divergent(DivergentType {
                    origin,
                    ..divergent
                }),
            ));
        }
    } else if let Type::Union(union) = actual {
        for element in union.elements(db) {
            project(db, env, context, parameters, formal, *element, projections);
        }
    } else if let Some((left, right)) = matching_arguments(db, env, formal, actual)
        && left.len() == right.len()
    {
        for (left, right) in left.into_iter().zip(right) {
            project(db, env, context, parameters, left, right, projections);
        }
    }
}

/// Infer symbolic parameters for recursive arguments to an unbounded generic signature.
pub(in crate::types) fn recursive_call_projections<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    context: GenericContext<'db>,
    formal: Type<'db>,
    actual: Type<'db>,
) -> Vec<(BoundTypeVarInstance<'db>, Type<'db>)> {
    // Bounds and constraints can stop an otherwise growing sequence at a concrete type.
    // Variadic parameters also need a different structural matching rule.
    if context.variables(db).any(|parameter| {
        let typevar = parameter.typevar(db);
        typevar.is_paramspec(db)
            || typevar.is_typevartuple(db)
            || typevar.bound_or_constraints(db, env).is_some()
    }) {
        return Vec::new();
    }
    let parameters = context
        .variables(db)
        .map(|parameter| parameter.identity(db))
        .collect();
    let mut projections = Vec::new();
    project(
        db,
        env,
        context,
        &parameters,
        formal,
        actual,
        &mut projections,
    );
    projections
}

/// Recover projections only at their originating query, after all intervening calls have run.
/// Preserve finite fields alongside a growing parameter using ordinary inference's evidence.
/// If there is no growing parameter, discard the symbolic seed and use the concrete alternatives.
pub(in crate::types) fn resolve_recursive_projections<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
    cycle: &salsa::Cycle,
) -> Type<'db> {
    let projected = RefCell::new(FxOrderMap::<DivergentType<'db>, Type<'db>>::default());
    any_over_type_including_alias_arguments(db, env, ty, |nested| {
        if let Type::Divergent(divergent) = nested
            && let DivergentOrigin::Projection(projection) = divergent.origin
            && projection.root(db).origin == DivergentOrigin::Recursive(cycle.id())
        {
            projected
                .borrow_mut()
                .insert(divergent, Type::TypeVar(projection.parameter(db)));
        }
        false
    });
    let mut replacements = projected.into_inner();
    if replacements.is_empty() {
        return ty;
    }
    let symbolic = ty.apply_type_mapping(
        db,
        env,
        &TypeMapping::ReplaceRecursiveProjections(&replacements),
        TypeContext::default(),
    );
    for (divergent, replacement) in &mut replacements {
        let DivergentOrigin::Projection(projection) = divergent.origin else {
            continue;
        };
        let growing = structurally_growing_parameters(
            db,
            env,
            projection.context(db),
            projection.formal(db),
            symbolic,
        );
        *replacement = if growing.contains(&projection.parameter(db).identity(db)) {
            Type::Divergent(DivergentType {
                origin: projection.root(db).origin,
                flags: divergent.flags | DivergentFlags::GROWING_PROJECTION,
                ..*divergent
            })
        } else if !growing.is_empty() {
            projection_evidence(db, env, projection.formal(db), ty, projection.parameter(db))
        } else {
            Type::Never
        };
    }
    ty.apply_type_mapping(
        db,
        env,
        &TypeMapping::ReplaceRecursiveProjections(&replacements),
        TypeContext::default(),
    )
}

/// Remove symbolic union alternatives before a call whose overloads may change parameter flow.
/// Replacing only the projection with `Never` could create a real type such as `list[Never]`;
/// that type would take part in subsequent iterations instead of remaining a provisional seed.
pub(in crate::types) fn discard_recursive_projections<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: Type<'db>,
) -> Type<'db> {
    let discard = |ty| {
        if any_over_type_including_alias_arguments(
            db,
            env,
            ty,
            |nested| matches!(nested, Type::Divergent(divergent) if matches!(divergent.origin, DivergentOrigin::Projection(_))),
        ) {
            Type::Never
        } else {
            ty
        }
    };
    if let Type::Union(union) = ty {
        union.map(db, env, |ty| discard(*ty))
    } else {
        discard(ty)
    }
}
