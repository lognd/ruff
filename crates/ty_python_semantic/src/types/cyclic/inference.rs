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
    Type, TypeContext, TypeMapping,
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
/// When growth is not established, discard the extra seed and use ordinary argument inference.
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
        let parameters = projection
            .context(db)
            .variables(db)
            .map(|parameter| parameter.identity(db))
            .collect();
        let mut graph = SpecializationFlowGraph::default();
        let matches = collect_flow(
            db,
            env,
            &parameters,
            projection.formal(db),
            symbolic,
            &mut graph.edges,
        );
        let components = graph.strongly_connected_parameter_components(parameters);
        let parameter = projection.parameter(db).identity(db);
        let grows = matches
            && graph.edges.iter().any(|edge| {
                edge.kind == FlowKind::Nested
                    && components.get(&edge.from) == components.get(&edge.to)
                    && components.get(&edge.from) == components.get(&parameter)
            });
        *replacement = if grows {
            Type::Divergent(DivergentType {
                origin: projection.root(db).origin,
                flags: divergent.flags | DivergentFlags::GROWING_PROJECTION,
                ..*divergent
            })
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
