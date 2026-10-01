# Regression tests for https://github.com/astral-sh/ty/issues/3837.

from collections.abc import Callable
from typing import TypeGuard, TypeIs, TypedDict


def grow[A, B](value: tuple[A, B]) -> tuple[list[A], tuple[A, B]]:
    raise NotImplementedError


def grow_guard[A, B](
    value: tuple[Callable[[], TypeGuard[A]], B],
) -> tuple[Callable[[], TypeGuard[list[A]]], tuple[Callable[[], TypeGuard[A]], B]]:
    raise NotImplementedError


def grow_is[A, B](
    value: tuple[Callable[[], TypeIs[A]], B],
) -> tuple[Callable[[], TypeIs[list[A]]], tuple[Callable[[], TypeIs[A]], B]]:
    raise NotImplementedError


class Payload[A](TypedDict):
    value: A


def grow_payload[A, B](
    value: tuple[Callable[[], Payload[A]], B],
) -> tuple[Callable[[], Payload[list[A]]], tuple[Callable[[], Payload[A]], B]]:
    raise NotImplementedError


def tuple_elements():
    while True:
        value = grow(value)


def guard_arguments():
    while True:
        value = grow_guard(value)


def type_is_arguments():
    while True:
        value = grow_is(value)


def typed_dict_arguments():
    while True:
        value = grow_payload(value)


class Container[T]: ...


def is_container[T](value: object, other: T) -> TypeIs[Container[T]]:
    return True


def bound_method_narrowing():
    while True:
        if is_container(value, type(value)):
            value = value.__str__
        else:
            value = {value}
