# Regression tests for https://github.com/astral-sh/ty/issues/3837.

from collections.abc import Callable
from typing import TypeGuard, TypeIs, TypedDict
from typing_extensions import TypeForm


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


class Pair[A, B]: ...


def grow_class[A, B](value: Pair[type[A], B]) -> Pair[type[list[A]], Pair[type[A], B]]:
    raise NotImplementedError


def grow_form[A, B](
    value: Pair[TypeForm[A], B],
) -> Pair[TypeForm[list[A]], Pair[TypeForm[A], B]]:
    raise NotImplementedError


def class_arguments():
    while True:
        value = grow_class(value)


def type_form_arguments():
    while True:
        value = grow_form(value)
