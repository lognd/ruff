# Regression test for https://github.com/astral-sh/ty/issues/4607

value = lambda: value
try:
    type Alias = value
finally:
    @[Alias]
    class Example:
        pass

    value = Example
