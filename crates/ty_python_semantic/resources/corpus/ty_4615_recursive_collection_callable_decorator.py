# Regression test for https://github.com/astral-sh/ty/issues/4615

@0
@lambda cls: {replacement}
class C:
    pass

if condition:
    raise ValueError

@{**(lambda: replacement)}
def replacement():
    pass

replacement = C
