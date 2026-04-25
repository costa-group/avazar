"""
Module for useful methods applies to the classes in core.py
"""

from llzk_dialects.core import SSAVar, TranslationContext, Type
from llzk_dialects.utils import translate_assignment_core


def translate_assignment_core_with_ctx(lhs: SSAVar, rhs: SSAVar, type_: Type, ctx: TranslationContext) -> str:
    """
    Generates a str with the translation of an assignment in core. Moreover,
    it updates the context if rhs corresponds to a variable that evaluates to a constant
    """
    is_ff = "array" not in type_.name

    if is_ff:
        # Only check constants in case it is a ff
        const = ctx.var2const.get(rhs.name)
        if const is not None:
            ctx.var2const[lhs.name] = const

    return translate_assignment_core(lhs.to_core(), rhs.to_core(), is_ff)

