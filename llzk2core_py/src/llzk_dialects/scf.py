"""
SCF dialect — Structured Control Flow (standard MLIR dialect, used inside LLZK).
Prefix: scf.

Operations:
  SCFYield     — scf.yield     (yield values from a block, used in if/for/while)
  SCFCondition — scf.condition (while-loop condition + pass-through values)
  SCFIf        — scf.if        (BlockOperation: conditional with then/optional else)
  SCFFor       — scf.for       (BlockOperation: counted loop with step)
  SCFWhile     — scf.while     (BlockOperation: pre-condition loop with before/after regions)
"""
import itertools
import re
from typing import List, Optional, Tuple, Generator, Dict, Set, Union

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.core_utils import translate_assignment_core_with_ctx, infer_n_repetitions_from_expressions
from llzk_dialects.felt import FeltBinary, FeltConst
from llzk_dialects.bool import BoolCmp
from llzk_dialects.utils import translate_assignment_core


class SCFYield(Operation):
    """
    Yield values from an scf block (if-branch, for-body, while-body, etc.).

    Syntax: scf.yield [$operands : type($operands)]
    Operands: variadic (any type)
    Traits: Terminator, ReturnLike
    """

    _OPS = {"scf.yield"}

    def __init__(self, operands: List[SSAVar], types: List[Type]):
        self._operands = operands
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in SCFYield._OPS

    @classmethod
    def parse(cls, line: str) -> 'SCFYield':
        # scf.yield
        # scf.yield %v0, %v1 : !felt.type, !felt.type
        pattern = re.compile(
            r"\s*scf\.yield"
            r"(?:\s+(?P<ops>[^:]+)\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse SCFYield: {line}")
        operands = (
            [SSAVar.parse(o.strip()) for o in m["ops"].split(",") if o.strip()]
            if m["ops"] else []
        )
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return SCFYield(operands, types)

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # It uses "current_yield" inside the context to retrieve
        # the name of the variable that is used as a result and performs
        # all the assignments for each component
        yield_res_index = 0
        for result in ctx.scf_result:
            for component in range(result.n_components):
                # Retrieve the component and the yield operand at current
                # index "yield_res_index"
                lhs = result.to_core_component(component)
                rhs = self._operands[yield_res_index].to_core()
                type_ = self.types[yield_res_index]

                to_core_type = type_.to_core()
                assert to_core_type is not None, f"Error recognizing type inside a yield expression: {self}"
                # Depending on whether the type corresponds to an array
                # or to a ff, we generate a copy or a direct assignment
                # Here, we don't consider translate_assignment_core_with_ctx because
                # the variables are not constants (they are unfolded depending on the branch)
                yield translate_assignment_core(lhs, rhs, to_core_type == "ff")
                yield_res_index += 1

    @property
    def operands(self) -> List[SSAVar]:
        return self._operands

    def __repr__(self):
        if not self._operands:
            return "SCFYield(scf.yield)"
        ops_str = ', '.join(repr(o) for o in self._operands)
        type_str = ' : ' + ', '.join(repr(t) for t in self.types) if self.types else ''
        return f"SCFYield(scf.yield {ops_str}{type_str})"


class SCFCondition(Operation):
    """
    Terminate the 'before' region of an scf.while, passing the condition
    and any loop-carried values to the 'after' region.

    Syntax: scf.condition($condition) $args [: type($args)]
    Operands: condition (i1), args (variadic — loop-carried values)
    Traits: Terminator
    """

    _OPS = {"scf.condition"}

    def __init__(self, condition: SSAVar, args: List[SSAVar], types: List[Type]):
        self.condition = condition
        self.args = args
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().startswith("scf.condition")

    @classmethod
    def parse(cls, line: str) -> 'SCFCondition':
        # scf.condition(%cond) %arg0, %arg1 : !type, !type
        pattern = re.compile(
            r"\s*scf\.condition\s*\(\s*(?P<cond>\S+)\s*\)"
            r"(?:\s+(?P<args>[^:]+?))?(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse SCFCondition: {line}")
        args = (
            [SSAVar.parse(a.strip()) for a in m["args"].split(",") if a.strip()]
            if m["args"] else []
        )
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return SCFCondition(SSAVar.parse(m["cond"]), args, types)

    @property
    def operands(self) -> List[SSAVar]:
        return [self.condition] + list(self.args)

    def to_core(self, ctx: TranslationContext) -> str:
        # Follows the same idea as the yield operation
        cond_res_index = 0
        for result in ctx.scf_result:
            for component in range(result.n_components):
                # Retrieve the component and the yield operand at current
                # index "yield_res_index"
                lhs = result.to_core_component(component)
                rhs = self.args[cond_res_index].to_core()
                type_ = self.types[cond_res_index]

                to_core_type = type_.to_core()
                assert to_core_type is not None, f"Error recognizing type inside a cond expression: {self}"

                # Depending on whether the type corresponds to an array
                # or to a ff, we generate a copy or a direct assignment
                # Here, we don't consider translate_assignment_core_with_ctx because
                # the variables are not constants (they are unfolded depending on the branch)

                yield translate_assignment_core(lhs, rhs, to_core_type == "ff")
                cond_res_index += 1


    def __repr__(self):
        args_str = (', '.join(repr(a) for a in self.args) + ' ') if self.args else ''
        type_str = ': ' + ', '.join(repr(t) for t in self.types) if self.types else ''
        return f"SCFCondition(scf.condition({self.condition}) {args_str}{type_str})"


class SCFIf(BlockOperation):
    """
    Conditional control flow with a mandatory 'then' block and optional 'else'.

    Syntax:
      [%results =] scf.if $condition [: type($results)] {
        <then body>
      } [else {
        <else body>
      }]

    Both branches are parsed recursively and stored as lists of Operations.
    """

    _OPS = {"scf.if"}

    def __init__(self, results: List[SSAVar], condition: SSAVar,
                 result_types: List[Type],
                 then_body: List[Operation],
                 else_body: Optional[List[Operation]]):
        self.results = results
        self.condition = condition
        self.result_types = result_types
        self.then_body = then_body
        self.else_body = else_body

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return "scf.if" in line

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['SCFIf', int]:
        header = lines[cursor]
        # [%r0, %r1 =] scf.if %cond [-> (!type) | : !type] {
        pattern = re.compile(
            r"\s*(?:(?P<res>[^=]+?)\s*=\s*)?scf\.if\s+(?P<cond>\S+)"
            r"(?:\s*(?:->|:)\s*(?P<types>[^{]+?))?\s*\{"
        )
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse SCFIf header: {header}")

        results = (
            [SSAVar.parse(r.strip()) for r in m["res"].split(",") if r.strip()]
            if m["res"] else []
        )
        result_types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )

        # Find end of 'then' block by tracking depth character-by-character so
        # that "} else {" is correctly treated as closing then before opening else.
        depth = sum(1 if c == '{' else (-1 if c == '}' else 0) for c in header)
        then_end = cursor
        while depth > 0 and then_end + 1 < len(lines):
            then_end += 1
            for ch in lines[then_end]:
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        break  # stop as soon as the first matching } is found

        then_body = parse_fn(cursor + 1, then_end)
        next_cursor = then_end + 1

        # Check for 'else' block: may be on the same line as the closing '}'
        # (i.e. "} else {") or on the next line ("else {").
        else_body = None
        then_close_line = lines[then_end].strip()
        if "else {" in then_close_line or then_close_line == "else {":
            # else block opens on the same line as the then-closing brace.
            # The opening '{' of else is on this line; depth starts at 1.
            else_start = then_end
            depth = 1
            else_end = else_start
            while depth > 0 and else_end + 1 < len(lines):
                else_end += 1
                depth += lines[else_end].count('{') - lines[else_end].count('}')
            else_body = parse_fn(else_start + 1, else_end)
            next_cursor = else_end + 1
        elif next_cursor < len(lines) and lines[next_cursor].strip() == "else {":
            else_start = next_cursor
            depth = 1
            else_end = else_start
            while depth > 0 and else_end + 1 < len(lines):
                else_end += 1
                depth += lines[else_end].count('{') - lines[else_end].count('}')
            else_body = parse_fn(else_start + 1, else_end)
            next_cursor = else_end + 1

        return (
            SCFIf(results, SSAVar.parse(m["cond"]), result_types,
                  then_body, else_body),
            next_cursor,
        )

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # If translation:
        # * The condition corresponds to a variable. Hence, we transform it to if(var == 1),
        #   as 1 is for true in CORE.
        # * Then we translate the body of the if and of the else. The transformation here just
        #   needs to consider that "scf.yield" assigns the variables yielded to the results
        #   (which can be multiple)
        yield f"if ({self.condition.to_core()} == 1) {{"
        yield from self._translate_branch(self.then_body, ctx)
        yield "}\n"
        yield "else {"
        yield from self._translate_branch(self.else_body, ctx)
        yield "}"

    def _translate_branch(self, branch_ops: List[Operation], ctx: TranslationContext) -> Generator[str, None, None]:
        assert isinstance(branch_ops[-1], SCFYield), "Last instruction of SCFIf must be a yield"

        for statement in branch_ops[:-1]:
            # Process all the operands as usual, except for the scf.yield
            yield from statement.to_core(ctx)

        # For the yield operation, we must retrieve the results variables
        ctx.scf_result = self.results
        yield from branch_ops[-1].to_core(ctx)
        ctx.scf_result = []

    def update_variables(self, rename: Dict[str, str]) -> None:
        if self.condition.name in rename:
            self.condition.name = rename[self.condition.name]
        for r in self.results:
            if r.name in rename:
                r.name = rename[r.name]
        for op in self.then_body:
            op.update_variables(rename)
        if self.else_body:
            for op in self.else_body:
                op.update_variables(rename)

    def __repr__(self):
        res_str = (', '.join(repr(r) for r in self.results) + ' = ') if self.results else ''
        then_str = '\n  '.join(repr(op) for op in self.then_body)
        else_str = (' else {\n  ' + '\n  '.join(repr(op) for op in self.else_body) + '\n}'
                    if self.else_body else '')
        return (f"SCFIf({res_str}scf.if {self.condition} {{\n  {then_str}\n}}"
                f"{else_str})")


class SCFFor(BlockOperation):
    """
    Counted loop: iterates from lower_bound to upper_bound by step.

    Syntax:
      [%results =] scf.for %iv = $lb to $ub step $step [iter_args(%arg = %init)] {
        <body>
      }

    The induction variable (%iv), bounds, step, and optional iter_args are
    stored. The body is parsed recursively.
    """

    _OPS = {"scf.for"}

    def __init__(self, results: List[SSAVar], iv: SSAVar,
                 lb: SSAVar, ub: SSAVar, step: SSAVar,
                 iter_args: List[Tuple[SSAVar, SSAVar]],
                 body: List[Operation]):
        self.results = results
        self.iv = iv          # induction variable
        self.lb = lb          # lower bound
        self.ub = ub          # upper bound
        self.step = step
        # iter_args: list of (block_arg, initial_value) pairs
        self.iter_args = iter_args
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return "scf.for" in line

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['SCFFor', int]:
        header = lines[cursor]
        # [%res =] scf.for %iv = %lb to %ub step %step [iter_args(%a = %v)] {
        pattern = re.compile(
            r"\s*(?:(?P<res>[^=]+?)\s*=\s*)?scf\.for\s+(?P<iv>\S+)"
            r"\s*=\s*(?P<lb>\S+)\s+to\s+(?P<ub>\S+)\s+step\s+(?P<step>\S+)"
            r"(?:\s+iter_args\s*\(\s*(?P<iargs>[^)]*)\s*\))?"
            r"\s*\{"
        )
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse SCFFor header: {header}")

        results = (
            [SSAVar.parse(r.strip()) for r in m["res"].split(",") if r.strip()]
            if m["res"] else []
        )
        iter_args: List[Tuple[SSAVar, SSAVar]] = []
        if m["iargs"]:
            for pair in m["iargs"].split(","):
                pair = pair.strip()
                if pair:
                    arg, init = pair.split("=", 1)
                    iter_args.append((SSAVar.parse(arg.strip()),
                                      SSAVar.parse(init.strip())))

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return (
            SCFFor(results, SSAVar.parse(m["iv"]),
                   SSAVar.parse(m["lb"]), SSAVar.parse(m["ub"]),
                   SSAVar.parse(m["step"]), iter_args, body),
            end + 1,
        )

    def update_variables(self, rename: Dict[str, str]) -> None:
        for r in self.results:
            if r.name in rename:
                r.name = rename[r.name]
        if self.iv.name in rename:
            self.iv.name = rename[self.iv.name]
        for var in (self.lb, self.ub, self.step):
            if var.name in rename:
                var.name = rename[var.name]
        for block_arg, init_val in self.iter_args:
            if block_arg.name in rename:
                block_arg.name = rename[block_arg.name]
            if init_val.name in rename:
                init_val.name = rename[init_val.name]
        for op in self.body:
            op.update_variables(rename)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        res_str = (', '.join(repr(r) for r in self.results) + ' = ') if self.results else ''
        iargs_str = (
            ' iter_args(' +
            ', '.join(f"{a} = {v}" for a, v in self.iter_args) + ')'
            if self.iter_args else ''
        )
        body_str = '\n  '.join(repr(op) for op in self.body)
        return (f"SCFFor({res_str}scf.for {self.iv} = {self.lb} to "
                f"{self.ub} step {self.step}{iargs_str} {{\n  {body_str}\n}})")


class SCFWhile(BlockOperation):
    """
    Pre-condition loop with separate 'before' (condition) and 'after' (body) regions.

    Syntax:
      [%results =] scf.while (%arg = %init [: type]) : (in_types) -> (out_types) {
        <before region — must end with scf.condition>
      } do {
        <after region — must end with scf.yield>
      }

    Both regions are parsed recursively and stored as lists of Operations.
    """

    _OPS = {"scf.while"}

    def __init__(self, results: List[SSAVar],
                 init_args: List[Tuple[SSAVar, SSAVar]],
                 func_type: List[List[Type]],
                 before_body: List[Operation],
                 after_args: List[Tuple[SSAVar, Type]],
                 after_body: List[Operation]):
        self.results = results
        # init_args: list of (block_arg, initial_value) pairs
        self.init_args: List[Tuple[SSAVar, SSAVar]] = init_args
        self.func_type = func_type
        self.before_body = before_body
        # after_args: SSA names introduced at the start of the after region
        self.after_args = after_args
        self.after_body = after_body

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return "scf.while" in line

    @staticmethod
    def _parse_block_args(line: str) -> List[Tuple[SSAVar, Type]]:
        """Parse a block argument declaration line like `^bb0(%arg0: !type, %arg1: !type):`."""
        m = re.match(r'\s*\^bb\d+\(\s*(?P<args>[^)]*)\s*\)\s*:', line)
        if not m:
            return []
        args_str = m.group('args').strip()
        if not args_str:
            return []
        result = []
        for arg_pair in re.split(r',\s*(?=%)', args_str):
            arg_pair = arg_pair.strip()
            colon_idx = arg_pair.index(':')
            var_str = arg_pair[:colon_idx].strip()
            type_str = arg_pair[colon_idx + 1:].strip()
            result.append((SSAVar.parse(var_str), Type.parse(type_str)))
        return result

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['SCFWhile', int]:
        header = lines[cursor]
        # [%res =] scf.while (%arg = %init) : (t0) -> (t1) {
        pattern = re.compile(
            r"\s*(?:(?P<res>[^=]+?)\s*=\s*)?scf\.while"
            r"\s*\(\s*(?P<iargs>[^)]*)\s*\)"
            r"(?:\s*:\s*(?P<ftype>[^{]+?))?\s*\{"
        )
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse SCFWhile header: {header}")

        results = (
            [SSAVar.parse(r.strip()) for r in m["res"].split(",") if r.strip()]
            if m["res"] else []
        )

        types = [[Type.parse(type) for type in region.strip()[1:-1].split(', ')]
                 for region in m["ftype"].split("->")]

        init_args: List[Tuple[SSAVar, SSAVar]] = []
        if m["iargs"]:
            for pair in m["iargs"].split(","):
                pair = pair.strip()
                if pair:
                    # Handle optional type annotation: %arg: !type = %init
                    pair_no_type = re.sub(r":\s*\S+", "", pair)
                    if "=" in pair_no_type:
                        arg, init = pair_no_type.split("=", 1)
                        init_args.append((SSAVar.parse(arg.strip()),
                                          SSAVar.parse(init.strip())))

        # Find end of 'before' region using char-by-char depth so that '} do {'
        # is correctly treated as closing the before block (the '}' fires first).
        depth = sum(1 if c == '{' else (-1 if c == '}' else 0) for c in header)
        before_end = cursor
        while depth > 0 and before_end + 1 < len(lines):
            before_end += 1
            for ch in lines[before_end]:
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                if depth == 0:
                    break

        # Skip optional ^bb0(...): block arg declaration — redundant with init_args
        before_body_start = cursor + 1
        if (before_body_start < before_end and
                lines[before_body_start].strip().startswith('^bb')):
            before_body_start += 1

        before_body = parse_fn(before_body_start, before_end)

        # Find 'do {' — may be on the same line as the closing '}' (i.e. '} do {').
        after_start = before_end
        while after_start < len(lines) and 'do' not in lines[after_start]:
            after_start += 1

        # The '{' in 'do {' opens exactly one block; don't recompute from the line
        # since '} do {' has net-zero braces.
        depth = 1
        after_end = after_start
        while depth > 0 and after_end + 1 < len(lines):
            after_end += 1
            depth += lines[after_end].count('{') - lines[after_end].count('}')

        # Capture optional ^bb0(...): block arg declaration at start of after region
        after_body_start = after_start + 1
        after_args: List[Tuple[SSAVar, Type]] = []
        if (after_body_start < after_end and
                lines[after_body_start].strip().startswith('^bb')):
            after_args = cls._parse_block_args(lines[after_body_start])
            after_body_start += 1

        after_body = parse_fn(after_body_start, after_end)

        # Rename results in each region with _bef/_aft suffixes to eliminate
        # collisions between the two regions.  after_args names are the declared
        # entry-point variables of the after region — exclude them so they keep
        # their original names (they are passed in from scf.condition, not
        # computed inside the body).
        after_arg_names: Set[str] = {v.name for v, _ in after_args}

        before_rename: Dict[str, str] = {
            name: name + "_bef"
            for name in _collect_result_names(before_body)
        }
        for op in before_body:
            op.update_variables(before_rename)

        after_rename: Dict[str, str] = {
            name: name + "_aft"
            for name in _collect_result_names(after_body) - after_arg_names
        }
        for op in after_body:
            op.update_variables(after_rename)

        return (
            SCFWhile(results, init_args, types,
                     before_body, after_args, after_body),
            after_end + 1,
        )

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        # We first initialize the variables outside the loop
        first_region_args = self.init_args
        in_types = self.func_type[0]

        # We store the initial values associated to the arguments in the
        # before region (as they initialize the while)
        initial_values = dict()

        for type_, (lhs, rhs) in zip(in_types, first_region_args):
            yield translate_assignment_core(lhs.to_core(), rhs.to_core(),
                                            "array" not in type_.name)

            constant = ctx.var2const.get(rhs.name)
            if constant is not None:
                initial_values[lhs.name] = constant

        # Then, we determine the number of steps in the while loop and
        # assign it to repeat
        steps = self._extract_step(initial_values)
        yield f"repeat {steps} {{"

        # The order of the regions to synthesize is reversed, as the before body
        # checks the condition at the end of the loop. Ignore the final yield
        for statement in self.after_body[:-1]:
            yield from statement.to_core(ctx)

        # Then assign the yielded values to the arguments
        yield_op = self.after_body[-1]
        for yield_val, (before_in_arg, type_) in zip(yield_op.operands, self.init_args):
            if yield_val.name != before_in_arg.name:
                yield translate_assignment_core_with_ctx(before_in_arg, yield_val, type_, ctx)

        # The before body comes afterwards
        for statement in self.before_body[:-1]:
            yield from statement.to_core(ctx)

        # Finally, assigned the returned values to the variables outside the while
        scf_condition = self.before_body[-1]

        # We need to assign the current results of the while operation
        ctx.scf_result = self.results
        yield from scf_condition.to_core(ctx)
        ctx.scf_result = []

        yield f"}}"

    def _extract_step(self, initial_values: Dict[str, int]) -> int:
        """
        Extracts how many iterations are performed in the loop
        """
        # We assume the following structure:
        # * Second Region / First region for the first iteration, as the first region
        #   contains the condition to evaluate. We traverse in reverse this structure to
        #   detect which variable in the condition is evaluated, which other variable is constant
        #   and how many steps are thus performed.

        # First, extract the condition variable (last instruction in the before body)
        scf_condition = self.before_body[-1]
        assert isinstance(scf_condition, SCFCondition), "Last operation of the before body must be a SCFCondition"

        # To detect the step, we need to identify three parts
        # * The condition variable
        # * The arguments of the condition variable
        # * How the arguments vary: whether they are constant, or are modified

        # First, the condition variable
        condition_var = scf_condition.condition

        # Assume the traversal from the before region in reverse order,
        # and then from the after region in reverse
        # The yield argument gives how the link the variables in both regions
        # We store the relevant expressions to compute the while expressions
        while_variables = {condition_var.name}
        var2expression = {}
        self._process_while_variables(self.before_body[:-1], while_variables, var2expression)

        # The input variables of the before region
        # correspond to the yielded variables of the after region
        yield_op = self.after_body[-1]
        assert isinstance(yield_op, SCFYield), "Last instruction in the after body must be a yield"
        for yiel_val, (before_in_arg, _) in zip(yield_op.operands, self.init_args):
            if before_in_arg.name in while_variables:
                # Add the yielded value that is linked to the variables to analyze
                while_variables.add(yiel_val.name)

                # This is a plain assignment
                var2expression[before_in_arg.name] = yiel_val.name

                while_variables.remove(before_in_arg.name)

        # We traverse the after region, ignoring the yield
        self._process_while_variables(self.after_body[:-1], while_variables, var2expression)

        # Propagate the names inside the after region with the init args of that same region
        # They usually share the same name, but i would not assume it is always the case
        assert len(scf_condition.args) == len(self.after_args), "Condition args and after region args must match"
        for cond_arg, (arg_var, _) in zip(scf_condition.args, self.after_args):
            if cond_arg.name != arg_var.name and arg_var.name in while_variables:
                while_variables.add(cond_arg.name)
                # This is a plain assignment
                var2expression[arg_var.name] = cond_arg.name
                while_variables.remove(arg_var.name)

        # Finally, using the information from var2expression, we can process the repeat information
        return infer_n_repetitions_from_expressions(while_variables, var2expression,
                                                    condition_var.name, initial_values)

    def _process_while_variables(self, operations: List[Operation], while_variables: Set[str],
                                 var2expression: Dict[str, Union[str, Operation]]):
        """
        Process the while variables (i.e. variables that affect the while condition)
        in a given set of operations.
        """
        # The operations are traversed in reverse order to perform the operation in one pass
        for operation in operations[::-1]:
            ssa_var_introduced = operation.result
            if ssa_var_introduced is not None and ssa_var_introduced.name in while_variables:
                var2expression[ssa_var_introduced.name] = operation
                while_variables.update(op.name for op in operation.operands)

                # Removes the expressions after processing them
                # (there might be collisions between the bef and aft regions)
                while_variables.remove(ssa_var_introduced.name)

    def _translate_second_region(self, region_ops: List[Operation], ctx: TranslationContext) -> Generator[str, None, None]:
        for statement in region_ops[:-1]:
            # Process all the operands as usual, except for the scf.yield
            yield from statement.to_core(ctx)

        # For the yield operation, we must retrieve the results variables
        ctx.scf_result = self.results
        yield from region_ops[-1].to_core(ctx)
        ctx.scf_result = []

    def update_variables(self, rename: Dict[str, str]) -> None:
        for r in self.results:
            if r.name in rename:
                r.name = rename[r.name]
        for _block_arg, init_val in self.init_args:
            if init_val.name in rename:
                init_val.name = rename[init_val.name]
        for op in self.before_body:
            op.update_variables(rename)
        for op in self.after_body:
            op.update_variables(rename)

    def __repr__(self):
        res_str = (', '.join(repr(r) for r in self.results) + ' = ') if self.results else ''
        iargs_str = ', '.join(f"{a} = {v}" for a, v in self.init_args)
        before_str = '\n  '.join(repr(op) for op in self.before_body)
        after_bb_str = ('^bb0(' + ', '.join(f"{v}: {t}" for v, t in self.after_args) + '):\n  '
                        if self.after_args else '')
        after_str = '\n  '.join(repr(op) for op in self.after_body)
        return (f"SCFWhile({res_str}scf.while ({iargs_str}) {{\n  {before_str}\n}}"
                f" do {{\n  {after_bb_str}{after_str}\n}})")


def _collect_result_names(ops: List[Operation]) -> Set[str]:
    """Recursively collect all SSA result names introduced within a list of operations."""
    names: Set[str] = set()
    for op in ops:
        if op.result is not None:
            names.add(op.result.name)
        if isinstance(op, SCFIf):
            names.update(r.name for r in op.results)
            names.update(_collect_result_names(op.then_body))
            if op.else_body:
                names.update(_collect_result_names(op.else_body))
        elif isinstance(op, SCFFor):
            names.update(r.name for r in op.results)
            names.add(op.iv.name)
            names.update(_collect_result_names(op.body))
        elif isinstance(op, SCFWhile):
            names.update(r.name for r in op.results)
            names.update(_collect_result_names(op.before_body))
            names.update(_collect_result_names(op.after_body))
        elif hasattr(op, 'body'):
            names.update(_collect_result_names(op.body))
    return names


class SCFDialect(Dialect):
    """Registry for all scf dialect operations."""

    def __init__(self):
        super().__init__("scf")
        self.register(SCFYield)
        self.register(SCFCondition)
        # Block ops dispatched separately by LLZKParser
        self.register(SCFIf)
        self.register(SCFFor)
        self.register(SCFWhile)
