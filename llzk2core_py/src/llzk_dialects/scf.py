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

import re
from typing import List, Optional, Tuple

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect


class SCFYield(Operation):
    """
    Yield values from an scf block (if-branch, for-body, while-body, etc.).

    Syntax: scf.yield [$operands : type($operands)]
    Operands: variadic (any type)
    Traits: Terminator, ReturnLike
    """

    _OPS = {"scf.yield"}

    def __init__(self, operands: List[SSAVar], types: List[Type]):
        self.operands = operands
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

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        if not self.operands:
            return "SCFYield(scf.yield)"
        ops_str = ', '.join(repr(o) for o in self.operands)
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

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

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
        # [%r0, %r1 =] scf.if %cond [: !type] {
        pattern = re.compile(
            r"\s*(?:(?P<res>[^=]+?)\s*=\s*)?scf\.if\s+(?P<cond>\S+)"
            r"(?:\s*:\s*(?P<types>[^{]+?))?\s*\{"
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

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

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
                 func_type: Optional[str],
                 before_body: List[Operation],
                 after_body: List[Operation]):
        self.results = results
        # init_args: list of (block_arg, initial_value) pairs
        self.init_args = init_args
        self.func_type = func_type
        self.before_body = before_body
        self.after_body = after_body

    def dialect(self) -> Dialect:
        return Dialect("scf")

    @staticmethod
    def match(line: str) -> bool:
        return "scf.while" in line

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

        # Find end of 'before' region
        depth = header.count('{') - header.count('}')
        before_end = cursor
        while depth > 0 and before_end + 1 < len(lines):
            before_end += 1
            depth += lines[before_end].count('{') - lines[before_end].count('}')

        before_body = parse_fn(cursor + 1, before_end)

        # Find 'do {' and parse 'after' region
        after_start = before_end + 1
        # The 'do {' may be on its own line or on the same line as the closing '}'
        while after_start < len(lines) and "do" not in lines[after_start]:
            after_start += 1

        depth = lines[after_start].count('{') - lines[after_start].count('}')
        after_end = after_start
        while depth > 0 and after_end + 1 < len(lines):
            after_end += 1
            depth += lines[after_end].count('{') - lines[after_end].count('}')

        after_body = parse_fn(after_start + 1, after_end)

        return (
            SCFWhile(results, init_args, m["ftype"] and m["ftype"].strip(),
                     before_body, after_body),
            after_end + 1,
        )

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        res_str = (', '.join(repr(r) for r in self.results) + ' = ') if self.results else ''
        iargs_str = ', '.join(f"{a} = {v}" for a, v in self.init_args)
        before_str = '\n  '.join(repr(op) for op in self.before_body)
        after_str = '\n  '.join(repr(op) for op in self.after_body)
        return (f"SCFWhile({res_str}scf.while ({iargs_str}) {{\n  {before_str}\n}}"
                f" do {{\n  {after_str}\n}})")


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
