# llzk2core_py

Python parser for LLZK IR — an MLIR-based intermediate representation for
zero-knowledge circuits composed of multiple dialects.

Spec: https://project-llzk.github.io/llzk-lib/main/dialects.html

## Architecture

```
src/llzk_dialects/
  core.py        — base classes: SSAVar, GlobalVariable, Type, Operation,
                   BlockOperation, TranslationContext
  definitions.py — Dialect base class (plain class, NOT Enum)
  parser.py      — LLZKParser: dialect-driven dispatcher for LLZK IR text
  felt.py        — finite field element operations
  array.py       — N-dimensional array operations
  bool.py        — boolean logic and comparison
  cast.py        — type conversions (felt ↔ index ↔ i1)
  constrain.py   — constraint emission (eq, in)
  function.py    — function definition, calls, returns
  global_.py     — global value definition and access  (named global_.py to
                   avoid Python's builtin 'global' keyword)
  include.py     — file inclusion
  llzk.py        — core LLZK constructs (nondet)
  pod.py         — plain-old-data struct operations
  poly.py        — polymorphic / templated constructs
  string.py      — string literals
  struct.py      — circuit component (struct) definitions and member access
  scf.py         — structured control flow (standard MLIR: if/for/while)
src/execution/
  main_execution.py — entry point; builds LLZKParser with all 14 dialects
tests/
  test_{dialect}_parse.py — one file per dialect
  test_parser.py          — integration tests for LLZKParser
```

## Naming conventions

- Class names: `{DialectCap}{OpCamelCase}`, e.g. `FeltBinary`, `BoolCmp`, `StructDef`
- Dialect registry class at the bottom of each module: `{DialectCap}Dialect`
- `_OPS` class variable: a `set` of the exact op-name strings this class handles

## Two kinds of operations

### Flat operations (`Operation`)
Single-line; used for all arithmetic, cast, constraint, and access ops.

Required methods:
```python
@staticmethod
def match(line: str) -> bool: ...          # True if this line belongs to this op

@classmethod
def parse(cls, line: str) -> 'OpClass': ...  # parse from a single text line

def to_core(self, ctx: TranslationContext) -> str: ...  # translate to core repr

def __repr__(self) -> str: ...
```

### Block operations (`BlockOperation`)
Multi-line; used for `struct.def`, `function.def`, `poly.template`, `poly.expr`,
`scf.if`, `scf.for`, `scf.while`.

`match()` inspects only the opening header line.  
`parse()` has a different signature — it consumes multiple lines:

```python
@staticmethod
def match(line: str) -> bool: ...

@classmethod
def parse(cls, lines: List[str], cursor: int,
          parse_fn: ParseFn) -> Tuple['OpClass', int]: ...
# parse_fn(start, end) -> List[Operation]  — provided by LLZKParser;
# call it to recursively parse the body between cursor+1 and the closing brace.
# Returns (parsed_op, next_cursor_after_closing_brace).

def to_core(self, ctx: TranslationContext) -> str: ...

def __repr__(self) -> str: ...
```

## Translation

Every operation has:
```python
def to_core(self, ctx: TranslationContext) -> str:
    raise NotImplementedError   # stub — implement per operation
```

`TranslationContext` (in `core.py`) holds all translation state:
- `var_map: Dict[str, str]` — maps SSA names to core variable names.

**To add more context:** add a field to `TranslationContext` — do NOT change
method signatures. Existing implementations that don't need the new field are
unaffected. This is the Option B / dataclass-context pattern.

## LLZKParser

`parser.py` is a thin dispatcher; each dialect owns its own parsing logic.

```python
parser = LLZKParser(lines)
parser.add_dialects([FeltDialect(), StructDialect(), ...])  # all 14 in main_execution
ops = parser.parse()          # returns List[Operation]; handles module { } wrapper
ops = parser.parse_body(s, e) # parse a sub-range; passed as parse_fn to block ops
```

**Dispatch flow:**
1. Scan tokens for the first one starting with a letter that contains `.` — this is
   the operation token (e.g. `felt.add`, `struct.writem`). The part before `.` is
   the dialect prefix.
2. Look up the dialect by prefix; iterate `registered_ops` calling `op_cls.match(line)`.
3. `issubclass(op_cls, BlockOperation)` → `op_cls.parse(lines, cursor, parse_body)`;
   otherwise `op_cls.parse(line)`.

**Unrecognised lines** raise `ValueError`. Structural markers (`}`, `} else {`,
`do {`, `^bb…`) are silently skipped.

**module wrapper:** if the first line starts with `module`, `parse()` extracts the
body inside the outermost `{…}` before dispatching.

## Parsing conventions

- Use `re.fullmatch` with named groups for flat ops
- SSA variables start with `%`; global/symbol references start with `@`
- Types are optional in many ops; parse as `List[Type]`, empty list if absent
- Attribute dicts `{...}` are parsed as `Dict[str, str]` for now
- `Type` wraps a raw string — full structural type parsing is a later phase
- Types that contain spaces (e.g. `!pod.type<[@x: !felt.type, ...]>`) must be
  captured with `[^{]+?` (not `\S+`) when they appear before an optional `{attrs}`
  suffix; always `.strip()` the captured group

## Testing

- One file per dialect: `tests/test_{dialect}_parse.py`; parser tests in `tests/test_parser.py`
- Test class: `Test{DialectCap}`
- Per operation, cover:
  1. Simplified form (no type annotation)
  2. Full form (with type annotation)
  3. Invalid op name → expect `AssertionError` or `ValueError`
  4. At least one corner/edge case specific to that op
- `to_core` stubs raise `NotImplementedError`; tests verify parsing only for now
- `conftest.py` at project root adds `src/` to `sys.path` so `llzk_dialects.*`
  resolves without a `src.` prefix
