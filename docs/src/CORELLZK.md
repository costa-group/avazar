# Core LLZK Specification

The purpose of Core LLZK is to provide a language simple enough to
allow a clean formalization of transforming witness generators to SMT
formulas, yet rich enough to model LLZK programs.

## Scope and Restrictions

To ensure feasible formalization, LLZK programs must adhere to the
following restrictions:

* **Static Array Sizes:** The size of an array cannot depend on input
  values.

* **Type Consistency:** A variable accessed at a specific program
  point must always have the same type, regardless of the control flow
  path taken to reach that point. This ensures, for example, that if
  we access `y[i]`, the dimensions of `y` is known statically.

* **No Recursion:** Recursion is forbidden. This is enforced by
  requiring a total order on function definitions (a function may only
  call functions defined prior to itself).

* **Unrolled Loops:** The language does not support dynamic loops. It
  supports [bounded loops](#bounded-loops), which are intended to be
  unrolled during processing.

## Informal Definition

We assume a prime number `P` and an architecture width of `k` bits,
such that `P < 2^k`.  For any number `x`, its **FF-value** (Finite
Field value) is an integer in the range `[0, P-1]`, calculated as `x
mod P`. We first give the grammar, and then explain each part
separately.

```text
// numbers
N := a natural number
Z := an integer (will be interpreted as a finite field value)

// identifiers
id  := %[_,a-z,A-Z,0-9]* 
cid := $[_,a-z,A-Z,0-9]*

// one or more id separated by comma
ids := id [("," id)*]

// simple expression
sexp := id | cid | Z

// zero or more simple expressions separated by comma
sexps := (sexp [("," sexp)*])?

// finite field operations
felt_bop := "felt.add" | "felt.mul" | "felt.div"
felt_uop := "felt.neg"
felt_nop := sexp

// bitwise operations
bit_bop := "bit.shl" | "bit.shr" | "bit.and" | "bit.or" | "bit.xor"
bit_uop := bit.not

// boolean operations
bool_bop := "bool.eq" | "bool.neq" | "bool.lt" | "bool.gt" | "bool.le" | "bool.ge" | "bool.and" | "bool.or"
bool_uop := "bool.not"
bool_nop := "True" | "False"

// binary, unary and 'n operand' operations
bop := felt_bop | bit_bop | bool_bop
uop := felt_uop | bit_uop | bool_uop
zop := felt_nop | bool_nop

// expressions
exp := bop sexp sexp | uop sexp | zop

//assignment
assignment := id "=" exp

// if statement
cond := sexp "==" sexp | sexp "!=" sexp
if  := "if" "(" cond ")" "{" cmd* "}" [else "{" cmd* "}"]

// bounded for loop
for := "for" "(" cid "," exp "," exp "," exp  ")" "{" cmd* "}"

// const variable definition
wconst := "with_const" cid "=" exp "{" cmd* "}"

// array operations
narray := "array.new" sexp id
rarray := "array.read" id "[" sexp "]" id
warray := "array.write" sexp id "[" sexp "]"
carray := "array.copy" id id

// function call
fcall  := "call" id "(" sexps ")" ["to" ids]

// command
cmd := assignment | if | for | wconst | narray | rarray | warray | carray | fcall

// types
type := ff | aar<N>

// parameter
param := id ":" type

// zero or more parameters separated by comma
params := (param ["," param]*)?

// function definition
function := "func" id "(" params ")" [":" params] "{" cmd* "}"

// program
prog := func*
```

### Types

There are two primary types:

1. `ff`: A scalar variable over the finite field.
2. `arr<N>`: An array of `N` finite field elements (`N` is a constant).

Types must be declared for function input and output parameters. Local
variable types are inferred dynamically upon assignment and checked
upon usage.

> [!NOTE]
>
> Machine integers and booleans are simulated using the `ff` type.

**Conventions:**

* `%x`, `%y`, `%z`: Variables of type `ff`.
* `v`, `v1`, `v2`: Concrete values.
* `#i`, `#j`: **Constant variables** (e.g., loop indices).

A **Simple Expression** (`s`, `s1`, `s2`) is an atomic unit that can
be a variable, a value, or a constant variable. A **Constant Simple
Expression** is one that is not a variable (it can be only a value or
a constant variable).

### Structure

A program consists of a set of functions. One function is designated
as `%main`, serving as the entry point for generating the SMT formula.

#### Functions

A function definition follows this syntax:

```text
def %fname(%X1:t, ..., %Xn:t) -> %Y1:t, ..., %Yk:t {
  body
}

```

* **Parameters:** Formal and return parameters
  follow the format `%name:type`.
* **Uniqueness:** All parameter names are distinct. All return names
  are distinct.
* **Body:** `body` is a sequence of instructions (commands).

#### Expressions

In what follow we explain the supported expressions by category.

##### Arithmetic

Semantics correspond to standard operations in the finite field .

1. `s1` (Identity)
2. `felt.neg s1` (Negation)
3. `felt.add s1 s2` (Addition)
4. `felt.add s1 s2` (Subtraction)
5. `felt.mul s1 s2` (Multiplication)
6. `felt.div s1 s2` (Multiplication by modular inverse)

##### Bitwise

Semantics: The operands `si` are converted to `k`-bit vectors
(standard unsigned integer representation), the operation is applied,
and the result is converted back to a finite field element (modulo
`P`).

1. `bit.shl s1 s2` (Left shift)
2. `bit.shr s1 s2` (Right shift)
3. `bit.and s1 s2` (Bitwise AND)
4. `bit.or s1 s2` (Bitwise OR)
5. `bit.xor s1 s2` (Bitwise XOR)
6. `bit.not s1` (Bitwise NOT)

> [!NOTE]
>
> How conversion from bit-vectors to finite field should be done?
> Calculate the corresponding non-negative integer `x` and then
> compute `x mod P`?

##### Boolean

Comparisons interpret field elements as signed integers. The
order is defined as `mid+1, ..., P-1, 0, ..., mid`, where
`mid = (P-1)/2`.

> [!NOTE]
>
> The semantics on the right is not an encoding to SMT, it is just to
> write it a bit formally.

1. `True`: evaluates to `1`.
2. `False`: evaluates to `0`.
3. `bool.eq s1 s2`: Equality. `(s1=s2 -> result=1) and (~(s1=s2) -> result=0)`.
4. `bool.neq s1 s2`: Inequality. `(s1=s2 -> result=0) and (~(s1=s2) -> result=1)`.
5. `bool.gt s1 s2`: Signed greater than. `s1>s2 -> result=1) and (~(s1>s2) -> result=0)`.
6. `bool.lt s1 s2`: Signed less than. `(s1<s2 -> result=1) and (~(s1<s2) -> result=0)`.
7. `bool.ge s1 s2`: Signed greater or equal. `(s1>=s2 -> result=1) and (~(s1>=s2) -> result=0)`.
8. `bool.le s1 s2`: Signed less or equal. `(s1<=s2 -> result=1) and (~(s1<=s2) -> result=0)`.
9. `bool.not s`: Logical NOT. `(s=0 -> result=1) and (~(s=0) -> result=0)`.
10. `bool.or s1 s2`: Logical OR. `((s1=0 and s2=0) -> result=0) and ((~(s1=0) or ~(s2=0)) -> result=1)`.
11. `bool.and s1 s2`: Logical AND. `(~(s1=0) and ~(s2=0)) -> result=1) and (((s1=0) or (s2=0)) -> result=0)`.

#### Commands

Next we describe the possible commands supported in the language.

Recall that a simple expression `s` is constant, if it does not
involve variables (it can involve constant variables). We say that an
expression `exp` is a **constant expression** if all its simple
expressions are constant.

##### Assignment

```text
id = exp
```

Assigns the result of `exp` to `x`. `exp` cannot be a compound
expression (nested operations are not supported directly; intermediate
variables must be used).

##### Arrays

1. `array.new sexp id`: Allocates an array of `sexp` elements (type
   `ff`), and stores it in variable `id`. `sexp` must be a constant simple expression.
2. `array.read id1[sexp] id2`: Reads the array `id1` at index `sexp` into variable `id2`.
3. `array.write sexp1 id[sexp2]`: Updates array `id` at index `exp2` with value of`sexp1`.
4. `array.copy id1 id2`: Copies array `id1` into `id2`. The previous value
   of `id2` is overwritten. `id1` must be an array.

> [!IMPORTANT]
>
> Efficient translation of array access/update `id[sexp]` to SMT formulas
> is only possible if the index `sexp` is a **Constant Simple
> Expression**.

##### Conditionals

1. `if sexp1==sexp2 { body } else { body }`
2. `if sexp1!=exps2 { body } else { body }`

The `else` part is optional.

> [!NOTE]
>
> Only equality checks are supported in guards. Other comparisons
> (e.g., `>`) must be computed beforehand or encoded, as they do not
> simplify the SMT translation.

##### Bounded Loops

```text
for(cid, START, N, STEP) { body }
```

`START`, `N` (iteration count), and `STEP` must be **Constant
Expressions**.

**Semantics:**

1. Evaluate `START`, `N`, and `STEP` to concrete values.
2. Initialize loop counter `cid = START`.
3. Execute `body` `N` times. After each iteration, update `cid := cid +
   STEP`.

Inside the loop body, the loop index is a **constant variable**.

> [!NOTE]
>
> This construct relies on loop unrolling. In every unrolled
> iteration, `cid` can be used to refer to the concrete index for that
> step. Nested loops must use distinct index names.

>[!NOTE]
>
>Should we allow `-(STEP)`? What to do if `i` goes negative in such
>case? Just treat it as a finite field negative (i.e., `-1` goes back
>to `P-1`)?

##### Constant Definition

```text
with_const cid = exp { body }
```

Defines a scope where `cid` is a constant variable with the value of
`exp` (which must be a constant expression). Inside `body`, this value
is accessed as `cid`. Re-declaration of `cid` within the body is
forbidden. This also applies to loop indices sine they are constant
variables.

>[!NOTE]
>
>This construct is useful for simulating `%x[$i+1]` using
>`with_const $j=$i+1 { ... x[$j] ... }`.

##### Function Calls

```text
call id(sexp1, ..., sexpn) to id1,...,idk
```

Executes function with name `id`. The return values (which may include arrays) are
assigned to `id1, ..., idk`. The `to` keyword is optional of the functions
does not return values.

### SSA Support

The language does not natively support Static Single Assignment
(SSA). It is structured code. However, the translator can simulate SSA
by inserting phi-functions at control flow merge points (e.g., after
`if/else` blocks).
