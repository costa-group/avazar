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

// identifiers (sequence of _,a-z,A-Z,0-9,%,@ or # that does not start with #
id  := [_,a-z,A-Z,%,@] [_,a-z,A-Z,0-9,%,@,#]* 

// zero or more id separated by comma
ids := (id ("," id)*)?

// simple expression
sexp := id | Z

// zero or more simple expressions separated by comma
sexps := (sexp ("," sexp)*)?

// finite field operations
felt_bin_op := "felt.add" | "felt.mul" | "felt.div"
felt_unary_op := "felt.neg"
felt_no_op := sexp

// bitwise operations
bit_bin_op := "bit.shl" | "bit.shr" | "bit.and" | "bit.or" | "bit.xor"
bit_unary_op := bit.not
bit_no_op :=

// boolean operations
bool_bin_op := "bool.eq" | "bool.neq" | "bool.lt" | "bool.gt" | "bool.le" | "bool.ge" | "bool.and" | "bool.or"
bool_unary_op := "bool.not"
bool_no_op := "True" | "False"

// binary, unary and no-operand operations
bin_op := felt_bin_op | bit_bin_op | bool_bin_op
unary_op := felt_unary_op | bit_unary_op | bool_unary_op
no_op := felt_no_op | bool_no_op

// expressions
exp := bin_op sexp sexp | unary_op sexp | no_op

// assignment
assignment := id "=" exp

// if statement
cond := sexp "==" sexp | sexp "!=" sexp
if  := "if" "(" cond ")" "{" cmd* "}" [else "{" cmd* "}"]

// bounded loops
for := "repeat" sexpr "{" cmd* "}"

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
type := ff | arr<N>

// parameter
param := id ":" type

// zero or more parameters separated by comma
params := (param ("," param)*)?

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

### Structure

A program consists of a set of functions. One function is designated
as `%main`, serving as the entry point for generating the SMT formula.

#### Functions

A function definition follows this syntax:

```text
def id(id1:t, ...,idn:t) -> id1:t, ..., idk:t {
  body
}

```

* **Parameters:** Formal and return parameters
  follow the format `%name:type`.
* **Uniqueness:** All parameter names are distinct. All return names
  are distinct.
* **Body:** `body` is a sequence of commands.

#### Expressions

In what follow we explain the supported expressions by category.

##### Arithmetic

Semantics correspond to standard operations in the finite field .

1. `sexp` (Identity)
2. `felt.neg sexp` (Negation)
3. `felt.add sexp1 sexp2` (Addition)
4. `felt.add sexp1 sexp2` (Subtraction)
5. `felt.mul sexp1 sexp2` (Multiplication)
6. `felt.div sexp1 sexp2` (Multiplication by modular inverse)

##### Bitwise

Semantics: The operands `sexpi` are converted to `k`-bit vectors
(standard unsigned integer representation), the operation is applied,
and the result is converted back to a finite field element (modulo
`P`).

1. `bit.shl sexp1 sexp2` (Left shift)
2. `bit.shr sexp1 sexp2` (Right shift)
3. `bit.and sexp1 sexp2` (Bitwise AND)
4. `bit.or sexp1 sexp2` (Bitwise OR)
5. `bit.xor sexp1 sexp2` (Bitwise XOR)
6. `bit.not sexp1` (Bitwise NOT)

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
3. `bool.eq sexp1 sexp2`: Equality. `(sexp1=sexp2 -> result=1) and (~(sexp1=sexp2) -> result=0)`.
4. `bool.neq sexp1 sexp2`: Inequality. `(sexp1=sexp2 -> result=0) and (~(sexp1=sexp2) -> result=1)`.
5. `bool.gt sexp1 sexp2`: Signed greater than. `sexp1>sexp2 -> result=1) and (~(sexp1>sexp2) -> result=0)`.
6. `bool.lt sexp1 sexp2`: Signed less than. `(sexp1<sexp2 -> result=1) and (~(sexp1<sexp2) -> result=0)`.
7. `bool.ge sexp1 sexp2`: Signed greater or equal. `(sexp1>=sexp2 -> result=1) and (~(sexp1>=sexp2) -> result=0)`.
8. `bool.le sexp1 sexp2`: Signed less or equal. `(sexp1<=sexp2 -> result=1) and (~(sexp1<=sexp2) -> result=0)`.
9. `bool.not sexp`: Logical NOT. `(sexp=0 -> result=1) and (~(sexp=0) -> result=0)`.
10. `bool.or sexp1 sexp2`: Logical OR. `((sexp1=0 and sexp2=0) -> result=0) and ((~(sexp1=0) or ~(sexp2=0)) -> result=1)`.
11. `bool.and sexp1 sexp2`: Logical AND. `(~(sexp1=0) and ~(sexp2=0)) -> result=1) and (((sexp1=0) or (sexp2=0)) -> result=0)`.

#### Commands

Next we describe the possible commands supported in the language.

##### Assignment

```text
id = exp
```

Assigns the result of `exp` to `id`.

##### Arrays

1. `array.new sexp id`: Allocates an array of `sexp` elements (type
   `ff`), and stores it in variable `id`. `sexp` must be a constant simple expression.
2. `array.read id1[sexp] id2`: Reads the array `id1` at index `sexp` into variable `id2`.
3. `array.write sexp1 id[sexp2]`: Updates array `id` at index `exp2` with value of`sexp1`.
4. `array.copy id1 id2`: Copies array `id1` into `id2`. The previous value
   of `id2` is overwritten. `id1` must be an array.

> [!IMPORTANT]
>
> In symbolic execution requires that size of arrays is known (at symbolic execution time),
> otherwise it would fail.

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
> Types of all live variables at exit of both branches must coincide.

##### Bounded Loops

```text
repeat sexp  { body }
```

Repeats `body` for `sexp` times. There is no loop counter, should be taken care of independently (i.e., initializing a variable before the loop and increment it inside `body`).

> [!IMPORTANT]
>
> 'sexp' must be computed at symbolic execution time, otherwise we cannot unfold the loop.

**Semantics:**

1. Evaluate `sexp` to a value `N`.
2. Repeat `body` for `N` times.

##### Function Calls

```text
call id(sexp1, ..., sexpn) to id1,...,idk
```

Executes function with name `id`. The return values (which may include arrays) are
assigned to `id1, ..., idk`. The `to` keyword is optional if the functions
does not return values.

### SSA Support

The language does not natively support Static Single Assignment
(SSA). It is structured code. However, the translator can simulate SSA
by inserting phi-functions at control flow merge points (e.g., after
`if/else` blocks).
