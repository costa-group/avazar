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
mod P`.

### Types

There are two primary types:

1. `ff`: A scalar variable over the finite field.
2. `a<N>`: An array of `N` finite field elements (`N` is a constant).

Types must be declared for function input and output parameters. Local
variable types are inferred dynamically upon assignment and checked
upon usage.

> [!NOTE]
>
> Machine integers and booleans are simulated using the `ff` type.

**Conventions:**

* `x`, `y`, `z`: Variables of type `ff`.
* `v`, `v1`, `v2`: Concrete values.
* `#i`, `#j`: **Constant variables** (e.g., loop indices).

A **Simple Expression** (`s`, `s1`, `s2`) is an atomic unit that can
be a variable, a value, or a constant variable. A **Constant Simple
Expression** is one that does not contain variables (it contains only
values or constant variables).

### Structure

A program consists of a set of functions. One function is designated
as `main`, serving as the entry point for generating the SMT formula.

#### Functions

A function definition follows this syntax:

```text
def fname(X1:t, ..., Xn:t) -> Y1:t, ..., Yk:t {
  body
}

```

* **Parameters:** Formal parameters (`X`) and return parameters (`Y`)
  follow the format `name:type`.
* **Uniqueness:** All parameter names (`Xi`) and return names (`Yi`)
  must be distinct.
* **Body:** `body` is a sequence of instructions.

#### Expressions

In what follow we explain the supported expressions by category.

##### Arithmetic

Semantics correspond to standard operations in the finite field .

1. `s1` (Identity)
2. `-s1` (Negation)
3. `s1 + s2`
4. `s1 - s2`
5. `s1 * s2`
6. `s1 / s2` (Multiplication by modular inverse)

##### Bitwise Operations

Semantics: The operands `si` are converted to `k`-bit vectors
(standard unsigned integer representation), the operation is applied,
and the result is converted back to a finite field element (modulo
`P`).

1. `s1 << s2` (Left shift)
2. `s1 >> s2` (Right shift)
3. `s1 & s2` (Bitwise AND)
4. `s1 | s2` (Bitwise OR)
5. `s1 ^ s2` (Bitwise XOR)
6. `~s1` (Bitwise NOT)

> [!NOTE]
>
> How conversion from bit-vectors to finite field should be done?
> Calculate the corresponding non-negative integer `x` and then
> compute `x mod P`?

##### Comparisons

Semantics: Comparisons interpret field elements as signed
integers. The order is defined as `mid+1, ..., P-1, 0, ..., mid`,
where `mid = (P-1)/2`. Trueth value 

> [!NOTE]
>
> The semantics on the right is not an encoding to SMT, it is just to
> write it a bit formally.

1. `True`: evaluates to `1`.
2. `False`: evaluates to `0`.
3. `s1=s2`: Equality. (s1=s2 -> result=1) and (~(s1=s2) -> result=0).
4. `s1!=s2`: Inequality. (s1=s2 -> result=0) and (~(s1=s2) -> result=1).
5. `s1 > s2`: Signed greater than. s1>s2 -> result=1) and (~(s1>s2) -> result=0).
6. `s1 < s2`: Signed less than. (s1<s2 -> result=1) and (~(s1<s2) -> result=0).
7. `s1 >= s2`: Signed greater or equal. (s1>=s2 -> result=1) and (~(s1>=s2) -> result=0).
8. `s1 <= s2`: Signed less or equal. (s1<=s2 -> result=1) and (~(s1<=s2) -> result=0).
9. `!s`: Logical NOT. (s=0 -> result=1) and (~(s=0) -> result=0).
10. `s1 || s2`: Logical OR. ((s1=0 and s2=0) -> result=0) and ((~(s1=0) or ~(s2=0)) -> result=1).
11. `s1 && s2`: Logical AND. (~(s1=0) and ~(s2=0)) -> result=1) and (((s1=0) or (s2=0)) -> result=0).


#### Instructions

Next we describe the possible instructions supported in the language.

Recall that a simple expression `s` is constant, if it does not
involve variables (it can involve constant variables). We say that an
expression `exp` is a **constant expression** if all its simple
expressions are constant.

##### Assignment

```text
x := exp
```

Assigns the result of `exp` to `x`. `exp` cannot be a compound
expression (nested operations are not supported directly; intermediate
variables must be used).

##### Arrays

1. `x := new_array N`: Allocates an array of `N` elements (type
   `ff`). `N` must be a constant.
2. `x := y[s]`: Reads `y` at index `s` into `x`.
3. `x[s1] := s2`: Updates `x` at index `s1` with value `s2`.
4. `x := cpy_array y`: Copies array `y` into `x`. The previous value
   of `x` is overwritten. `y` must be an array.

> [!IMPORTANT]
>
> Efficient translation of array access/update `x[s]` to SMT formulas
> is only possible if the index `s` is a **Constant Simple
> Expression**. 

##### Conditionals

1. `if s1=s2 { body } else { body }`
2. `if s1!=s2 { body } else { body }`

> [!NOTE]
>
> Only equality checks are supported in guards. Other comparisons
> (e.g., `>`) must be computed beforehand or encoded, as they do not
> simplify the SMT translation.

##### Bounded Loops

```text
for(i, START, N, STEP) { body }
```

`START`, `N` (iteration count), and `STEP` must be **Constant
Expressions**.

**Semantics:**

1. Evaluate `START`, `N`, and `STEP` to concrete values.
2. Initialize loop counter `i = START`.
3. Execute `body` `N` times. After each iteration, update `i := i +
   STEP`.

Inside the loop body, the loop index is a **constant variable**
accessed via `#i`.

> [!NOTE]
>
> This construct relies on loop unrolling. In every unrolled
> iteration, `#i` can be used to refer to the concrete index for that
> step. Nested loops must use distinct index names.

>[!note]
>
>Should we allow `-(STEP)`? What to do if `i` goes negative in such
>case? Just treat it as a finite field negative (i.e., `-1` goes back
>to `P-1`)?

##### Constant Definition

```text
with_const i = exp { body }
```

Defines a scope where `i` is a constant variable with the value of
`exp` (which must be a constant expression). Inside `body`, this value
is accessed as `#i`. Re-declaration of `i` within the body is
forbidden. This also applies to loop indices sine they are constant
variables.

##### Function Calls

```text
x1, ..., xk = fname(s1, ..., sn)
```

Executes `fname`. The return values (which may include arrays) are
assigned to `x1, ..., xk`.

### SSA Support

The language does not natively support Static Single Assignment
(SSA). It is structured code. However, the translator can simulate SSA
by inserting phi-functions at control flow merge points (e.g., after
`if/else` blocks).
