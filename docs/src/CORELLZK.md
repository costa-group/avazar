# Core LLZK

The purpose is to have a language that is simple enough to allow a
clean formalization of transforming witness generators to SMT
formulas, and rich enough to model LLZK programs.

## Restrictions on LLZK programs that can be handled

The LLZK programs that we can handled must have the following features:

* The size of an array cannot depend on the input value.

* At a given program point, a variable that is accessed will always
  have the same type, independently from how the corresponding program
  point has been reached. This is important in the case of arrays, to
  guarantee that if we are accessing y[i] then we know what the size
  of y is.

* Recursion is forbidden, which can be achieved by forcing a total
  order on the different functions, e.g., the definition order (a
  function can call those defined before, excluding itself).

* There are no loops in the language, they are supposed to have been
  unfolded. Though we can handle [bounded loops](#bounded-loops). 


## Informal definition of CORE LLZK

We assume a prime number `P` and an architecture with `k` bits, such
that `P < 2^k`. For a number `x`, its `FF-value` is a value between
`0` and `P-1` calculated as `x mod P`.

### Types

There are two types:

1. `ff`: for a variable over the finite field type.
2. `a<N>`: for an array of `N` finite field elements.

We only require declaring types for the input and output variables of
a function (maybe we do not need it for the output, will become clear
later). Local variables can be used without type and their type is
determined dynamically when assigned a value, and checked when they
are used.

>[!note>
>
> Machine integer and boolean can be simulated using the `ff` type.

In what follows we use the the following conventions:

1. We use `x`,`y`,`z`,... for a variable of a finite field type.

2. We use `v`, `v1`,`v2`,... for concrete values.

3. We use `#i`,`#j`,... for *constant variables* (such as loop
   indices, etc).

A *simple expression* is an expression that be any of the above, and
is denoted by `s`, `s1`, `s2`, etc. A **constant** simple expression
is simple expression that is not a variable (i.e, can be case 2 or
case 3).


### Programs

A program is a set of functions, and one is assumed to be the main,
i.e., the one we use as the entry point to generate the SMT formula.

### Functions

A function definition is of the form

```text
def fname(X1:t,...,Xn:t) -> Y1:t,...,Yk:t {
  body
}
```

Formal parameters and return parameters have the form `var:t`, meaning
that `var` is the name and `t` is the type. All Xi must be different,
and all Yi as well.

The `body` is a sequence of instructions.


### Expressions

We group expressions by their kind, and briefly explain the
corresponding semantics.

#### Arithmetic

The semantics of these operations is simply as the corresponding operations in the finite field.

1. `s1`.
2. `-s1`.
3. `s1 + s2`.
4. `s1 - s2`.
5. `s1 * s2`.
6. `s1 / s2`.

#### Bitwise expression

The semantics of these operations converts `si` to bit-vectors of `k`
bits, applies the corresponding bitwise operation, and converts back
to finite field.

1. `s1 << s2`: left shift.
2. `s1 >> s2`: right shift.
3. `s1 & s2`: bitwise-and.
4. `s1 | s2`: bitwise-or.
5. `s1 ^ s2`: bitwise-xor.
6. `~s1`: bitwise negation.

> [!NOTE]
>
> How conversion from bit-vectors to finite field should be done?
> Calculate the corresponding non-negative integer `x` and then
> compute `x mod P`?

#### Comparison expressions

Every operation has its semantic to the right. Here `<`, `>`, `>=` and
`<=` are interpreted according to the order `mid+1,...,P-1,0,...,mid`
where `mid=(p-1)/1`

> [!NOTE]
>
> The semantics on the right is not an encoding to SMT, it is just to
> write it a bit formally.

1. `s1=s2`: (s1=s2 -> result=1) and (~(s1=s2) -> result=0).
2. `s1!=s2`: (s1=s2 -> result=0) and (~(s1=s2) -> result=1).
3. `s1 > s2`: (s1>s2 -> result=1) and (~(s1>s2) -> result=0).
4. `s1 < s2`: (s1<s2 -> result=1) and (~(s1<s2) -> result=0).
5. `s1 >= s2`: (s1>=s2 -> result=1) and (~(s1>=s2) -> result=0).
6. `s1 <= s2`: (s1<=s2 -> result=1) and (~(s1<=s2) -> result=0).
7. `!s`: (s=0 -> result=1) and (~(s=0) -> result=0).
8. `s1 || s2`: ((s1=0 and s2=0) -> result=0) and ((~(s1=0) or ~(s2=0)) -> result=1).
9. `s1 && s2`: (~(s1=0) and ~(s2=0)) -> result=1) and (((s1=0) or (s2=0)) -> result=0).

### Instructions

Next we describe the possible instructions supported in the language.

Recall that a simple expression `s` is constant, if it does not
involve variables (it can involve constant variables). We say that an
expression `exp` is constant if all its simple expressions are
constant.

#### Assignment

An assignment is of the following form:

```text
x := exp
```

It assigns the value of `exp` to `x`. Note that `exp` is any of the
expressions described above (it cannot be compound).


#### Arrays

1. `x := new_array N`: creates an array of `N` elements of type `ff`, where `N` is a constant.
2. `x := y[s]`: extracts the value of `y[s]` into variable `x`.
3. `x[s1] := s2`: sets the value of `x[s1]` to a simple expression `s2`.
4. `x := cpy_array y`: `y` must be of array type, copies the array `y`
   into `x` (old value of `x`, if any, is destroyed).

> [!NOTE] 
>
> We should be aware that translating an array access/update `x[s]` to
> formulas can be done in a compact way only when the index `s` is
> constant simple-expression. There is no constant propagation, this
> should be done independently as a preprocessing step.

#### Conditionals

1. `if s1=s2 { body } else { body }`: s1=s2 -> then branch, ~(s1=s2) -> else branch.
2. `if s1!=s2 { body } else { body }`: ~(s1=s2) -> then branch, s1=s2 -> else branch.

> [!NOTE]
>
> Adding other kinds of comparison, like `>`, explicitly to the guard
> does not simplify anything in the translation, since they all have
> non-trivial encoding.

#### Bounded loops

A bounded loop is of the form:

```text
for(i,START,N,STEP) { body }
```

where `START`, `N`, and `STEP` are constant expressions.


It should be interpreted as follows: 

1. We first evaluate `START`, `N`, and `STEP` into their concrete
   values `START_v`, `N_v`, and `STEP_v`. The evaluation is also done
   in the symbolic execution, since they are constant expressions.
   
2. Start from `i=START_v`, and repeat `body` for `N_v` times where
   after each time add `STEP_v` to `i`.

The loop index `i` is a constant variable, and inside `body` it can be
used as `#i`.

>[!note]
>
>The implementation is based on loop unrolling, where in every
>iteration there is a **constant** that is equivalent to the loop
>index. To refer to this constant value we can use `#i`. Nested loops
>**must** use different indices. We cannot define a constant `i`
>inside `body` (see [Constant definition](#constant-definition).


>[!note]
>
>Should we allow `-(STEP)`? What to do if `i` goes negative in such
>case? Just treat it as a finite field negative (i.e., `-1` goes back
>to `P-1`)?

#### Constant definition

This is an instruction that allows defining a constant variable, and is
of the form:

```text
with_const i=exp { body }
```

where `exp` is a constant expression. Inside `body` the value of `i`
can be accessed as `#i` and is available at symbolic execution time as
well (since `exp` is a constant expressions). We cannot redefine the
constant `i` inside `body`, not have a loop with index called `i`.

>[!note] 
>
>This is useful for simulating `y:=x[#i+1]` using `with_const j=#i+1 {
>y:=[#j] }`, becuase array accesses use only simple expressions.


#### Function calls

1. `x1,...,xk = fname(s1,...,sn)`: variables `x1,...,xk` receive the
   returned values, which can be arrays as well.

### Support for SSA

There is no direct support for SSA in the language, because it is
structured, so we can always add the phi-functions at the end of the
branches of an if-statement.
