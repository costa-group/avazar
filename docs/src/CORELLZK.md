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


## Definition of CORE LLZK

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

Note that machine integer and boolean can be simulated using the `ff` type.

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

### Instructions

We group instructions by their kind, and briefly explain the corresponding semantics. We use the following conventions for names

1. we use `x`,`y`,`z`,... for a variable
2. we use `v1`,`v2`,... for concrete values
3. we use `#i`,`#j`,... for refering to the value of a loop index
3. we use `s1`,`s2`,... for a simple expression that is a **variable over finite field**, a value, or a loop index

> [!NOTE]
>
> Simple expressions do not include array accesses.  

#### Arithmetic

The semantics of these operations is simply as the corresponding operations in the finite field.

1. `x := s1`.
2. `x := -s1`.
3. `x := s1 + s2`.
4. `x := s1 - s2`.
5. `x := s1 * s2`.
6. `x := s1 / s2`.

#### Bitwise operations

The semantics of these operations converts `si` to bit-vectors of `k` bits, applies the corresponding bitwise operation, and converts back to finite field.

1. `x := s1 << s2`: left shift.
2. `x := s1 >> s2`: right shift.
3. `x := s1 & s2`: bitwise-and.
4. `x := s1 | s2`: bitwise-or.
5. `x := s1 ^ s2`: bitwise-xor.
6. `x := ~s1`: bitwise negation.

#### Comparison operations

Every operation has its semantic to the right. Here `<`, `>`, `>=` and `<=` are interpreted according to the order `mid+1,...,P-1,0,...,mid` where `mid=(p-1)/1`

> [!NOTE]
>
> The semantics on the right is not an encoding to SMT, it is just to
> write it a bit formally.

1. `x := s1=s2`: (s1=s2 -> x=1) and (~(s1=s2) -> x=0).
2. `x := s1!=s2`: (s1=s2 -> x=0) and (~(s1=s2) -> x=1).
3. `x := s1 > s2`: (s1>s2 -> x=1) and (~(s1>s2) -> x=0).
4. `x := s1 < s2`: (s1<s2 -> x=1) and (~(s1<s2) -> x=0).
5. `x := s1 >= s2`: (s1>=s2 -> x=1) and (~(s1>=s2) -> x=0).
6. `x := s1 <= s2`: (s1<=s2 -> x=1) and (~(s1<=s2) -> x=0).
7. `x := !s`: (s=0 -> x=1) and (~(s=0) -> x=0).
8. `x := s1 || s2`: ((s1=0 and s2=0) -> x=0) and ((~(s1=0) or ~(s2=0)) -> x=1).
9. `x := s1 && s2`: (~(s1=0) and ~(s2=0)) -> x=1) and (((s1=0) or (s2=0)) -> x=0).

#### Arrays

1. `x := array N`: creates an array of `N` elements of type `ff`, where `N` is a constant.
2. `x := y[s]`: extracts the value of `y[s]` into variable `x`.
3. `x[s1] := s2`: sets the value of `x[s1]` to a simple expression `s2`.
4. `x := y`: if `y` is of array type, copies the array `y` into `x` (old value of `x`, if any, is destroyed).

> [!NOTE] 
>
> We should be aware that translating an array access `x[s]` > to
> formulas can be done in a compact way only when the index `s` is > a
> value. There is no constant propagation, this should be done >
> independently as a preprocessing step.

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
for(i,LB,UB,D) { body }
```

where `LB`, `UB`, and `D` are constants. It should be interpreted as
the C-loop:

```text
for(i=LB;i<UB,i+=D) { body }
```

The loop index `i` is not a variable, but rather a constant value and
inside `body` it can be used as `#i`.

>[!note]
>
>The implementation is based on loop unrolling, where in every
>iteration there is a **constant** that is equivalent to the loop
>index. To refer to this constant value we can use `#i`.

>[!important]
>
>Since `#i` is not a variable, it cannot appear in the encoding to
>SMT, we must use the corresponding value that is also available at
>symbolic execution time.

>[!note]
> Handling bounded loops was not promised in the project proposal.

#### Function calls

1. `x1,...,xk = fname(s1,...,sn)`: variables `x1,...,xk` receive the returned values, which can be arrays as well.

#### Support for SSA

There is no direct support for SSA in the language, because it is
structured, so we can always add the phi-functions at the end of the
branches of an if-statement.
