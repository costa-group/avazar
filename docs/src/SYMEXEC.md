# Symbolic Execution of Core-LLZK Programs

The goal of symbolic execution of core-LLZK is to generate an SMT2 formula that faithfully represents the big-step semantics of the witness program (also referred to simply as the witness or the program). This formula can then be used, for example, to prove that the witness and the corresponding circuit are equivalent — that is, that they compute the same function.

To illustrate the idea, consider a program that consists of two instructions: `y = felt.mul y x` followed by `z = felt.add y z`. Assuming that `x` and `y` are represented by constraint variables `X0` and `Y0`, the first instruction is encoded as `(= Y1 (ff.mul Y0 X0))`, where `Y1` is a fresh variable representing the updated value of `y`. The second instruction is then encoded as `(= Z1 (ff.add Y1 Z0))`. The operations `ff.add` and `ff.mul` are finite-field addition and multiplication in the SMT2 format. The formula that represents the program is then

```
(and (= Y1 (ff.mul Y0 X0)) (= Z1 (ff.add Y1 Z0)))
```

In what follows we will describe the encoding of the different instructions of the language, how they are composed and how a function can be encoded in a modular way as SMT2 macros.

We will assume familiarity with the finite-field SMT2 format, and if we introduce some new constructs they will be explained just when they are used to facilitate reading.

All concrete values and operations used in the rest of this document are over a finite-field with respect to a given prime `p` that fits in exactly `k` bits. We will thus drop the term *finite-field*.

## Assigning constraint variables to program variables

The first thing we need to model is how to relate program variables to their corresponding constraint variables. For this we will use a mapping `T` such that `T[v]` returns one of the following values:

- A concrete finite-field value.
- A constraints variable.
- An array-mapping `T'` such that `T'[i]` represents the symbolic value of the i-th position of the array `v` (the value can be either a concrete finite-field value or a constraints variable).

Why we need the concrete finite-field value? This is one of the powerful features of the translation since it will execute the instructions when all variables have concrete values and thus avoid generating new constraint variables and corresponding formula. Also handles aliasing, i.e., if we have an instruction like `x = y`, then we will not generate a new variable for `x` and add a formula stating the equality, but rather will assign to `x` the current value of `y` and avoid generating a new formula.

We will use the syntax `T' = T[v->Y]` for a symbolic variable mapping that is obtained from `T` by setting `T[v]` to `Y`, replacing its current value if any.

For simplicity, sometimes we have an `sexp` which can be a variable or a value. When looking up `T[sexp]`, it returns the constraint variable when `sexp` is a variable, and returns `sexp` itself when it is a finite-field value.

## Encoding of expressions

Encoding of an expression, in the context of a symbolic variable map `T`, generates formula of the form `(F,LV)` where `F` is the formula and `LV` are the local constraint variables used. Encoding of expressions does not modify the symbolic variables map, it simply uses the constraint variables of `T` and binds the result to a given variable `OUTV` (which is not part of `LV`, it will be generated when encoding an assignment).

### Arithmetic

#### `sexp` (Identity)

 `F` is `(= OUTV T[sexp])` and `LV={}`.

#### `felt.neg sexp` (Negation)

 `F` is `(= OUTV (ff.neg T[sexp]))` and `LV={}`.

#### `felt.add sexp1 sexp2` (Addition)

 `F` is `(= OUTV (ff.add T[sexp1] T[sexp2]))` and `LV={}`.

#### `felt.sub sexp1 sexp2` (Subtraction)

 `F` is `(= OUTV (ff.sub T[sexp1] T[sexp2]))` and `LV={}`.

#### `felt.mul sexp1 sexp2` (Multiplication)

 `F` is `(= OUTV (ff.mul T[sexp1] T[sexp2]))` and `LV={}`.

#### `felt.div sexp1 sexp2` (Multiplication by modular inverse)

 `F` is `(= (ff.mul OUTV T[sexp2]) T[sexp1])` and `LV={}`.
