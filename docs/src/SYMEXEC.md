# Symbolic Execution of Core-LLZK Programs

The goal of symbolic execution of core-LLZK is to generate an SMT2 formula that faithfully represents the big-step semantics of the witness program (also referred to simply as the witness or the program). This formula can then be used, for example, to prove that the witness and the corresponding circuit are equivalent — that is, that they compute the same function.

To illustrate the idea, consider a program that consists of two instructions: `y = felt.mul y x` followed by `z = felt.add y z`. Assuming that `x` and `y` are represented by constraint variables $X_0$ and $Y_0$, the first instruction is encoded as $Y_1 = Y_0  \cdot X_0$, where $Y_1$ is a fresh variable representing the updated value of `y`. The second instruction is then encoded as $Z_1 = Y_1 \cdot Z_0$. The formula that represents the program is then

$$Y_1 = Y_0  \cdot X_0 \land Z_1 = Y_1 \cdot Z_0$$

Note that, for clarity, we write constraints using logical formula, where the arithmetic operations are interpreted over a finite field. Translating them into SMT2 format is straightforward.

In what follows we will describe the encoding of the different instructions of the language, how they are composed and how a function can be encoded in a modular way as SMT2 macros.

All concrete values and operations used in the rest of this document are over a finite-field with respect to a given prime `p` that fits in exactly `k` bits. We will thus sometimes drop the term *finite-field*.

## Assigning constraint variables to program variables

The first thing we need to model is how to relate program variables to their corresponding constraint variables. For this we will use a mapping $T$ such that $T[x]$, where $x$ is a program variable, returns one of the following values:

- A concrete finite-field value.
- A constraints variable.
- An array-mapping $T'$ such that $T'[i]$ represents the symbolic value of the $i$-th position of the array $x$ (the value can be either a concrete finite-field value or a constraints variable).

Why we need the concrete finite-field value?

This is one of the powerful features of the translation, since it will execute the instructions when all variables have concrete values and thus avoid generating new constraint variables and corresponding formula. Also handles aliasing, i.e., if we have an instruction like `x = y`, then we will not generate a new variable for `x` and add a formula stating the equality, but rather will assign to `x` the current value of `y` and avoid generating a new formula.

We will use the syntax $T' = T[x\mapsto X_i]$ for a symbolic variable mapping that is obtained from $T$ by setting $T[x]$ to $X_i$, replacing its current value if any.

For simplicity, when we have a simple expression `sexp`, which can be a variable or a value, then $T[\mathit{sexp}]$ returns `sexp` itself when it is a finite-field value.

## Encoding of expressions

Encoding of an expression, in the context of a symbolic variable map $T$, generates formula of the form $(F,LV)$ where $F$ is the formula and $L$ is a set local constraint variables used in $F$. I.e., variables in $L$ do not come from $T$ but rather they are intermediate fresh variables.

Encoding of expressions does not modify the symbolic variables map $T$, it simply uses the constraint variables of $T$ and binds the result to a given variable $V_o$ (which is not part of $L$, it will be generated when encoding an assignment).

Next we describe the encodings of the different expressions as they are defined in the [core-LLZK language](CORELLZK.md).

### Arithmetic

#### `sexp` (Identity)

- $F$ is $V_o = X$ where $X=T[\mathtt{sexp}]$
- $L=\emptyset$

#### `felt.neg sexp` (Negation)

- $F$ is $V_o = -X$ where $X=T[\mathtt{sexp}]$
- $L=\emptyset$

#### `felt.add sexp1 sexp2` (Addition)

- $F$ is $V_o = X+Y$ where $X=T[\mathtt{sexp1}]$ and $Y=T[\mathtt{sexp1}]$
- $L=\emptyset$

#### `felt.sub sexp1 sexp2` (Subtraction)

- $F$ is $V_o = X-Y$ where $X=T[\mathtt{sexp1}]$ and $Y=T[\mathtt{sexp1}]$
- $L=\emptyset$

#### `felt.mul sexp1 sexp2` (Multiplication)

- $F$ is $V_o = X \cdot Y$ where $X=T[\mathtt{sexp1}]$ and $Y=T[\mathtt{sexp1}]$
- $L=\emptyset$

#### `felt.div sexp1 sexp2` (Multiplication by modular inverse)

- $F$ is $V_o \cdot Y = X$ where $X=T[\mathtt{sexp1}]$ and $Y=T[\mathtt{sexp1}]$
- $L=\emptyset$

### Bitwise

Encoding of bitwise operations heavily relies on the binary expansion of a given variable $X$ (it also work wne $X$ is a value). This operation is denoted by $\mathtt{bitify}(X,n)$, i.e., the binary expansion of $X$ using $n$ bits. We assume that it generates a formula that is a conjunction of the following constraints:

1. $X = \sum_{i=0}^{n-1} 2^i \cdot X_{b_i}$, where $X_{b_0},\ldots,X_{b_{n-1}}$ are fresh finite-field variables representing the bits.
2. $X_{b_i} \cdot (1 - X_{b_i}) = 0$ for each $i$ (which can also be replaced by $(\mathtt{ff.range}~X_{b_i}~0~1)$ when range constraints are allowed).

#### `bit.and sexp1 sexp2` (Bitwise AND)

Let $(F_1,L_1)$, $(F_2,L_2)$, and $(F_3,L_3)$ be the encodings corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding $F$ is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

The local variables are $L=L_1\cup L_2\cup L_3$.

As an optimization, when `sexp1` is a constant that fits in $m$ bits, the encoding of $T[\mathtt{sexp1}]$ and $V_o$ can be done with respect to $m$ bits instead of $k$ bits, and then use $F$ as

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

This is valid because all bits $V_{o_{b_i}}$ with $i \ge m$ are $0$. Here we save $k-m$ variables, which can be important for scalability during the verification phase.

#### `bit.or sexp1 sexp2` (Bitwise OR)

Let $(F_1,L_1)$, $(F_2,L_2)$, and $(F_3,L_3)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding $F$ is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i} + Y_{b_i} - X_{b_i} \cdot Y_{b_i})$$

The local variables are $L=L_1\cup L_2\cup L_3$.

#### `bit.xor sexp1 sexp2` (Bitwise XOR)

Let $(F_1,L_1)$, $(F_2,L_2)$, and $(F_3,L_3)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding $F$ is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i} + Y_{b_i} -  2 \cdot X_{b_i} \cdot Y_{b_i})$$

The local variables are $L=L_1\cup L_2\cup L_3$.

#### `bit.not sexp1` (Bitwise NOT)

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call.

The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = 1-X_{b_i})$$

The local variables are $L=L_1\cup L_2$.

#### `bit.shl sexp1 sexp2` (Left shift)

The encoding of left-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we start with the first case and then the second.

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = 0) \land (\bigwedge_{i=m}^{k-1} V_{o_{b_i}} = X_{b_{i-m}})$$

The local variables are $L=L_1\cup L_2$.

We skip the second case as it is more elaborated. In principle, it computes the binary expansion of `sexp2` as well, and then iteratively shifts the bits of `sexp1` by $i$ positions depending on whether the $i$-th bit of `sexp2` is 1 or 0.

#### `bit.shr sexp1 sexp2` (Right shift)

The encoding of right-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we start with the first case and then the second.

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-m-1} V_{o_{b_i}} = X_{b_{i+m}}) \land (\bigwedge_{i=k-m}^{k-1} V_{o_{b_i}} = 0)$$

The local variables are $L=L_1\cup L_2$.

We skip the second case as it is more elaborated. In principle, it computes the binary expansion of `sexp2` as well, and then iteratively shifts the bits of `sexp1` by $i$ positions depending on whether the $i$-th bit of `sexp2` is 1 or 0.
