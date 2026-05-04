# Symbolic Execution of Core-LLZK Programs

The goal of symbolic execution of core-LLZK is to generate an SMT2 formula that faithfully represents the big-step semantics of the witness program (also referred to simply as the witness or the program). This formula can then be used, for example, to prove that the witness and the corresponding circuit are equivalent — that is, that they compute the same function.

To illustrate the idea, consider a program that consists of two instructions: `y = felt.mul y x` followed by `z = felt.add y z`. Assuming that `x` and `y` are represented by constraint variables $X_0$ and $Y_0$, the first instruction is encoded as $Y_1 = Y_0  \cdot X_0$, where $Y_1$ is a fresh variable representing the updated value of `y`. The second instruction is then encoded as $Z_1 = Y_1 + Z_0$. The formula that represents the program is then

$$Y_1 = Y_0  \cdot X_0 \land Z_1 = Y_1 + Z_0$$

Note that, for clarity, we write constraints using logical formula, where the arithmetic operations are interpreted over a finite field. Translating them into SMT2 format is straightforward.

In what follows we will describe the encoding of the different instructions of the language, how they are composed and how a function can be encoded in a modular way as SMT2 macros.

> [!NOTE]
>
> All concrete values and operations used in the rest of this document are over a finite-field with respect to a given prime `p` that fits in exactly `k` bits. We will thus sometimes drop the term *finite-field*.

## Assigning constraint variables to program variables

The first thing we need to model is how to relate program variables to their corresponding constraint variables. For this we will use a mapping $T$ (that we refer to an a *symbolic environment*) such that $T[x]$, where $x$ is a program variable, returns one of the following values:

- A concrete finite-field value.
- A constraints variable.
- An symbolic environment $T'$ such that $T'[i]$ represents the symbolic value of the $i$-th position of the array $x$ (the value can be either a concrete finite-field value or a constraints variable, it cannot be array again).

*Why we need the concrete finite-field value?*

 This is one of the powerful features of the translation, since it will execute the instructions when all variables have concrete values and thus avoid generating new constraint variables and corresponding formula. It also handles aliasing, i.e., if we have an instruction like `x = y`, then we will not generate a new variable for `x` and add a formula stating the equality, but rather will assign to `x` the current value of `y` and avoid generating a new formula.

We will use the syntax $T' = T[x\mapsto X_i]$ for a symbolic environment that is obtained from $T$ by setting $T[x]$ to $X_i$, replacing its current value if any.

For simplicity, when we have a simple expression `sexp`, which can be a variable or a value, then abusing notation we assume that $T[\mathit{sexp}]$ returns `sexp` itself when it is a finite-field value.

## Encoding of expressions

Encoding of an expression, in the context of a symbolic environment $T$, generates formula of the form $(F,L)$ where $F$ is the formula and $L$ is a set local constraint variables used in $F$. I.e., variables in $L$ do not come from $T$ but rather they are intermediate fresh variables that were generate during the encoding of the expression.

Encoding of expressions does not modify the symbolic environment $T$, it simply uses the constraint variables of $T$ and binds the result to a given output variable $V_o$ (which is not part of $L$, it will be generated when encoding an assignment). Note that all variables that appear in an expression do not correspond to arrays, otherwise the program is ill-typed (array accesses are handled using dedicated instructions).

Next we describe the encodings of the different expressions as they are defined in the [core-LLZK language](CORELLZK.md).

### Arithmetic

#### `sexp` (Identity)

- $F$ is $V_o = T[\mathtt{sexp}]$
- $L=\emptyset$

#### `felt.neg sexp` (Negation)

- $F$ is $V_o = -T[\mathtt{sexp}]$
- $L=\emptyset$

#### `felt.add sexp1 sexp2` (Addition)

- $F$ is $V_o = T[\mathtt{sexp1}]+T[\mathtt{sex2}]$
- $L=\emptyset$

#### `felt.sub sexp1 sexp2` (Subtraction)

- $F$ is $V_o = T[\mathtt{sexp1}]-T[\mathtt{sex2}]$
- $L=\emptyset$

#### `felt.mul sexp1 sexp2` (Multiplication)

- $F$ is $V_o = T[\mathtt{sexp1}] \cdot T[\mathtt{sexp2}]$
- $L=\emptyset$

#### `felt.div sexp1 sexp2` (Multiplication by modular inverse)

- $F$ is $V_o \cdot T[\mathtt{sexp2}] = T[\mathtt{sexp1}]$
- $L=\emptyset$

### Bitwise

Encoding of bitwise operations heavily relies on the binary expansion of a given variable $X$ (it also works when $X$ is a value). This operation is denoted by $\mathtt{bitify}(X,n)$, i.e., the binary expansion of $X$ using $n$ bits. We assume that it generates a formula that is a conjunction of the following constraints:

1. $X = \sum_{i=0}^{n-1} 2^i \cdot X_{b_i}$, where $X_{b_0},\ldots,X_{b_{n-1}}$ are fresh finite-field variables representing the bits.
2. $X_{b_i} \cdot (1 - X_{b_i}) = 0$ for each $i$ (which can also be replaced by $\mathtt{range}(X_{b_i},0,1)$ when range constraints are allowed).

#### `bit.and sexp1 sexp2` (Bitwise AND)

Let $(F_1,L_1)$, $(F_2,L_2)$, and $(F_3,L_3)$ be the encodings corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding $F$ is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

The local variables are $L=L_1\cup L_2\cup L_3$.

As an optimization, when `sexp1` is a constant that fits in $m$ bits, the encoding of $T[\mathtt{sexp1}]$ and $V_o$ can be done with respect to $m$ bits instead of $k$ bits, and then use $F$ as

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

This is valid because all bits $V_{o_{b_i}}$ with $i \ge m$ are $0$. Here we save $k-m$ variables, which can be important for scalability during the verification phase. We can apply a similar optimization for the case when `sexp2` is a constant.

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

#### `bit.not sexp` (Bitwise NOT)

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp}]$, produced by the respective $\mathtt{bitify}$ call.

The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = 1-X_{b_i})$$

The local variables are $L=L_1\cup L_2$.

#### `bit.shl sexp1 sexp2` (Left shift)

The encoding of left-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we start with the first case and then the second.

##### The case when `sexp2` is a constant

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = 0) \land (\bigwedge_{i=m}^{k-1} V_{o_{b_i}} = X_{b_{i-m}})$$

The local variables are $L=L_1\cup L_2$.

##### The general case

The second case is more elaborated, and is based computing the binary expansion of $T[\mathtt{sexp2}]$ using $\lceil\log_2 k\rceil$ bits, i.e., $\mathtt{bitify}(T[\mathtt{sexp2}],\lceil\log_2 k\rceil)$, and then iteratively left-shift by $i$ position when the corresponding bit of
$T[\mathtt{sexp2}]$ is 1.

#### `bit.shr sexp1 sexp2` (Right shift)

The encoding of right-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we start with the first case and then the second.

##### The case when `sexp2` is a constant

Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding $F$ is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-m-1} V_{o_{b_i}} = X_{b_{i+m}}) \land (\bigwedge_{i=k-m}^{k-1} V_{o_{b_i}} = 0)$$

The local variables are $L=L_1\cup L_2$.

##### The general case

It is based on the same idea as the general case of `bit.shl`.

### Boolean

We will rely on formulas of the form $\mathtt{ite}(F,V_1,V_2)$, interpreted as: if $F$ holds then $V_1$ otherwise $V_2$. Note that when $F$ is a bit variable this can be expressed arithmetically as $F \cdot V_1 + (1-F) \cdot V_2$, however, it keeping the $\mathtt{ite}$ form might provide important explicit information for the verifier (that one that uses the encoding of the witness program).

Note that Boolean values are simulated using finite-field values, where $0$ represents *false* and any other value is *true*.

#### `bool.eq sexp1 sexp2`(Equality)

The formula $F$ is as follows:

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=T[\mathtt{sexp2}],1,0) \wedge V_o \cdot (1-V_o)=0$$

The set of local variables is $L=\emptyset$.

#### `bool.neq sexp1 sexp2` (Inequality)

The formula $F$ is as follows:

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=T[\mathtt{sexp2}],0,1) \wedge V_o \cdot (1-V_o)=0$$

The set of local variables is $L=\emptyset$.

#### `bool.and sexp1 sexp2` (Logical AND)

The formula $F$ is as follows:

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=0 \vee T[\mathtt{sexp2}]=0,0,1) \wedge V_o \cdot (1-V_o)=0$$

The set of local variables is $L=\emptyset$.

#### `bool.or sexp1 sexp2`(Logical OR)

The formula $F$ is as follows:

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=0 \land T[\mathtt{sexp2}]=0,0,1) \wedge V_o \cdot (1-V_o)=0$$

The set of local variables is $L=\emptyset$.

#### `bool.not sexp` (Logical NOT)

The formula $F$ is as follows:

$$V_o = \mathtt{ite}(T[\mathtt{sexp}]=0,1,0) \wedge V_o \cdot (1-V_o)=0$$

The set of local variables is $L=\emptyset$.

#### `bool.lt sexp1 sexp2` (Signed less than)

First recall that we deal with signed values. Thus, comparisons interpret field elements as signed integers. The order is defined as

$$\mathit{mid}, ..., p-1, 0, ..., \mathit{mid}-1$$

where $\mathit{mid} = \frac{p}{2}+1$. The idea is that $\mathit{mid}, ..., p-1$ represent negative numbers.

There are two special cases that we consider, which improve the overall performance of the verification process. There are obtained when `sexp1` or `sexp2` are constant values. We describe these cases first, and the general case when both are variables. Note that the case when both `sexp1` and `sexp2` are constant is handled when executing the corresponding command (since both are constant, the comparison will be simple execute).

##### The case when `sexp1` is a constant

Let $v$ be the value of `sexp1`, so we want to encode the signed comparison $v<\mathtt{sexp2}$. The encoding is divided into several case, in all of them the formula $F$ is

$$V_o = \mathtt{ite}(F',1,0) \land V_o\cdot(1-V_o)=0$$

where $F'$ is:

- if $v = \mathit{mid}-1$, then $F'$ is *false*, because $mid-1$ represents the largest non-negative value.

- if $v < \mathit{mid}-1$, the $F'$ is $\mathtt{range}(T[\mathtt{sexp2}], v+1, \mathit{mid}-1)$, because $T[\mathtt{sexp2}]$ can be any positive larger than $v$.

- if $v = p-1$, then $F'$ is $range(T[\mathtt{sexp2}], 0, \mathit{mid}-1)$, because $T[\mathtt{sexp2}]$ can be any non-negative number.

- if $v \ge mid$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp2}], v+1, p-1) \vee \mathtt{range}(T[\mathtt{sexp2}], 0, \mathit{mid}-1)$, because $v$ is negative, so $T[\mathtt{sexp2}]$ can be any positive of negative larger than $v$.

The set of local variables is $L=\emptyset$.

##### The case when `sexp2` is a constant

Let $v$ be the value of `sexp2`, so we want to encode the signed comparison $\mathtt{sexp1}<v$. The encoding is divided into several case, in all of them the formula $F$ is

$$V_o = \mathtt{ite}(F',1,0) \land V_o\cdot(1-V_o)=0$$

where $F'$ is defined separately for each case:

- if $v = \mathit{mid}$, then $F'$ is *false*, because $mid$ represents the smallest negative value.

- if $v > \mathit{mid}$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, v-1)$, because $v$ is negative and thus $T[\mathtt{sexp1}]$ is a negative number smaller than $v$.

- if $v = 0$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, p-1)$, because $T[\mathtt{sexp1}]$ must be negative.

- if $0 < v < \mathit{mid}$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], 0, v-1) \vee \mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, p-1)$, because $v$ is positive so $T[\mathtt{sexp1}]$ can be negative or non-negative smaller than $v$.

The set of local variables is $L=\emptyset$.

##### The general case

We assume that both `sexp1` and `sexp2` are not constant values, so we want to encode the signed comparison $\mathtt{sexp1}<\mathtt{sexp2}$. Let $(F_1,L_1)$ and $(F_2,L_2)$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(T[\mathtt{sexp2}],k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The idea is to compare the bits from the most to the least significant, until we find $i$ such that $X_{b_i}=0 \land Y_{b_i}=1$, in which case the comparison is *true*, otherwise it is *false*. This can be done by defining $F$ as

$$F_1 \land F_2 \land V_o = G_k \land V_o\cdot(1-V_o)=0$$

where $G_i$ is recursively defined as:

- $G_0 = 0$
- $G_i = \mathtt{ite}(X_{b_i}=0 \land Y_{b_i}=1,1,G_{i-1})$

The set of local variables is $L=L_1\cup L_2$.

#### `bool.gt sexp1 sexp2` (Signed greater than)

This is done by using the encoding of `bool.lt sexp2 sexp1`.

#### `bool.le sexp1 sexp2` (Signed less or equal)

It is computed as the negation of `bool.lt sexp2 sexp1`. Suppose $(F_1,L_1)$ is the encoding of `bool.lt sexp2 sexp1` using an auxiliary output variable $V_o'$, then $F$ is

$$F_1 \land V_o = 1-V_o' \land V_o\cdot(1-V_o)=0$$

The set of local variables is $L=L_1\cup \{V_o'\}$.

#### `bool.ge sexp1 sexp2` (Signed greater or equal)

This is done by using the encoding of `bool.le sexp2 sexp1`.

## Encoding of commands

Next we describe how commands and lists of commands are encoded. Any encoding of a command receives as input a command $C$ and a symbolic environment $T$, and produces $(T,F,T',L)$ where $F$ and $L$ are the corresponding formula and the local auxiliary variables, and $T'$ is a new symbolic environment that results from $T$ by modifying the values of some variables (due to the symbolic execution of $C$).

Executing a list of commands $[C_1,\ldots,C_n]$ is done recursively as follows:

- The symbolic execution of an empty list generates $(T,\mathit{true},T',\emptyset)$
- The symbolic execution of $[C_1,\ldots,C_n]$ is done in two steps. We first execute $C_1$ using $T$ and obtain $(T,F,T',L)$, then recursively execute  $[C_2,\ldots,C_n]$ using T' and obtain $(T',F',T'',L')$, and then the result is $(T,F\land F',T'',L\cup L')$.

The symbolic execution of a function $f$ is supposed to generate a macro that we denote as

$$\mathtt{f}(I,O,L) = F$$

where $I$ and $O$ are a sequences of constraint variables obtained from the input and output parameters of function $f$, $L$ is a sequence of local variables used in the formula $F$ (these are not only the auxiliary ones generated when encoding expressions, but any variable used in $F$ that does not appear in $I$ and $O$). We will explain how this encoding is generated later, but for now we just need to explain it briefly since we will assume it when encoding function calls.

Next we describe the encodings of the different commands as they are defined in the [core-LLZK language](CORELLZK.md).

### Assignment

The encoding of an assignment starts by trying to concretely evaluate `exp`, and if all variables used in `exp` have constant values in $T$, the evaluation succeeds and results in a value $v$. We then generate $T'=T[\mathit{id} \mapsto v]$, and the encoding is $(T,\mathit{true},T',\emptyset)$.

If `exp` cannot be concretely evaluated, we symbolically evaluate `exp` using $T$ and a fresh output variable $V_o$ and obtain the encoding $(F,L)$. Then we generate $T'=T[\mathit{id} \mapsto V_o]$, and the encoding is $(T,F,T',L)$.
