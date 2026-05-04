# Symbolic Execution of Core-LLZK Programs

The goal of symbolic execution of core-LLZK is to generate an SMT2 formula that faithfully represents the big-step semantics of the witness program (also referred to simply as the witness or the program). This formula can then be used, for example, to prove that the witness and the corresponding circuit are equivalent — that is, that they compute the same function.

To illustrate the idea, consider a program that consists of two instructions: `y = felt.mul y x` followed by `z = felt.add y z`. Assuming that `x`, `y` and `z` are represented by constraint variables $X_0$, $Y_0$, and $Z_0$, the first instruction is encoded as $Y_1 = Y_0  \cdot X_0$, where $Y_1$ is a fresh variable representing the updated value of `y`. The second instruction is then encoded as $Z_1 = Y_1 + Z_0$. The formula that represents the program is then

$$Y_1 = Y_0  \cdot X_0 \land Z_1 = Y_1 + Z_0$$

Note that, for clarity, we write constraints using standard (mathematical) format logical formulas, where the arithmetic operations are interpreted over a finite field. Translating them into SMT2 format is straightforward.

In what follows we will describe the encoding of the different instructions of the language, how they are composed, and how a function can be encoded in a modular way as SMT2 macros. Then, in the last section, we explain where the implementation of the symbolic execution can be found, and how it can be used.

> [!NOTE]
>
> All concrete values and operations used in the rest of this document are over a finite-field with respect to a given prime `p` that fits in exactly `k` bits, unless stated otherwise. We will thus sometimes drop the term *finite-field*.

## Assigning constraint variables to program variables

The first thing we need to model is how to relate program variables to their corresponding constraint variables. For this we will use a mapping $T$ (referred to as a *symbolic environment*) such that $T[x]$, where $x$ is a program variable, returns one of the following values:

- A concrete finite-field value.
- A constraint variable.
- A symbolic (array) environment $T'$ such that $T'[i]$ represents the symbolic value of the $i$-th position of the array $x$ (the value can be either a concrete finite-field value or a constraint variable; it cannot be an array again).

_Why we need the concrete finite-field value in the symbolic environment_ $T$_?_

 This is needed in order to achieve one of the powerful features of the translation, which executes the instructions when all variables have concrete values and thus avoid generating new constraint variables and corresponding formulas. It also handles aliasing, i.e., if we have an instruction like `x = y`, then we will not generate a new variable for `x` and add a formula stating the equality, but rather will assign to `x` the current value of `y` and avoid generating a new formula.

We will use the syntax $T' = T[x\mapsto X_i]$ for a symbolic environment that is obtained from $T$ by setting $T[x]$ to $X_i$, replacing its current value if any.

For simplicity, when we have a simple expression `sexp`, which can be a variable or a value, then abusing notation we assume that $T[\mathit{sexp}]$ returns `sexp` itself when it is a finite-field value.

## Encoding of expressions

Encoding of an expression, in the context of a symbolic environment $T$, generates a formula $F$ that encodes the result of evaluating the expression.

Encoding of expressions does not modify the symbolic environment $T$, it simply uses the constraint variables of $T$ and binds the result to a given output variable $V_o$. Note that all variables that appear in an expression do not correspond to arrays, otherwise the program is ill-typed (array accesses are handled using dedicated instructions).

Next we describe the encodings of the different expressions as they are defined in the [core-LLZK language](CORELLZK.md).

### Arithmetic

#### `sexp` (Identity)

The encoding is the formula $V_o = T[\mathtt{sexp}]$

#### `felt.neg sexp` (Negation)

The encoding is the formula $V_o = -T[\mathtt{sexp}]$

#### `felt.add sexp1 sexp2` (Addition)

The encoding is the formula $V_o = T[\mathtt{sexp1}]+T[\mathtt{sex2}]$

#### `felt.sub sexp1 sexp2` (Subtraction)

The encoding is the formula $V_o = T[\mathtt{sexp1}]-T[\mathtt{sex2}]$

#### `felt.mul sexp1 sexp2` (Multiplication)

The encoding is the formula $V_o = T[\mathtt{sexp1}] \cdot T[\mathtt{sexp2}]$

#### `felt.div sexp1 sexp2` (Multiplication by modular inverse)

The encoding is the formula $V_o \cdot T[\mathtt{sexp2}] = T[\mathtt{sexp1}]$

### Bitwise

Encoding of bitwise operations heavily relies on the binary expansion of a given constraint variable $X$ (it also works when $X$ is a finite-field value). This operation is denoted by $\mathtt{bitify}(X,n)$, i.e., the binary expansion of $X$ using $n$ bits. We assume that it generates a formula that is a conjunction of the following constraints:

1. $X = \sum_{i=0}^{n-1} 2^i \cdot X_{b_i}$, where $X_{b_0},\ldots,X_{b_{n-1}}$ are fresh finite-field variables representing the bits of $X$.
2. $\bigwedge_{i=0}^{n-1} X_{b_i} \cdot (1 - X_{b_i}) = 0$ to state that the bits can bey either $0$ or $1$. The constraint $X_{b_i} \cdot (1 - X_{b_i}) = 0$ can also be replaced by $\mathtt{range}(X_{b_i},0,1)$ when range constraints are allowed.

Recall the the finite-field is with respect to a prime $p$ that fits in $k$ bits.

#### `bit.and sexp1 sexp2` (Bitwise AND)

Let $F_1$, $F_2$, and $F_3$ be the encodings corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

As an optimization, when `sexp1` is a constant that fits in $m$ bits, the encoding of $T[\mathtt{sexp1}]$ and $V_o$ can be done with respect to $m$ bits instead of $k$ bits, and then use the following encoding

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = X_{b_i}\cdot Y_{b_i})$$

This is valid because all bits $V_{o_{b_i}}$ with $i \ge m$ are $0$. Here we save $k-m$ variables, which can be important for scalability during the verification phase. We can apply a similar optimization for the case when `sexp2` is a constant.

#### `bit.or sexp1 sexp2` (Bitwise OR)

Let $F_1$, $F_2$, and $F_3$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encodingis

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i} + Y_{b_i} - X_{b_i} \cdot Y_{b_i})$$

#### `bit.xor sexp1 sexp2` (Bitwise XOR)

Let $F_1$, $F_2$, and $F_3$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$, $\mathtt{bitify}(T[\mathtt{sexp2}],k)$, and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The encoding is

$$F_1 \land F_2 \land F_3 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = X_{b_i} + Y_{b_i} -  2 \cdot X_{b_i} \cdot Y_{b_i})$$

#### `bit.not sexp` (Bitwise NOT)

Let $F_1$ and $F_2$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp}]$, produced by the respective $\mathtt{bitify}$ call.

The encoding is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-1} V_{o_{b_i}} = 1-X_{b_i})$$

#### `bit.shl sexp1 sexp2` (Left shift)

The encoding of left-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we explain the two cases.

##### The case when `sexp2` is a constant

Let $F_1$ and $F_2$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{m-1} V_{o_{b_i}} = 0) \land (\bigwedge_{i=m}^{k-1} V_{o_{b_i}} = X_{b_{i-m}})$$

##### The general case

The second case is more elaborated, and is based computing the binary expansion of $T[\mathtt{sexp2}]$ using $\lceil\log_2 k\rceil$ bits, i.e., $\mathtt{bitify}(T[\mathtt{sexp2}],\lceil\log_2 k\rceil)$, and then iteratively left-shift by $i$ position when the corresponding bit of
$T[\mathtt{sexp2}]$ is 1.

#### `bit.shr sexp1 sexp2` (Right shift)

The encoding of right-shift considers two cases: the first handles the case when `sexp2` is a value, and the other when it is not. In practice, we rarely find the second case. Next we explain the two cases.

##### The case when `sexp2` is a constant

Let $F_1$ and $F_2$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(V_o,k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$, produced by the respective $\mathtt{bitify}$ call. Let the value of `sexp2` be $m$. The encoding is

$$F_1 \land F_2 \land (\bigwedge_{i=0}^{k-m-1} V_{o_{b_i}} = X_{b_{i+m}}) \land (\bigwedge_{i=k-m}^{k-1} V_{o_{b_i}} = 0)$$

##### The general case

It is based on the same idea as the general case of `bit.shl`.

### Boolean

We will rely on formulas of the form $\mathtt{ite}(F,V_1,V_2)$, interpreted as: if $F$ holds then $V_1$ otherwise $V_2$. Note that when $F$ is a bit variable this can be expressed arithmetically as $F \cdot V_1 + (1-F) \cdot V_2$, however, keeping the $\mathtt{ite}$ form may provide important explicit information during the verification process (the one that uses the encoding of the witness program).

Note that Boolean values are simulated using finite-field values, where $0$ represents *false* and any other value is *true*.

#### `bool.eq sexp1 sexp2` (Equality)

The encoding is

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=T[\mathtt{sexp2}],1,0) \wedge V_o \cdot (1-V_o)=0$$

#### `bool.neq sexp1 sexp2` (Inequality)

The encoding is

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=T[\mathtt{sexp2}],0,1) \wedge V_o \cdot (1-V_o)=0$$

#### `bool.and sexp1 sexp2` (Logical AND)

The encoding is

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=0 \vee T[\mathtt{sexp2}]=0,0,1) \wedge V_o \cdot (1-V_o)=0$$

#### `bool.or sexp1 sexp2` (Logical OR)

The encoding is

$$V_o = \mathtt{ite}(T[\mathtt{sexp1}]=0 \land T[\mathtt{sexp2}]=0,0,1) \wedge V_o \cdot (1-V_o)=0$$

#### `bool.not sexp` (Logical NOT)

The encoding is

$$V_o = \mathtt{ite}(T[\mathtt{sexp}]=0,1,0) \wedge V_o \cdot (1-V_o)=0$$

#### `bool.lt sexp1 sexp2` (Signed less than)

First recall that we deal with signed values. Thus, comparisons interpret field elements as signed integers. The order of the field elements is defined as

$$\mathit{mid}, ..., p-1, 0, ..., \mathit{mid}-1$$

where $\mathit{mid} = \frac{p}{2}+1$. The idea is that $\mathit{mid}, ..., p-1$ represent negative numbers.

There are two special cases that we consider, which improve the overall performance of the verification process. They arise when `sexp1` or `sexp2` are constant values. We describe these cases first, followed by the general case when both are variables. Note that the case when both `sexp1` and `sexp2` are constant is handled when executing the corresponding command (since both are constant, the comparison is simply evaluated).

##### The case when `sexp1` is a constant

Let $v$ be the value of `sexp1`, so we want to encode the signed comparison $v<\mathtt{sexp2}$. The encoding is divided into several cases; in all of them the encoding is

$$V_o = \mathtt{ite}(F',1,0) \land V_o\cdot(1-V_o)=0$$

where $F'$ is:

- if $v =_{\mathbb N} \mathit{mid}-1$, then $F'$ is *false*, because $mid-1$ represents the largest non-negative value.

- if $v <_{\mathbb N} \mathit{mid}-1$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp2}], v+1, \mathit{mid}-1)$, because $T[\mathtt{sexp2}]$ can be any positive value larger than $v$.

- if $v =_{\mathbb N} p-1$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp2}], 0, \mathit{mid}-1)$, because $T[\mathtt{sexp2}]$ can be any non-negative number.

- if $v \ge_{\mathbb N} mid$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp2}], v+1, p-1) \vee \mathtt{range}(T[\mathtt{sexp2}], 0, \mathit{mid}-1)$, because $v$ is negative, so $T[\mathtt{sexp2}]$ can be any positive or negative value larger than $v$.

##### The case when `sexp2` is a constant

Let $v$ be the value of `sexp2`, so we want to encode the signed comparison $\mathtt{sexp1}<v$. The encoding is divided into several cases; in all of them the encoding is

$$V_o = \mathtt{ite}(F',1,0) \land V_o\cdot(1-V_o)=0$$

where $F'$ is defined separately for each case:

- if $v =_{\mathbb N} \mathit{mid}$, then $F'$ is *false*, because $mid$ represents the smallest negative value.

- if $v >_{\mathbb N} \mathit{mid}$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, v-1)$, because $v$ is negative and thus $T[\mathtt{sexp1}]$ is a negative number smaller than $v$.

- if $v =_{\mathbb N} 0$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, p-1)$, because $T[\mathtt{sexp1}]$ must be negative.

- if $0 \lt_{\mathbb N} v \lt_{\mathbb N} \mathit{mid}$, then $F'$ is $\mathtt{range}(T[\mathtt{sexp1}], 0, v-1) \vee \mathtt{range}(T[\mathtt{sexp1}], \mathit{mid}, p-1)$, because $v$ is positive so $T[\mathtt{sexp1}]$ can be negative or non-negative smaller than $v$.

##### The general case

We assume that both `sexp1` and `sexp2` are not constant values, so we want to encode the signed comparison $\mathtt{sexp1}<\mathtt{sexp2}$. Let $F_1$ and $F_2$ be the formulas corresponding to $\mathtt{bitify}(T[\mathtt{sexp1}],k)$ and $\mathtt{bitify}(T[\mathtt{sexp2}],k)$. Let $X_{b_i}$ denote the $i$-th bit of $T[\mathtt{sexp1}]$ and $Y_{b_i}$ the $i$-th bit of $T[\mathtt{sexp2}]$, produced by the respective $\mathtt{bitify}$ calls.

The idea is to compare the bits from the most to the least significant, until we find $i$ such that $X_{b_i}=0 \land Y_{b_i}=1$, in which case the comparison is *true*, otherwise it is *false*. This can be done using the encoding

$$F_1 \land F_2 \land V_o = G_k \land V_o\cdot(1-V_o)=0$$

where $G_i$ is recursively defined as:

- $G_0 = 0$
- $G_i = \mathtt{ite}(X_{b_i}=0 \land Y_{b_i}=1,1,G_{i-1})$

#### `bool.gt sexp1 sexp2` (Signed greater than)

This is done by using the encoding of `bool.lt sexp2 sexp1`.

#### `bool.le sexp1 sexp2` (Signed less or equal)

It is computed as the negation of `bool.lt sexp2 sexp1`. Suppose $F_1$ is the encoding of `bool.lt sexp2 sexp1` using an auxiliary output variable $V_o'$, then the encoding is

$$F_1 \land V_o = 1-V_o' \land V_o\cdot(1-V_o)=0$$

#### `bool.ge sexp1 sexp2` (Signed greater or equal)

This is done by using the encoding of `bool.le sexp2 sexp1`.

## Encoding of commands

Next we describe how commands and lists of commands are encoded. Any encoding of a command receives as input a command $C$ and a symbolic environment $T$, and produces $(T,F,T')$ where $F$ is the corresponding formula, and $T'$ is a new symbolic environment that results from $T$ by modifying the values of some variables (due to the symbolic execution of $C$).

Executing a list of commands $[C_1,\ldots,C_n]$ is done recursively as follows:

- The symbolic execution of an empty list generates $(T,\mathit{true},T)$.
- The symbolic execution of $[C_1,\ldots,C_n]$ is done in two steps. We first execute $C_1$ using $T$ and obtain $(T,F,T')$, then recursively execute $[C_2,\ldots,C_n]$ using $T'$ and obtain $(T',F',T'')$; the overall encoding is then $(T,F\land F',T'')$.

The symbolic execution of a function $\mathtt{foo}$ is supposed to generate a macro that we denote as

$$\mathtt{foo}(I,O,L) = F$$

where $I$ and $O$ are sequences of constraint variables obtained from the input and output parameters of function $\mathtt{foo}$, and $L$ is a sequence of local variables used in the formula $F$ (i.e., all variables used in $F$ that do not appear in $I$ or $O$). We will explain how this encoding is generated later, but for now a brief description suffices since we will rely on it when encoding function calls.

Next we describe the encodings of the different commands as they are defined in the [core-LLZK language](CORELLZK.md).

### Assignment

The encoding of an assignment `id = exp` starts by trying to concretely evaluate `exp`, and if all variables used in `exp` have constant values in $T$, the evaluation succeeds and results in a value $v$. We then generate $T'=T[\mathit{id} \mapsto v]$, and the encoding is $(T,\mathit{true},T')$.

If `exp` cannot be concretely evaluated, we symbolically evaluate `exp` using $T$ and a fresh output variable $V_o$ and obtain the encoding $F$. Then we generate $T'=T[\mathit{id} \mapsto V_o]$, and the encoding is $(T,F,T')$.

### Arrays

#### Creating a new array

Creating an array is done using the command `array.new sexp id`.

To symbolically execute this command, we first evaluate `sexp` to a concrete value $n$ that represents the size of the array (the size of an array must be known during symbolic execution). Then we generate a new symbolic array environment $T_{\mathit{id}}$ such that $T_{\mathit{id}}[i]=0$ for all $i\in[0..n]$, and set $T'=T[id\mapsto T_{\mathit{id}}]$. The encoding is then $(T,\mathit{true},T')$.

#### Accessing an array element

Accessing an array element is done using the command `array.read id1[sexp] id2`, which retrieves the value at position `sexp` from array `id1`, and stores it in variable `id2`.

To symbolically execute this command, we first let $T_{\mathit{id}}=T[\mathit{id1}]$, which is the symbolic environment of the array `id1`. Then we handle two cases separately: the first when the index $T[\mathit{id2}]$ is constant, and the other when it is not.

##### The case of a constant index

If $T[\mathit{sexp}]$ evaluates to a constant index $v$, we generate $T^\prime=T[\mathit{id2}\mapsto T\_{\mathit{id1}}[v]]$, and the encoding is then $(T,\mathit{true},T')$.

##### The case of a non-constant index

If the index $T[\mathit{sexp}]$ evaluates to a variable $V_{sexp}$, we have to consider all possible values for the index. We let $n$ be the size of the array, which is supposed to be known during symbolic execution (it is part of the environment $T[\mathit{id1}]$).

Considering all possible values for the index can be done using $G_{n}$ where:

- $G_0 = \mathit{false}$
- $G_i = \mathtt{ite}(V_{sexp}={i-1},V_o=T_{\mathit{id1}}[i-1],G_{i-1})$

where $V_o$ is a fresh variable. Note that this simulates an if-then-else to identify which index was accessed.

Next we generate the output symbolic environment $T'=T[\mathit{id2} \mapsto V_{o}]$, and let the encoding be $(T,G_n,T')$.

#### Updating an array element

Updating an array element is done using the command `array.write sexp1 id[sexp2]`, which updates the value at position `sexp2` to the value of `sexp1`.

To symbolically execute this command, we first let $T_{\mathit{id}}=T[\mathit{id}]$, which is the symbolic environment of the array `id`. Then we handle two cases separately: the first when the index $T[\mathit{sexp2}]$ is constant, and the other when it is not.

##### The case of a constant index

If $T[\mathit{sexp2}]$ evaluates to a constant index $v$, we generate $T^\prime_{\mathit{id}}=T_{\mathit{id}}[v\mapsto T[\mathit{sexp1}]]$, then $T'=T[\mathit{id}\mapsto T_{\mathit{id}}']$, and finally the encoding is $(T,\mathit{true},T')$.

##### The case of a non-constant index

If $T[\mathit{sexp2}]$ evaluates to a variable $V_{\mathit{sexp2}}$, we have to consider all values for the index. We let $n$ be the size of the array, which is supposed to be known during symbolic execution.

We first generate new fresh variables for all positions of the array, to represent the values after the update. Let us name them $V\_{\mathit{id}\_0},\ldots,V\_{\mathit{id}\_{n-1}}$. Let $T^\prime\_{\mathit{id}}$ be a new array environment such that $T^\prime_{\mathit{id}}[i]=V_{\mathit{id}_i}$ for all $i\in[0..n-1]$.

We denote by $U_i$ a formula that simulates an update to the $i$-th position of the array, i.e., assigns $T[\mathit{sexp1}]$ to $V_{\mathit{id}_{i}}$, and the rest of position keep their old values. This can be modeled as follows:

$$V_{\mathit{id}_{i}} = T[\mathit{sexp1}] \land (\bigwedge_{j \neq i \in [0..n-1]} V_{\mathit{id}_{j}}= T_{\mathit{id}}[j]).$$

Then, to consider all possible cases, we can use an if-then-else structure as in the following recursive definition:

- $G_0 = \mathit{false}$
- $G_i = \mathtt{ite}(V_{\mathit{sexp2}}=i-1,U_{i-1},G_{i-1})$

The encoding is then $(T,G_n,T')$.

#### Copying an array

Copying an array from one variable to another is done using the command `array.copy id1 id2`. The encoding simply updates the value of `id2` (in $T$) to that of `id1`. Let $T'=T[\mathit{id2} \mapsto T[\mathit{id1}]]$, then the encoding is $(T,\mathit{true},T')$.

### Conditionals

A conditional statement is of the form `if sexp1==sexp2 { tb } else { te }`, where `tb` and `te` are sequences of commands. The encoding is done by combining the encodings of `tb` and `te`.

Let $(T,F_1,T_1)$ and $(T,F_2,T_2)$ be the encodings of `tb` and `te` respectively. The encoding starts by creating a new environment $T'$ that merges $T_1$ and $T_2$ for the variables that are live immediately after the if-statement (we infer live variables using liveness analysis). For each such live variable $x$: if $T_1[x]$ and $T_2[x]$ agree, then $T'[x]=T_1[x]$; otherwise we introduce a fresh variable $V_x$, add $V_x=T_1[x]$ to $F_1$ and $V_x=T_2[x]$ to $F_2$, and set $T'[x]=V_x$. Assuming that at the end of this process we obtain $T'$, $F_1'$, and $F_2'$, the encoding is $(T, F_1'\vee F_2',\, T')$.

As an important optimization, if the condition `sexp1==sexp2` can be concretely evaluated to $v$, i.e., all used variables have concrete values, then we can use the encoding of `tb` or `eb` depending on $v$.

### Bounded Loops

A bounded loop is of the form `repeat sexp { body }`, and executes `body` for `sexp` iterations. Note that the value of `sexp` must be known statically.

Assume that $T[\mathit{sexp}]=n$, i.e., the loop is executed $n$ times. The encoding of the loop is computed using the following recursive definition of $G_i$, which represents the execution of the loop for $i$ iterations:

- $G_0$ is simply $(T,\mathit{true},T)$ since nothing is executed.
- For $G_i$, we first compute the encoding of `body` starting from $T$, which results in $(T,F,T')$; then we compute $G_{i-1}$ with respect to $T'$, which results in $(T',F',T'')$; and the value of $G_i$ is $(T,F\land F',T'')$.

The encoding of the loop is then defined as the result of $G_n$.

### Function Calls

A function call is of the form `call foo(sexp1, ..., sexpn) to id1,...,idm`, where `sexp1, ..., sexpn` are the input parameters and `id1,...,idm` are the output parameters. Recall that we have assumed that a function is encoded as a macro of the form

  $$\mathtt{foo}(I,O,L) = F$$

where $I$ is a sequence of constraint variables corresponding to the formal input parameters of $\mathtt{foo}$, $O$ is a sequence of constraint variables corresponding to the formal output parameters of $\mathtt{foo}$, and $L$ is a sequence of auxiliary variables (those used in $F$ that are not in $I$ or $O$).

The function call is encoded as call to the above macro according to the following steps:

- We generate the actual input variables $I_{\mathit{call}}$ by concatenating the values of $T[\mathit{sexp1}],\ldots,T[\mathit{sexpn}]$. If any $T[\mathit{sexp}\_i]$ is an array, then all its elements are inserted into $I_{\mathit{call}}$.

- We generate $T'$ from $T$ by inserting a fresh variable for each output variable `idi`. For an output variable that is of array type, it is assigned an array of fresh variables.

- We generate the actual output variables $O_{\mathit{call}}$ by concatenating the values of $T'[\mathit{id1}],\ldots,T'[\mathit{idm}]$. If any $T'[\mathit{id}\_i]$ is an array, then all its elements are inserted into $O_{\mathit{call}}$.

- We generate a sequence of fresh variables $L_{\mathit{call}}$ of the same length as $L$ (these are, in principle, existential variables).

The encoding of the call is then $(T,\mathtt{foo}(I_{\mathit{call}},O_{\mathit{call}},L_{\mathit{call}}),\,T')$. Note that we keep it as a call to a macro, which is important when translating the formulas into SMT2 format to allow modular verification.

## Encoding of functions

A function is of the form

```text
def foo(x1:t, ...,xn:t) -> y1:t, ..., ym:t {
  body
}
```

and as explained earlier, its encoding generates a corresponding macro according to the following steps:

- Generate an initial symbolic environment $T$, where each `xi` is mapped to a fresh variable or an array of fresh variables, depending on its type. Let $I$ be the sequence of constraint variables corresponding to `x1,...,xn`.

- Symbolically execute `body` starting from $T$, which results in $(T,F_1,T')$.

- Generate $T''$ from $T'$ by inserting a fresh variable for each output variable `yi`. For an output variable of array type, it is assigned an array of fresh variables. Let $F_2$ be a conjunction of equalities of the form $T'[\mathit{yi}] = T''[\mathit{yi}]$ (or $\bigwedge_{j=0}^{l-1} T'[\mathit{yi}][j] = T''[\mathit{yi}][j]$ when `yi` is an array of size $l$) for $i\in [1..m]$. Let $O$ be the sequence of constraint variables corresponding to `y1,...,ym` taken from $T''$.

- Let $L$ be the sequence of all variables used in $F_1 \land F_2$ that are not in $I$ or $O$.

The encoding is then:

  $$\mathtt{foo}(I,O,L) = F_1 \land F_2$$

## Encoding of a program

The encoding of a program is done by encoding all its functions, as macros, and adding a top-level formula that simulates a call to the `main` function.

## Implementation

A symbolic execution engine has been implemented in Lean following the ideas described above, and can be found under `translator/lean/llzk/Llzk/SymExec`.

To compile it, first move to the directory `translator/lean/llzk` and run `lake build`. It can then be executed using the following command:

```text
.lake/build/bin/llzk_cli -zk g64 -se -o output.smt2 input.core
```

This generates the SMT2 encoding of `input.core` into `output.smt2`. The `g64` parameter selects the prime `18446744069414584321` with `64` bits. For debugging purposes, it can be replaced by `f11` to use the prime `11` with `4` bits. Omitting the `-o` option prints the result to standard output.

The following command pretty-prints the input program:

```text
.lake/build/bin/llzk_cli -zk g64 -pp -o output.smt2 input.core
```

and is useful for debugging. Full usage information can be obtained with:

```text
.lake/build/bin/llzk_cli --help
```
