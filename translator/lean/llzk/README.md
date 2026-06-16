# Modeling the big-step semantics of LLZK program into SMT2 formulas

This part of the project focuses on translating LLZK programs into SMT2 formulas that capture their input-output behavior. The translator is implemented in Lean and is accompanied by formal proofs establishing the equivalence between the SMT2 formulas and the big-step semantics.

The translator does not work directly on LLZK, but rather on a language that is expressive enough to model LLZK programs and simple enough to facilitate proofs in Lean. We introduce this intermediate language — called **core-LLZK** — to provide stability, so that changes to LLZK do not cascade into changes in the formal statements.

## Requirements

Install `elan` (The Lean toolchain manager) using:

```text
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Build

```text
lake build
```

## Usage

To generate the SMT2 formula of a given program use:

```text
.lake/build/bin/llzk_cli -zk g64 -se -o output.smt2 input.core
```

This generates the SMT2 encoding of `input.core` into `output.smt2`. The `g64` parameter selects the prime `18446744069414584321` with `64` bits. For debugging purposes, it can be replaced by `f11` to use the prime `11` with `4` bits. Omitting the `-o` option prints the result to standard output.

For parsing and pretty-prints the input program, use:

```text
.lake/build/bin/llzk_cli -zk g64 -pp -o output.smt2 input.core
```

Full usage information can be obtained using:

```text
.lake/build/bin/llzk_cli --help
```
