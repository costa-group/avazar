# llzk

## Build

```text
lake build
```

## Usage

To run the symbolic execution use the following command:

```text
.lake/build/bin/llzk_cli -zk g64 -se -o output.smt2 input.core
```

This generates the SMT2 encoding of `input.core` into `output.smt2`. The `g64` parameter selects the prime `18446744069414584321` with `64` bits. For debugging purposes, it can be replaced by `f11` to use the prime `11` with `4` bits. Omitting the `-o` option prints the result to standard output.

For parsing and pretty-prints the input program, use the following:

```text
.lake/build/bin/llzk_cli -zk g64 -pp -o output.smt2 input.core
```

Full usage information can be obtained with:

```text
.lake/build/bin/llzk_cli --help
```
