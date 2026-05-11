# ffsol Tool

This document explains the usage of the SMT solver `ffsol`, specialized in finite field arithmetic.

## What the tool does

`ffsol` is a solver designed to process formulas in the SMT-LIB2 (`.smt2`) format over finite fields. It checks whether a formula is satisfiable (`sat`), unsatisfiable (`unsat`), or if the result is unknown (`unknown`). Additionally, it allows precise configuration of which optimization and deduction subroutines are activated during the solving process. We have adopted the same SMT-LIB2 format for finite fields presented [here](https://cvc5.github.io/docs/cvc5-1.3.2/theories/finite_field.html).

## Installation
The repository of `ffsol` can be downloaded from [here](https://mygitlab.cs.upc.edu/polynomial-equations/poly-eqs.git). It provides an installation script, `install.sh`, which automatically installs all the required libraries and dependencies needed to compile and run the solver.

## Basic usage

```bash
./ffsol -file <FILE_SMT2>
```

## Usage Examples

### Basic invocation
```bash
./ffsol -file file.smt2
```

### With time limit
```bash
./ffsol -file file.smt2 -tlimit 20
```
Time limit is 20 seconds; default is no limit.

### Writing model to file
```bash
./ffsol -file file.smt2 -model fileName
```
Model will be written to file `fileName`; default is model is not written.
