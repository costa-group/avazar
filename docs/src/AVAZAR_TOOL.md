# avazar Tool

This document explains the `avazar` command-line tool, what it does, and the arguments it accepts.

## What the tool does

`avazar` is a general modular verifier for ZK circuits. It reads an R1CS constraint system, optionally a pre-computed decomposition structure, and verifies the circuit node by node using an SMT solver according to the selected mode. It reports which nodes are verified, failed, or unknown.

## Basic usage

```bash
avazar [OPTIONS] <INPUT>
```

An example:
```bash
avazar ./circuit.r1cs --solver civer --equivalence structural --clustering_size 200
```

## Modes

The tool has three operating modes:

- `determinism` (default)
  - If no mode flag is provided, the tool runs in determinism mode by default. It checks if the inputs are fixed, the outputs are unique. 

- `--check_correctness <correctness.json>` 
  - Activates correctness-checking mode.  
  - Verifies whether the input R1CS file is consistent with the given SMT-LIB (`.smt2`) formula. The `correctness.json` file must contain several fields:  
    - `input_signals` and `output_signals`, two lists of signals which must match the input/output structure of the R1CS file.  
    - `signals`, listing the auxiliar variables that appear in the SMT formula.  
    - `constraints`, specifying the SMT formula to be checked.

- `--check_equivalence <another_file.r1cs>`
    - Activates equivalence check mode.
    - Checks equivalence between the input and the given R1CS files. Both files must have the same input/output structure. Otherwise, they cannot be equivalent.


## Arguments and options

### Required argument

- `INPUT`
  - Type: path (`String`)
  - Default: `./circuit.circom`
  - Description: path to the R1CS constraint system to be verified.

### Optional flags

- `--input_structure <PATH>`
  - Type: path
  - Description: path to a pre-computed decomposition structure JSON (as produced by the `clustering` tool). If not given, avazar clusters the circuit internally using `--clustering_size`.

- `--original_structure <PATH>`
  - Type: path
  - Description: original structural metadata of the circuit (E.g., in circom, template-level component info). Used to produce more meaningful error messages. Optional.

- `--timeout <MILLISECONDS>`
  - Type: `u64`
  - Default: `5000`
  - Description: timeout in milliseconds for each call to the underlying solver.

- `--solver <SOLVER>`
  - Type: string
  - Default: `civer`
  - Accepted values: `civer`, `ffsol`, `cvc5`, `z3`
  - Description: 

- `--equivalence <MODE>`
  - Type: string
  - Default: `structural`
  - Accepted values: `none`, `local`, `structural`
  - See [Equivalence modes](#equivalence-modes) below.

- `-p, --prime <N>`
  - Type: `BigInt`
  - Default: `21888242871839275222246405745257275088548364400416034343698204186575808495617` (BN254 scalar field prime)
  - Description: prime field modulus used during verification.

- `-c, --clustering_size <N>`
  - Type: `usize`
  - Default: `200`
  - Description: maximum size of nodes considered for internal re-clustering. Nodes larger than this threshold are split further. Set to `0` to disable internal clustering entirely.

- `-t, --target_size <N>`
  - Type: `usize`
  - Default: `0`
  - Description: target size for nodes in the internal clustering. Set to `0` to disable (default). Takes effect only when `--input_structure` is not provided.

## Equivalence modes

avazar avoids redundant solver calls by exploiting equivalence between DAG nodes:

- **`none`**: every node is sent to the solver independently, regardless of similarity.

- **`local`**: nodes grouped by local equivalence (same local fingerprint/signature) share a result. If one representative in the class is verified, the others are assumed verified too.

- **`structural`**: like `local`, but uses stricter structural equivalence that also accounts for the node's context in the DAG. Two nodes must agree in both content and structural position to be grouped. Consequently, two nodes can be local equivalent, but no structural equivalent.

The equivalence classes come either from the optional `--input_structure` file or are computed internally if that file is not provided.



