# AVAZAR Project
The AVAZAR (Automated Verification Tools for zkEVM Arithmetization) project aims at developing a suite of general-purpose tools for proving semantic equivalence of the arithmetization of a ZKVM, the input/output relation given by the witness computation code and the constraint system is the same. Our approach will rely on:

- Certified transformations from the witness computation code (in LLZK) to SMT formulas.
- Clustering techniques to improve scalability.
- SMT solvers capable of reasoning about polynomial equations over finite fields.

All this integrated in a general open source automated tool called AVAZAR.

## SMT solver submodule link
https://mygitlab.cs.upc.edu/polynomial-equations/poly-eqs.git

## Documentation
https://costa-group.github.io/avazar/


## Installation Guide

### 1. Clone the Repository
Start by cloning the repository along with all of its required submodules:

```bash
git clone --recurse-submodules --remote-submodules [https://github.com/costa-group/avazar.git](https://github.com/costa-group/avazar.git) avazar
```

### 2. Install Core AVAZAR Tools
The AVAZAR project is built on top of several tools developed by the AVAZAR Project team (avazar_tool, ffsol, and circom). You can install them automatically by executing the following script from the root directory:

```
bash
./install.sh
```

### 3. Install LLZK Dependencies
In order to generate the LLZK IR of a given Circom circuit, AVAZAR uses the [Circom frontend](https://github.com/project-llzk/circom) of the LLZK Project, which depends on [llzk-lib](https://github.com/project-llzk/llzk-lib). This requires a two-step installation:

#### 3.1. Install llzk-lib
Go to the llzk-lib root directory.

Follow the steps available in the llzk-lib [Setup Documentation](https://project-llzk.github.io/llzk-lib/main/setup.html).

#### 3.2 Install LLZK Circom Frontend
Go to the circom-llzk directory.

Follow the steps described in the [LLZK Circom GitHub Repository](https://github.com/project-llzk/circom#install).


## Usage

### avazar.py — Main Entry Point

`avazar.py` is the top-level script that automates the full AVAZAR verification pipeline. Given a Circom circuit, it runs all internal steps in sequence: R1CS generation, LLZK IR generation, IR translation to core format, and SMT-based verification.

```bash
python3 avazar.py -s <circuit.circom> [-out <output_dir>] [-solver <solver>]
```

#### Arguments

| Argument | Required | Default | Description |
|----------|----------|---------|-------------|
| `-s`, `--source` | Yes | — | Path to the input Circom circuit file (`.circom`) |
| `-out` | No | `/tmp/avazar_output/` | Directory where all intermediate and output files are written |
| `-solver` | No | `ffsol` | SMT solver to use for verification (see solvers below) |

<!-- #### Available Solvers -->

<!-- | Solver | Description | -->
<!-- |--------|-------------| -->
<!-- | `ffsol` | Default. Finite-field solver developed by the AVAZAR team | -->
<!-- | `civer` | Built-in constraint verifier (default for the low-level `avazar` binary) | -->
<!-- | `z3` | Z3 SMT solver | -->
<!-- | `niaz3` / `nia-z3` | Z3 in nonlinear integer arithmetic mode | -->
<!-- | `cvc5` | CVC5 SMT solver | -->
<!-- | `yices` | Yices SMT solver | -->
<!-- | `picus` | Picus solver | -->
<!-- | `all` | Run all available solvers in parallel | -->

<!-- > **Note:** Solvers other than `ffsol` and `civer` must be installed and available in `PATH`. -->

#### Example

```bash
# Basic usage with default solver
python3 avazar.py -s examples/semantic_equivalence/circomlib/iszero/iszero.circom

# Specify output directory and solver
python3 avazar.py -s examples/semantic_equivalence/circomlib/iszero/iszero.circom -out results/ -solver ffsol

```
