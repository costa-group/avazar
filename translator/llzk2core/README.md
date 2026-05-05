# LLZK to CORE Translator

It contains a translator that goes from [**LLZK**](https://project-llzk.github.io/llzk-lib/main/), an intermediate representation for Zero-Knowledge circuit languages, to [**CORE LLZK**](https://costa-group.github.io/avazar/#core-llzk-specification) representation.

## Overview

The translator operates as a modular pipeline that processes multiple dialects (inspired by MLIR). It handles everything from basic field arithmetic and data structures to high-level structured control flow (loops, conditionals) and polymorphic templates for ZK circuits.

## Project Architecture

The codebase is organized into modular components that separate parsing logic, dialect definitions, and core transformation utilities:

* **`llzk2core.py`**: The main entry point. It handles CLI arguments and starts the translation process via the `execution` module.
* **`llzk_dialects/`**: The core of the translator, containing implementations for LLZK dialects (SCF, Struct, Arith, Function, etc.). Each dialect is repretented in a separated script using the same name:
    * `parser.py`: Implements the `LLZKParser`. It performs top-level dispatching by identifying dialect prefixes and delegating parsing to specific operation classes.
    * `definitions.py`: Contains the base `Dialect` class, providing the registry and dispatch mechanism for all operations.
    * `core.py`: Defines fundamental IR entities like `SSAVar` (SSA variables) and the base `Operation` and `BlockOperation` classes.

| Dialect   | Prefix   | Key Files     | Responsibility                                         |
|-----------|----------|--------------|--------------------------------------------------------|
| LLZK      | llzk.    | llzk.py      | Core IR constructs and ZK-specific attributes.         |
| Arith     | arith.   | arith.py     | Standard integer arithmetic (MLIR style).              |
| Cast      | cast.    | cast.py      | Type conversions between field elements and indices.   |
| Constrain | constrain.| constrain.py | Semantic circuit constraint emission.                  | 
| Function  | function.| function.py  | Function lifecyclemanagement (definitions and calls).            | 
| Global    | global.  | global.py   | Management of module-level global variables.           | 
| Include   | include. | include.py   | External file and module inclusion.                    |
| SCF       | scf.     | scf.py       | Structured Control Flow (Loops/Conditionals).          |
| Struct    | struct.  | struct.py    | ZK circuit component definitions.                      | 
| String    | string.  | string.py    | Literal string constants management.                   | 
| POD       | pod.     | pod.py       | Plain-Old-Data structures (no constraints).            | 
| Poly      | poly.    | poly.py      | Polymorphic and templated circuit logic.               |
| Felt      | felt.    | felt.py      | Finite Field arithmetic operations.                    |
| Bool      | bool.    | bool.py      | Boolean logic and comparison operations.                |
| Array     | array.   | array.py     | N-dimensional array creation and access operations.    | 


## Requirements

* **Python 3.8+**
* **No external dependencies:** This project only uses the Python Standard Library (e.g.: `re`, `abc`, `typing`, `argparse`).

## Usage

To translate an LLZK IR file to CORE language, run:

```bash
python3 src/llzk2core.py -s SOURCE_FILE [-o TARGET_FILE]
```
where:
* SOURCE_FILE: The path to the .llzk source file you want to translate.
* TARGET_FILE: The name of the output file. If not specified, the output is stored in SOURCE_FILE.core.
