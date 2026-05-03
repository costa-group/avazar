# The Clustering Tool

This document explains the `clustering` command-line tool, what it does, and the arguments it accepts.

## What the tool does

The `clustering` binary reads an input circuit file (`.r1cs`), runs decomposition/clustering logic, and writes a JSON output file with the clustered structure.

## Output JSON format

The output has three main parts:

- `timing`: performance metrics for each processing stage.
- `nodes`: the circuit decomposed into DAG nodes (subcircuits).
- `equivalency_local` and `equivalency_structural`: optional partitions of node IDs into equivalence classes.

Think of `nodes` as "what the decomposition produced" and `equivalency` fields as "which produced nodes are considered similar under a specific notion of similarity".

### 1) `timing`

`timing` reports duration (in seconds) for each high-level stage:


### 2) `nodes`

`nodes` is the core structural output. Each entry represents one DAG node (a grouped subcircuit).

Node fields:

- `node_id` (`usize`): Identifier for the node inside this output.
- `constraints` (`usize[]`): IDs of original constraints contained in this node.


- `input_signals` (`usize[]`): Signal IDs consumed by the node from outside that node.

- `output_signals` (`usize[]`): Signal IDs produced by the node for downstream use.

- `signals` (`usize[]`): Signal IDs associated with the node (internal and boundary).

- `is_custom` (`bool`): Marker for custom/special node type in the decomposition pipeline.

- `successors` (`usize[]`): IDs of nodes that depend on this node's outputs.

- `predecessors` (`usize[]`): IDs of nodes this node's inputs depends on.




### 3) Equivalence fields and notions

Both equivalence fields encode a partition of node IDs into classes.

- Data shape: `Vec<Vec<usize>>`
- Each inner vector is one equivalence class.
- Node IDs inside one class are equivalent under that mode's criterion.

Example:

- `[[0, 4], [1], [2, 3]]` means:
  - Nodes `0` and `4` are equivalent.
  - Node `1` has no partner (singleton class).
  - Nodes `2` and `3` are equivalent.

#### Local equivalence (`equivalency_local`)

Subcircuits in the same equivalence class are equivalent up to renaming, scaling, shuffling.

#### Structural equivalence (`equivalency_structural`)

Subcircuits in the same equivalence class are locally equivalent as previous, and there exists an automorphism of the circuit hierarchy that preserves local equivalence and maps one to the other.


## Basic usage

```bash
clustering [OPTIONS] <FILEPATH>
```

An example of use case is:
```bash
./clustering file_name.r1cs -e total -x 50 -o .
```

## Arguments and options

### Required argument

- `FILEPATH`
  - Type: `String`
  - Description: input circuit file path.

### Optional flags

- `-o <OUT_DIRECTORY>`
  - Type: `String`
  - Default: `.`
  - Description: output directory where the resulting JSON file is written.

- `-x, --target-size <TARGET_SIZE>`
  - Type: `f64`
  - Description: target cluster size for modularity-based clustering.

- `-e, --equivalence <EQUIVALENCE_MODE>`
  - Type: enum
  - Default: `structural`
  - Accepted values:
    - `total`: to compute both structural and local equivalence.
    - `structural`: to compute structural equivalence.
    - `local`: to compute local equivalence
    - `none`: to diactivate the computation of any kind of equivalence.


### Built-in Clap flags

- `-h, --help`: print help.
- `-V, --version`: print version.


