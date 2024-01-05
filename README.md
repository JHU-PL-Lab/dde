# Artifact Overview

Artifact for paper #150, A Pure Demand Operational Semantics with Applications
to Program Analysis.

## Introduction

This artifact facilitates building, testing, and benchmarking the interpreter
and program analysis presented in the paper. In addition, it includes a
simplified version of the program analysis (`program_analysis/simple`) that is
less precise and does not use Z3 for path sensitivity and deriving recurrences.

TODO: list claims

## Hardware Dependencies

This artifact is packaged using Docker, so there is no hardware dependency
besides those required to [install
Docker](https://docs.docker.com/engine/install) on your OS.

## Getting Started Guide

Please follow the [official
instructions](https://docs.docker.com/engine/install) to install Docker on your
machine.

Then, you may retrieve the project's Docker image from Docker Hub:

```sh
docker pull pure-demand
```

Once retrieved, run the image:

```sh
docker run --rm -it pure-demand
```

This will enter into an interactive shell environment where you may run commands
and edit files (using `vim`/`emacs`). Once you are done, you may quit the
environment with Ctrl+D or type "exit".

If you prefer a modern text editor/IDE, VS Code has a [Remote SSH
extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-ssh)
that allows attaching to a running container. To do so, click on the icon of the
extension at the bottom left of your VS Code window, select "Attach to running
container..." from the dropdown menu, and then choose the "pure-demand"
container. Note that all of this has to be done before you exit the container
session.

## Step by Step Instructions

This artifact is divided into two components - `interpreter` (Section 2.2 in
paper) and `program_analysis` (Section 4.3). Below shows how to run their tests
and benchmarks. All commands should be run in the project root directory
(denoted by `.`).

### Interpreter

Base command:

```sh
dune exec -- interpreter/tests/tests.exe
```

There are several flags you can optionally specify, as listed below.

| Flag | Description |
| - | - | 
| --runtime | Print the runtime (processor time) of each test to stdout |
| --no-cache | Disable caching in the analysis |

For example, you may execute `dune exec -- interpreter/tests/tests.exe --runtime` to see how long tests take to finish.

### Program Analysis

Base command:

```sh
dune exec -- program_analysis/tests/tests.exe
```

There are several flags you can optionally specify, as listed below.

| Flag | Description |
| - | - | 
| --log | Log debug messages to a file, `./logs` |
| -log PATH | Log debug messages to a custom file at PATH |
| --runtime | Print the runtime (processor time) of each test to stdout |
| --no-cache | Disable caching in the analysis |
| --verify | Enable verification of final analysis result using Z3 |
| --bench | Run benchmarks, which takes ~4 mins. More accurate than --runtime. |
| --graph | Generate Graphviz source code visualizing the final analysis result, `./graph.dot`. |

For example, you may execute `dune exec -- program_analysis/tests/tests.exe
--runtime --no-cache` to see how long tests take to finish when caching is off.

To run the benchmarks, only specify the `--bench` flag and observe the runtimes
in the second column (Time/Run, in microseconds) of the resulting graph:

```sh
dune exec -- program_analysis/tests/tests.exe --bench
```

The simple system is devised in order to reduce the overhead incurred by Z3. For
each of the simple and full version, there a few long-running tests from DDPA
that do not terminate quickly. For this reason, they are separate from the other
benchmarks and are commented out right now ("DDPA long-running tests (full)" and
"DDPA long-running tests (simple)" in `program_analysis/tests/tests.ml`).
Running them will time out after 5 minutes.

## Reusability Guide

TODO

### Program Analysis

To add new tests, there are two options: (1) create a new test case under
`./program_analysis/tests/cases` and (2) write the test as an inline string.

For (1), after you have created the test case, modify the boilerplate
`custom_thunked` in `./program_analysis/tests/tests.ml` to read in your file and
run it. For (2), replace `read_input "your_test.ml"` with a string of your
program.

## Miscellaneous

Due to the our language supporting both record inspection (`l in { l = 1 }`) and
let binding (`let a = 1 in a`), you must insert parentheses around let
definitions ending in a variable, to disambiguate from record inspections. E.g.,
`let a = (fun x -> x) in a`.
