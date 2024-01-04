# Artifact Overview

Artifact for paper #150, A Pure Demand Operational Semantics with Applications
to Program Analysis.

## Introduction

This artifact facilitates building, testing, and benchmarking the interpreter
and program analysis presented in the paper. In addition, it includes a
simplified version of the program analysis that does not use Z3 for path
sensitivity and deriving recurrences.

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

In fact, if you prefer a modern text editor/IDE, VS Code has a [Remote SSH
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
| --runtime | Print the runtime of each test to stdout |
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
| --runtime | Print the runtime of each test to stdout |
| --no-cache | Disable caching in the analysis |
| --verify | Enable verification of final analysis result using Z3 |
| --graph | Generate Graphviz source code visualizing the final analysis result, `./graph.dot`. |
| --bench | Run benchmarks, which takes a while. Observe the second column "time/run" for the benchmark of each test |

For example, you may execute `dune exec -- program_analysis/tests/tests.exe
--runtime --no-cache` to see how long tests take to finish when caching is off.

To add new tests, there are two options: (1) create a new test case under
`./program_analysis/tests/cases` and (2) write the test as an inline string.

For (1), after you have created the test case, modify the boilerplate
`custom_thunked` in `./program_analysis/tests/tests.ml` to read in your file and
run it. For (2), replace `read_input "your_test.ml"` with a string of your
program.

## Reusability Guide
