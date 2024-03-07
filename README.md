[![DOI](https://zenodo.org/badge/569066625.svg)](https://zenodo.org/doi/10.5281/zenodo.10794349)

# Artifact Overview

Artifact for paper "A Pure Demand Operational Semantics with Applications
to Program Analysis" ([arXiv](https://arxiv.org/abs/2310.15915)).

Please cite our software as:

```bibtex
  @software{SmithZhangArtifact24,
  author = {Zhang, Robert and Smith, Scott},
  doi = {10.5281/zenodo.10794350},
  month = mar,
  title = {{Software Artifact for A Pure Demand Operational Semantics With Applications to Program Analysis}},
  url = {https://github.com/JHU-PL-Lab/dde/tree/artifact},
  version = {1.0.0},
  year = {2024}
}
```

## Introduction

This artifact facilitates building, testing, and benchmarking the interpreter
(Section 2.2) and program analysis (Section 4.3) presented in the paper. In
addition, it includes a simplified program analysis (`program_analysis/simple`)
that neither derives recurrences nor uses Z3 for path sensitivity and verifying
analysis results. It is meant to help evaluate our semantics against prior
program analyses on a more level playing field, since they also do not have the
aforementioned features. Hereinafter, we refer to the program analysis presented
in the paper as the "full analysis" and the simplified version as the "simple
analysis."

Below is a list of claims made about the full analysis in the paper (Section
5.2.4) and their status with both the full analysis and the simple
analysis.

- Of the 16 expressible DDPA benchmarks,

  (full) 11 terminate very quickly: `blur`, `eta`, `facehugger`, `kcfa-2`,
  `kcfa-3`, `loop2-1`, `mj09`, `map`, `primtest`, `rsa`, `sat-1`

  (simple) 10 terminate very quickly: `blur`, `eta`, `facehugger`, `kcfa-2`,
  `kcfa-3`, `mj09`, `map`, `primtest`, `rsa`, `sat-1`

  (full) one takes ~5s (`sat-3`), one takes ~50s (`sat-2`), and three time out
  after 10 minutes (`ack`, `tak`, `cpstak`).

  (simple) one takes ~5s (`sat-3`), one takes ~10s (`loop2-1`), one takes ~50s
  (`sat-2`), and three time out after 10 minutes (`ack`, `tak`, `cpstak`).

We ran the same set of tests on P4F, so these results also apply to compare
against it.

The full analysis' median runtime is 37.9ms and simple analysis' is 20.5ms.
However, this artifact does not yet claim to outperform related systems, so
their codebases are not included.

To reproduce the benmarks, please refer to the
[instructions](#program-analysis).

## Hardware Dependencies

This artifact is packaged using Docker, so there is no hardware dependency
besides those required to [install
Docker](https://docs.docker.com/engine/install) on your OS. We recommend
interacting with this artifact through the Docker image/container and the code
wherein. If you want to build it from source using the code here, you may need
to obtain a machine with RAM >16GB, to support installing the Z3 package. Please
see the next section for a guide on building from source.

## Getting Started Guide

We recommend interacting with this artifact using Docker. Please follow the
[official instructions](https://docs.docker.com/engine/install) to install
Docker on your machine.

Then, you may retrieve the project's Docker image from Docker Hub:

```sh
docker pull puredemand/puredemand:latest
```

Once retrieved, run the image:

```sh
docker run --rm -it puredemand/puredemand:latest
```

This will enter you into an interactive shell environment where you may run
commands and edit files (using `vim`/`emacs`). Try running `dune build` (already
run for you by Docker) - if it succeeds without errors, then you are good to go!
Once you are done, you may quit the environment with Ctrl+D or type "exit".

If you prefer a modern text editor/IDE, VS Code has a [Remote SSH
extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-ssh)
that allows attaching to a running container. To do so, click on the icon of the
extension at the bottom left of your VS Code window, select "Attach to running
container..." from the dropdown menu, and then choose the "puredemand"
container. Within the container, the root of the project is at `~/pure-demand`.
Note that all of this has to be done before you exit the container session.

Please refer to the [Step by Step Instructions](#step-by-step-instructions)
section for the commands you may run.

### Building from Source

Please first follow the [official instructions](https://ocaml.org/install) to
install and opam and OCaml.

Next, run the following command to install project dependencies:

```sh
opam install \
  core.v0.15.1 \
  core_unix.v0.15.2 \
  core_bench.v0.15.0 \
  dune.3.7.1 \
  menhir.20220210 \
  ounit2.2.2.7 \
  utop.2.11.0 \
  fmt.0.9.0 \
  logs.0.7.0 \
  ppx_let.v0.15.0 \
  ppx_deriving.5.2.1 \
  ppx_jane.v0.15.0 \
  z3.4.12.2-1 && \
  eval $(opam env)
```

Note that `z3` takes a long time and much compute power to install. For this
alone, you may need to obtain a machine with >16GB of RAM, if you do not already
have it.

Follow the [official instructions](https://graphviz.org/download) to install
Graphviz, which gives you the `dot` command to generate visualizations from
the Dot files generated by specifying the `--graph` flag. More details to follow
in the next section.

You are now good to go!

## Step by Step Instructions

This artifact is divided into two components - `interpreter` (Section 2.2) and
`program_analysis` (Section 4.3). Below shows how to run their tests and
benchmarks. All commands should be run in the project root directory (denoted by
`.`).

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
| --debug | Print debug messages to stdout |

For example, you may execute `dune exec -- interpreter/tests/tests.exe
--runtime` to see how long each test take to finish.

### Program Analysis

Base command:

```sh
# Expected runtime: ~2 minutes
dune exec -- program_analysis/tests/tests.exe
```

There are several flags you can optionally specify, as listed below.

| Flag | Description |
| - | - | 
| --runtime | Print the runtime (processor time) of each test to stdout |
| --no-cache | Disable caching in the analysis |
| --verify | Enable verification of final analysis result using Z3 |
| --bench | Run benchmarks. More accurate than --runtime. |
| --graph | Generate Graphviz source code visualizing the final analysis result, `./graph_name.dot` (`./graph_test.dot` by default) |
| --log | Log debug messages to a file, `./logs` |
| -log PATH | Log debug messages to a custom file at PATH |

For example, you may execute `dune exec -- program_analysis/tests/tests.exe
--runtime --no-cache` to see how long each test take to finish when caching is
off.

To run the benchmarks, only specify the `--bench` flag and observe the runtimes
in the second column of the resulting graph (Time/Run, in microseconds). It
takes 4-5 minutes to finish benchmarking and 2-3 minutes subsequently to run the
unit tests.

```sh
# Expected runtime: 6-8 minutes
dune exec -- program_analysis/tests/tests.exe --bench
```

For both the simple and full analysis, there are a few long-running benchmarks
that do not terminate quickly. For this reason, they are separate from the other
benchmarks and are by default commented out in `program_analysis/tests/tests.ml`
(see comments). Running them times out after 10 minutes.

To generate graphs, after you ran the tests with `--graph`, you should run an
additional command to actually generate an image of the graph from the Dot
source code produced:

```sh
dot -Tpng ./graph_name.dot > graph_name.png
```

To view the image, we recommend first attaching the running Docker container to
an IDE like VS Code. See relevant instruction in [Getting Started
Guide](#getting-started-guide).

For both the interpreter and the program analyses, you may also run ad-hoc
programs through OCaml's REPL - `utop`:

```sh
# Enter REPL with subproject modules loaded...
dune utop program_analysis/full
# ... or
dune utop program_analysis/simple
# ... or
dune utop interpreter

# In the REPL, open relevant modules for better access to utilities...
open Pa;;
# ... or
open Simple_pa;;
# ... or
open Interp;;

# You may optionally set environment variables corresponding to
# the commandline flags of tests, e.g.,
caching := false;
# To simplify interpreter results:
simplify := true;

# Then, execute programs...
pau "let a = 1 in a" # for both analyses
# ... or
peu "let a = 1 in a" # for the interpreter
```

Below is a table listing the environment variables you may set in the REPL for
each system:

| System | Environment Variables (default values) |
| - | - | 
| Interpreter | `report_runtime` (false), `caching` (true), `debug` (false), `simplify` (false) |
| Full analysis | `report_runtime` (false), `caching` (true), `verify` (false), `graph` (false) |
| Simple analysis | `report_runtime` (false), `caching` (true) |

You may profile both analyses by setting the environment variable
`OCAML_LANDMARKS` when running the tests:

```sh
OCAML_LANDMARKS=on dune exec -- program_analysis/tests/tests.exe
```

This will generate a hierarchy of functions called, which are ranked by the
total time taken to execute each.  You may find that in a lot of cases, CHC
solving (`Lib.solve_cond`) takes up a significant portion, if not most, of the
runtime.

## Reusability Guide

Both the interpreter and the analyses are core components of this project and
can be evaluated for reusability. An exception is the `--graph` flag, which was
only used to generate visualizations for the paper. The graphs generated from
the results of the `id` and `map` programs, which are presented in the paper,
are re-generated and placed in the `./graphs` folder for easy access
(the only different being `graph_id.png` additionally visualizes the
`letassert`). You are of course welcome to generate them yourself.

Below are instructions on adding new test inputs.

### Interpreter

To add new tests, follow the instructions in `./interpreter/tests/tests.ml` to
modify `test_custom` to define and run inline tests.

### Program Analysis

Again, follow the instructions in `./program_analysis/tests/tests.ml`. But now,
there are two options: (1) create a new test case in
`./program_analysis/tests/cases` and (2) write the test as an inline string.

For (1), after you have created the test case, modify the boilerplate
`custom_thunked` or `custom_benchmarkable_thunked` in
`./program_analysis/tests/tests.ml` to read in your file and run it. For (2),
replace `read_input "your_test.ml"` with a string of your program.

To add custom benchmarkable tests, follow the comments and modify
`custom_benchmarkable_thunked`, etc.

Note that to properly leverage the `--verify` flag, you have to wrap your
program in `letassert x = ... in x >= 0` where `x >= 0` can be any binary/unary
operation involving `x`. See the comment on `eval_assert` in
`./program_analysis/full/lib.ml` for details.

You may find comments and log messages throughout the source code to help you
understand and reuse the various components.

## Language Guide

The syntax of our language used across the interpreter and the program analyses
mostly follows OCaml's with a few differences:

- Curried functions cannot be inlined via the shorthand `fun a b c -> ...` and
  instead have to be laid out in full via `fun a -> fun b -> fun c -> ...`.

- Recursive functions have to be defined in the self-passing style, e.g., `(fun
  self -> fun x -> ...) (fun self -> fun x -> ...) 0`.

- Records can be defined immediately without an established type, and inspecting
  a record field can be done via the `in` keyword, e.g., `l in { l = 1 }`.

- Due to the `in` keyword being reused for both record inspections and let
  bindings, you must insert parentheses around let definitions that end in a
  variable, in order to disambiguate from record inspections, e.g., `let a =
  (fun x -> x) in a`.

- The added `letassert` expression takes the form `letassert x = e in assn`
  where e is an expression and `assn` is written in an assertion syntax
  described in Appendix B Section B.2 of the paper and at the
  [`eval_assert`](./program_analysis/full/lib.ml#82) function.
