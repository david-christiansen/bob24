# Lean for the General Programmer

This is the accompanying code for "Lean for the General Programmer", a
tutorial presented at BobKonf on 2024-03-15 in Berlin by Joachim
Breitner and David Thrane Christiansen.

## Overview

This tutorial is aimed at introducing Lean to functional programmers
who have no background in formal verification. We'll do this in two
stages:
 1. Basics of Lean - this quick overview will demonstrate how pattern
    matching, recursion, datatypes, and other common features of
    functional languages look in Lean's syntax, as well as how to
    interact with Lean
 2. Two verified implementations of a JSON filter
 
The JSON filter is a command-line tool that applies a query to a
sequence of JSON values read from standard input, writing those that
satisfy the query to standard output. As is common in high-assurance
systems, we'll be verifying the core algorithm, but not the user
interface. We'll start by verifying a version that works on linked
lists, and then proceed to one that uses packed arrays.

We won't have time to explain everything in complete detail, but we
hope that the overview we provide is a good starting point for
learning to use Lean. Please see [the documentation
section](https://lean-lang.org/documentation/) of the Lean website for
further resources.

## Repository Structure

This repository is an ordinary Lean project. To get started, first
[install Lean](https://lean-lang.org/lean4/doc/quickstart.html). Then,
open the repository in a terminal and run
```
$ lake build
```
to compile it, or
```
$ lake exe bob
```
to run the executable.

### Branches

The repository contains the following branches, each a refinement of the prior one:

 - `main`: the initial state of the example code, in which the tests do
   not yet pass and the proofs are not yet written.
 - `step1`: the code after writing the initial example programs, but
   before doing any verification. The program can be run at this
   stage, though it's using linked lists where an array would be more
   appropriate.
 - `step2`: the implementation used in `step1` is proven correct
 - `step3`: the implementation is replace with one that uses packed
   arrays instead of linked lists
 - `step4`: the array implementation is proven correct

### Code Structure

 - `Main.lean` contains the executable
 - `Bob.lean` is a library wrapper that imports (and thus implicitly re-exports) the modules:
   - `Bob/Intro.lean` - the introduction to programming in Lean
   - `Bob/List.lean` - the implementation using linked lists
   - `Bob/Array.lean` - the implementation using packed arrays
   - `Bob/Query.lean` - the query language, including its JSON syntax
     and matching queries against values (not a part of the tutorial
     _per se_, but it might be fun to read)

## Running the Tests

When the program seems to work, it can be tested using `run.sh` in the
`tests` directory. Please see [tests/README.md](tests/README.md) for
more information.
