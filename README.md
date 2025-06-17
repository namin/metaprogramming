# metaprogramming

Course on Metaprogramming

Originally:
University of Cambridge, UK
Michaelmas Term 2018

Currently being updated for 2025

 ## Highlights

 - [Lecture 1-lisp](lectures/1-lisp) shows a metacircular interpreter that can evaluate itself, and also an extension towards a reflective tower.
 - [Lecture 2-proof-by-reflection](lectures/2-proof-by-reflection) revisits the reflection principle with an example from the seminal FOL to Lean.
 - [Lecture 5-smt](lectures/5-smt) shows how to use SMT as a backend, by presenting a small verifier from IMP to SMT via verification conditions.

## Course Links for Original Edition

- Part II: https://www.cl.cam.ac.uk/teaching/1819/Metaprog/
- MPhil: https://www.cl.cam.ac.uk/teaching/1819/L305/

## Lecture Notes

- [Lecture notes from 2018 are still available.](https://namin.seas.harvard.edu/files/namin/files/metaprogramming-lecture-notes.pdf)
- [A repo with a working draft for the updated lecture notes.](https://github.com/namin/metaprogramming-lecture-notes)

## Solution to Assignment 1

The solution to assignment 1 has been released as part of the [Lisp Variations](https://github.com/namin/lisp-variations) used to create it.

## Installation

### for Scala code

- SBT: https://www.scala-sbt.org/

- In each inner directory, can do
  * `sbt compile`
  * `sbt run` or `sbt test`
