# A functional and "correct" regular expression matcher

## Dependencies

- You need to locally publish the `lms-verify` dependency:
  - `git clone https://github.com/namin/lms-verify`
  - `cd lms-verify`
  - `sbt publishLocal`

## How to run

`sbt test`

You can also start `sbt` interactively (with no arguments), and then
run only selected tests: `testOnly ex.*` or `testOnly
ex.StagedRegexpTests`. By adding a tilde, as in `~testOnly ex.*`,
these tests will be run interactively every time your project changes.

The generated code should verify with Frama-C. See how to run here:
- https://github.com/namin/lms-verify#c-verification

## Background

The interpreter code is based on
- Robert Harper, _Proof-Directed Debugging_, JFP Functional Pearl 1993.

Here, we will cheat a bit on correctness by generating the spec at the
same time as the code! This is achieved by passing `spec=true` to the
`toplevel` call, using [LMS-Verify](https://github.com/namin/lms-verify).

Warning: the generated code is sub-optimal (with traces of recursive
calls) and not optimized (as would be an automata). For variants on this theme, see also
- https://github.com/namin/lms-verify#functionally-correct-optimized-regular-expression-matcher
- Kwangkeun Yi, _'Proof-directed debugging' revisited for a first-order version_, JFP Educational Pearl, 2005.

## The task

Re-create the implementation in `StagedRegexp`. A good way to
get started is to copy the unstaged implementation in `regexp` and
change the code appropriately starting with the types. Use
`Rep[Input]` instead of `String`, as it is more tailored to C code
generation. You should only need the operations defined in [`lms.verify.Reader`](https://github.com/namin/lms-verify/blob/master/src/main/scala/lms/verify/Reader.scala#L22).

For the `Star` case, there is an issue of recursion, that will cause
stack overflows. Use memoization with the `val table` already
initialized. Rely on `toplevel` (see how it is called in
`StagedRegexpTests`).

Open question: How would you go further in optimizing or verifying the
generated code?
