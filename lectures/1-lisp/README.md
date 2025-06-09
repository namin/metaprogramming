# Scheme

This lecture uses [Chez Scheme](https://cisco.github.io/ChezScheme/).

You can experiment with the evaluator in a `scheme` session, by:
- running `scheme` interactively
- `(load "evl.scm")`
- `(repl 0)`
- Try `1`.
- Try `(lambda (x) x)`.
- Try the examples in `exs.scm`.
- Now you can copy paste the entire `evl.scm` file, and run another level of `(repl 1)`.
- With each level, the interpretive overlead increases.

## Example session

```
Chez Scheme Version 10.1.0
Copyright 1984-2024 Cisco Systems, Inc.

> (load "evl.scm")
> (repl 0)

0-0> (load "exs.scm")
..
;==> undefined
;(1 cpu-time)

0-1> (fact 6)
;==> 720
;(0 cpu-time)

0-2> (load "evl.scm")
..............
;==> undefined
;(1 cpu-time)

0-3> (repl 1)

1-0> (load "exs.scm")
..
;==> undefined
;(2 cpu-time)

1-1> (fact 6)
;==> 720
;(1 cpu-time)

1-2> (load "evl.scm")
..............
;==> undefined
;(0 cpu-time)

1-3> (repl 2)

2-0> (load "exs.scm")
..
;==> undefined
;(66 cpu-time)

2-1> (fact 6)
;==> 720
;(62 cpu-time)

2-2> (load "evl.scm")
..............
;==> undefined
;(42 cpu-time)

2-3> (repl 3)

3-0> (load "exs.scm")
..
;==> undefined
;(6395 cpu-time)

3-1> (fact 6)
;==> 720
;(5418 cpu-time)
```
