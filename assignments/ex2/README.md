# A pixel-by-pixel image processing DSL

## Dependencies

- You need to locally publish the `lms-verify` dependency:
  - `git clone https://github.com/namin/lms-verify`
  - `cd lms-verify`
  - `sbt publishLocal`
- Warning: this should be done OUTSIDE the `ex2` project.

## Windows Users (by Al Taylor)
It appears that several of the tools used by LMS don't work on Windows.
To run the unix tools correctly (on Windows 10)
- Install the Ubuntu subsystem on Windows: https://docs.microsoft.com/en-us/windows/wsl/install-win10
- Open ubuntu shell (windows key + then type ubuntu)
- create the user account etc
- set the ubuntu home directory to be your windows home directory (/mnt/c/Users/$name) https://superuser.com/questions/1132626/changing-home-directory-of-user-on-windows-subsystem-for-linux
- install sbt on ubuntu: https://www.scala-sbt.org/1.0/docs/Installing-sbt-on-Linux.html

- to test your version of sbt: clone https://github.com/scala-lms/tutorials (from windows, to your normal dev directory) and try running `sbt test` from the tutorials directory in linux. You may need to install more dependencies, like gcc.
- Note: you won't be able fully run the interpreted test in the first exercise, as `open out$n.jpg` will fail, but you can still view the output images in windows.

## How to run

- `sbt run` to run an interpreter or compiler (pick a main by number).
- Interactively, run `sbt`, then `~runMain imgdsl.ImageDslCompTestApp`.

## How to run/verify the generated C code

- Once you make it work, the image DSL compiler will generate the files `img1.c` to `img6.c`.
- `pgma_io_install.sh` to install [the C library](https://people.sc.fsu.edu/~jburkardt/c_src/pgma_io/pgma_io.html) to read/write PGM files.
- To create a main for a generated C processor, then compile and run it:
  - `run.sh img[1-6].c` on Mac OS X
  - `run-linux.sh img[1-6].c` on Linux
- Optionally, `verify.sh img[1-6].c` to run [Frama-C](http://frama-c.com/) on a generated C processor for verification. Note that this script might need to be adjusted depending on your installation. See the [README.md of LMS-verify](https://github.com/namin/lms-verify) for guidance and workaround in installing and running Frama-C.

## Background

The `imgdsl.scala` is ported from
- Oleg Kiselyov's _"A DSL for image manipulation"_,
  part of [his meta-programming tutorial](http://okmij.org/ftp/meta-programming/tutorial/)

With LMS-verify, we leave out the image reading / and writing to the
"main" method, and generate a processing unit that take the in-place
image. See `img.test.c` for an example main routine.

The processing is different in interpreter mode (Scala) and compile
mode (C) because we use different formats and libraries. (?)

(For implementing _if in the compiler, you can use the virtualized
`if` that operates on `Rep` types. However, be sure your conditional
and branches evaluate to `Rep` types, not other types.)

## Your task

Your task is to implement the interpreter, then the compiler to C.

## Bonus task 1

How would you implement in tagless final?

## Bonus task 2

Ensure your C generated code verifies.

Add the constraint that pixels should be in the range `0` to `255`,
both as an input requirement and an output assurance.

You can use the `(0 until ...).forall{x => ...}` construct to express
that range constraint.

You will need to guide the verification with some loop invariants and
assertions.
