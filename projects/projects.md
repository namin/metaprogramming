## Project suggestions 

* an embedded domain-specific language for image transformations, optimized according to a set of laws.  
  For example, you might coalesce adjacent rotations or resizings, or go further and compile down to efficient linear algebra operations.

* an embedded domain-specific language for music.  
  For example, you might build something along the lines of Szamozvancev and Gale's EDSL described in ([Well-typed music does not sound wrong, Haskell 2017](https://dl.acm.org/citation.cfm?id=3122964)), but using non-classical (e.g. Jazz) harmony rules.

* an embedded language for generating [efficient bit-twiddling code](https://www.cl.cam.ac.uk/~am21/hakmemc.html) from higher-level operations (e.g. loops and branches)

* an embedded language for context-free grammars with multiple interpretations, including:
    - parsers (perhaps using [monadic parser combinators](http://www.cs.nott.ac.uk/~pszgmh/monparsing.pdf))
    - producing graphical representations such as [railroad diagrams](https://en.wikipedia.org/wiki/Syntax_diagram)

* an embedding of a stack-based language like [Forth](https://en.wikipedia.org/wiki/Forth_(programming_language)).  Possible avenues:
    - can the embedding be typed?
    - how might you add support for reflection?
    - what optimizations are possible?

* an embedded language that compiles down to a low-level blockchain language such as [Simplicity](https://blockstream.com/2017/10/30/simplicity/), making it possible to write smart contracts in a high style

* investigate [Kiselyov's (2018) tagless-final translation from lambda calculus to SKI combinators](http://okmij.org/ftp/tagless-final/ski.pdf)
   - what further optimizations might be performed?

* an embedded langauge for remote procedure calls  
   - one possibility is to interpret the language to simulate symmetric communication on top of a stateless server  
     (see the [RPC calculus](https://www.era.lib.ed.ac.uk/handle/1842/3682) for a specification)

* use supercompilation techniques (see e.g. [Perfect Supercompilation](https://dl.acm.org/citation.cfm?id=705649)) to agressively optimize an embedded DSL

* an embedded query language, perhaps based on [Relational Algebra](https://en.wikipedia.org/wiki/Relational_algebra)

