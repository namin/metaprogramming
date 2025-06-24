# Proof by reflection

The seminal FOL from the late 70s pioneered proof by reflection.
[See a live reproduction of the FOL Prolegomena](https://io.livecode.ch/learn/namin/GETFOL).

The principle of proof by reflection:<br/>
_“Change theorem proving in the theory into evaluation in the metatheory.”_<br/>
(Weyrauch in section 9 of _Prolegomena to a Theory of Formal Reasoning_, 1978
[PDF](https://github.com/namin/GETFOL/blob/master/tst/prolegomena/Weyhrauch_Prolegomena.pdf))

We show the reflection principle in action through a small example, in each of FOL and Lean.

- [FOL](even.tst) ([live tutorial](https://io.livecode.ch/learn/namin/GETFOL/reflection))
- [Lean](even.lean) ([live](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fnamin%2Fmetaprogramming%2Frefs%2Fheads%2Fmaster%2Flectures%2F2-proof-by-reflection%2Feven.lean))

## Key advances in Lean

A key philosophical shift from reflection as a meta-theoretical add-on to computation as a first-class citizen, recognizing that:
- Computation and deduction are complementary.
- Many proofs are just computation in disguise.
- The type system itself can encorfe the soundness of reflection.

### Unified type theory foundation

Lean's dependent type theory unifies the object and meta levels of FOL.
Both `Prop` and `Bool` are first-class types in Lean.

### Built-in computational reduction

FOL requires manual attachment of computational semantics, while Lean's type theory has computation built into its core.
The function `isEven` automatically computes during type checking.

### Native decidability framework

FOL manually constructs the reflection infrastructure.
- Explicit representation of terms, formulas, and predicates.
- Manual axioms connecting syntactic and semantic levels.
- Complex axiom to enable reflection.

In contrast, Lean provides a systematic decidability framework.

### Proof-producing computation

FOL's reflection produces theorems as side effects.

Lean's `decide` tactic produces actual proof terms that can be type-checked independently.
The computation _is_ the proof.

### Type safety

The type system enforces the soundness of reflection.
