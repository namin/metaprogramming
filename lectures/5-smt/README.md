# Using SMT in a backend

[imp2vc2smt.scala](imp2vc2smt.scala) is explaned below, and shows how SMT can be used for _verification_.
SMT can also be used for synthesis.
The project [Holey](https://github.com/namin/holey) shows synthesis for values. Holey combines staged execution of symbolic expressions with SMT to solve Python programming puzzles.
Left as an exercise, synthesis for expressions could be integrated with [imp2vc2smt.scala](imp2vc2smt.scala) by enumerating shapes of expressions (for example, linear combinations for an arithmetic expression), constraining and discharging to SMT for solving.
See also this [tutorial blog post on synthesis with SMT](https://github.com/sampsyo/minisynth).

# IMP to Verification Conditions to SMT

[imp2vc2smt.scala](imp2vc2smt.scala) presents minimal Hoare logic verifier for a simple imperative language (IMP) that generates verification conditions, outputs them in SMT-LIB format, and runs Z3 for checking.

## Language (IMP)

### Expressions
- Arithmetic: `Num(n)`, `Var(x)`, `Plus`, `Minus`, `Times`
- Boolean: `True`, `False`, `Eq`, `Lt`, `Leq`, `Not`, `And`, `Or`, `Implies`

### Statements
- `Skip` - no operation
- `Assign(x, e)` - variable assignment
- `Seq(s1, s2)` - sequential composition
- `If(b, s1, s2)` - conditional
- `While(b, inv, s)` - loop with invariant

## Core Algorithm

The verifier computes weakest preconditions and generates verification conditions in one pass:

```scala
def wpVc(s: Stmt, q: BExpr): (BExpr, List[BExpr]) = s match {
  case Skip => (q, Nil)
  case Assign(x, a) => (substitute(q, x, a), Nil)
  case Seq(s1, s2) =>
    val (wp2, vcs2) = wpVc(s2, q)
    val (wp1, vcs1) = wpVc(s1, wp2)
    (wp1, vcs1 ++ vcs2)
  case If(b, s1, s2) =>
    val (wp1, vcs1) = wpVc(s1, q)
    val (wp2, vcs2) = wpVc(s2, q)
    (And(Implies(b, wp1), Implies(Not(b), wp2)), vcs1 ++ vcs2)
  case While(b, inv, s) =>
    val (wpBody, vcsBody) = wpVc(s, inv)
    (inv, Implies(And(inv, b), wpBody) :: 
           Implies(And(inv, Not(b)), q) :: vcsBody)
}
```

Key insight: **Only loops generate verification conditions** (to validate invariants). All other constructs compute pure weakest preconditions.

## Verification Process

To verify a Hoare triple `{P} S {Q}`:
1. Compute `(wp, vcs) = wpVc(S, Q)`
2. Generate main VC: `P => wp`
3. Collect all VCs: main VC + loop VCs
4. Translate to SMT-LIB and check satisfiability

## Example: Finding Maximum

This example demonstrates how the verifier works on a simple conditional program:

**Program**: 
```
if (x < y) then
  m := y
else
  m := x
```

**Specification**: 
- Precondition: `true` (no assumptions about inputs)
- Postcondition: `((m = x || m = y) && (x <= m && y <= m))` 
  - This captures that `m` is the maximum: it equals one of the inputs and is ≥ both

**Verification Process**:

1. **Weakest Precondition Computation**: Starting from the postcondition `Q = ((m = x || m = y) && (x <= m && y <= m))`, we compute `wp(S, Q)`:

   - **Then branch** `wp(m := y, Q)`: Substitute `y` for `m` in `Q`
     ```
     ((y = x || y = y) && (x <= y && y <= y))
     ```
   
   - **Else branch** `wp(m := x, Q)`: Substitute `x` for `m` in `Q`  
     ```
     ((x = x || x = y) && (x <= x && y <= x))
     ```
   
   - **If statement** `wp(if (x < y) then ... else ..., Q)`: 
     ```
     (x < y => wp_then) && (!(x < y) => wp_else)
     = ((x < y => ((y = x || y = y) && (x <= y && y <= y))) && 
        (!(x < y) => ((x = x || x = y) && (x <= x && y <= x))))
     ```

2. **From WP to VC**: The **key insight** is that a Hoare triple `{P} S {Q}` is valid iff `P => wp(S, Q)` is a tautology. 

   - Our precondition is `P = true`
   - Our computed weakest precondition is the complex formula above
   - The **verification condition** is therefore: `true => wp(S, Q)`

3. **Why This Works**: 
   - The **WP answers**: "What must be true beforehand to guarantee the postcondition?"
   - The **VC checks**: "Does our actual precondition imply what must be true?"
   - Since `true => X` is valid iff `X` is always true, we're asking: "Is the WP always satisfied?"

4. **VC Interpretation**: The verification condition says "for any x,y, if we execute the program (taking the then-branch when x < y and else-branch otherwise), the postcondition will hold". The substitutions make explicit what happens in each execution path.

The SMT solver can verify this VC is valid, proving the program correctly computes the maximum.

## Running

```bash
sbt run
```

This will verify three example programs:
1. Maximum of two numbers
2. Simple counter
3. Loop with invariant
4. Maximum of two numbers with bogus postcondition

## [Output](output.txt)

The verifier outputs:
1. Number of VCs generated
2. Pretty-printed VCs
3. SMT-LIB script ready for Z3 or other SMT solvers

## Key Concepts Demonstrated

- **Compositional verification** - Each construct has a clear WP rule
- **Loop invariants** - Required for while loops; become the WP and generate VCs
- **SMT integration** - VCs translated to SMT-LIB for automated solving (logical validity checking)
