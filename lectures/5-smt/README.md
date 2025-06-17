# Using SMT in a backend

[imp2vc2smt](imp2vc2smt.scala) prsents minimal Hoare logic verifier for a simple imperative language (IMP) that generates verification conditions and outputs them in SMT-LIB format.

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

```scala
// Program: if (x < y) then m := y else m := x
// Post: m = max(x, y)

val maxProgram = If(Lt(Var("x"), Var("y")),
                   Assign("m", Var("y")),
                   Assign("m", Var("x")))

val maxPost = And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
                  And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))

// Generates 1 VC: true => ((x < y => post[y/m]) && (!(x < y) => post[x/m]))
```

## Running

```bash
sbt run
```

This will verify three example programs:
1. Maximum of two numbers
2. Simple counter
3. Loop with invariant

## Output

The verifier outputs:
1. Number of VCs generated
2. Pretty-printed VCs
3. SMT-LIB script ready for Z3 or other SMT solvers

## Key Concepts Demonstrated

- **Compositional verification** - Each construct has a clear WP rule
- **Loop invariants** - Required for while loops; become the WP
- **SMT integration** - VCs translated to SMT-LIB for automated solving
