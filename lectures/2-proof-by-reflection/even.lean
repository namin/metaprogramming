-- Thanks to Kyle Miller for pointing out the `decide` tactic and offering this code

-- Object level: inductively defined Even predicate
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : ∀ n, Even n → Even (n + 2)

-- Meta level: computational even checker
def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => isEven n

theorem isEven_iff {n : Nat} : isEven n = true ↔ Even n := by
  constructor
  · fun_induction isEven n <;> simp +contextual [Even.zero, Even.succ_succ, *]
  · intro h; induction h <;> simp [isEven, *]

instance (n : Nat) : Decidable (Even n) :=
  decidable_of_decidable_of_iff isEven_iff

example : Even 2 := by decide
example : Even 4 := by decide
example : Even 6 := by decide
example : Even 100 := by decide
example : Even 1000 := by decide +kernel -- skip the elaborator when evaluating `isEven`.
example : ¬ Even 101 := by decide
example : ∀ n < 10, Even (2 * n) := by decide
example : ∀ n < 10, Even (2 * n) ∧ ¬ Even (2 * n + 1) := by decide