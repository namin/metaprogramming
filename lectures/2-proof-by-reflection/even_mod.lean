-- Thanks to Kyle Miller for pointing out the `decide` tactic and offering this code

-- Object level: inductively defined Even predicate
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : ∀ n, Even n → Even (n + 2)

-- Meta level: computational even checker using modulo
def isEven : Nat → Bool
  | n => n % 2 == 0

-- Auxiliary function to construct Even proofs
def mkEven : (n : Nat) → n % 2 = 0 → Even n
  | 0, _ => Even.zero
  | 1, h => absurd h (by simp)
  | n + 2, h => Even.succ_succ n (mkEven n (by simp [Nat.add_mod] at h ⊢; exact h))

-- Auxiliary function to extract modulo property from Even
def evenToMod : {n : Nat} → Even n → n % 2 = 0
  | _, Even.zero => by simp
  | _, Even.succ_succ n h => by simp [Nat.add_mod, evenToMod h]

-- Main theorem
theorem isEven_iff {n : Nat} : isEven n = true ↔ Even n := by
  simp [isEven]
  constructor
  · exact mkEven n
  · exact evenToMod

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