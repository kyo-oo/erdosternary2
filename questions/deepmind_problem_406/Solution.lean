import ErdosTernary2

/-!
# DeepMind Problem 406 — comparator solution

Green-era wiring, restored.  The solution-side Lean file for the
comparator harness: it imports the green monolith `ErdosTernary2` and
bridges the question-side recursive predicate to the monolith's
`noTernaryTwo` predicate.  The unconditional crown
`erdos_ternary_2_universal` is restored at the green comparator
commit's shape (run 34002729428); the hypothesis-to-theorem
conversion (`GSTHypothesisToTheorem.lean`) and the base-camp shrink
(`GSTFourPowerHappyBaseCamp.lean`) stand beside it in the same
monolith build as named reductions of the same statement to their
seams.
-/

/-- Byte-identical challenge-side recursive predicate. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Bridge the challenge predicate to the monolith predicate. -/
theorem noTernaryDigitTwo_eq_noTernaryTwo (n : Nat) :
    noTernaryDigitTwo n = noTernaryTwo n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [noTernaryDigitTwo.eq_def n, noTernaryTwo.eq_def n]
    by_cases hn : n = 0
    · simp [hn]
    · by_cases h2 : n % 3 = 2
      · simp [hn, h2]
      · simp [hn, h2]
        exact ih (n / 3)
          (Nat.div_lt_self (by omega) (by decide : 1 < 3))

/-- DeepMind Problem 406 / Erdős ternary-2 comparator solution. -/
theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact erdos_ternary_2_universal n hn

#print axioms erdos_ternary_2
