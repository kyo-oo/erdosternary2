import GSTTailFWorldtraceReplacement

/-!
# Erdős Problem 406 — Solution

This is the solution-side file for the conjecture itself:

  ∀ n ≥ 9, the ternary expansion of 2^n contains the digit 2.

The theorem has no custom hypothesis.  It is wired to the zero-input
production replacement and then bridged to the challenge-side recursive
predicate.
-/

def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

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

theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact GSTTailFWorldtraceReplacement.full_erdos n hn

#print axioms erdos_ternary_2
