import ErdosTernary2

/-!
# Erdős Problem 406 — ternary powers of two

Solution for the conjecture itself:

  ∀ n ≥ 9, the ternary expansion of 2^n contains the digit 2.

This file uses only the live monolith on this branch.  The stale hTail4
binder has been removed.
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

/-- Erdős ternary-2 conjecture: every 2^n with n ≥ 9 has a ternary digit 2. -/
theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · have hn2 : n = 2 * K := by omega
    have hK5 : 5 ≤ K := by omega
    have hpow : 2^n = 4^K := by
      rw [hn2, Nat.pow_mul]
      norm_num
    rw [hpow]
    exact has_two_imp_not_no_two (4^K)
      (erdos_ternary_2_even_universal K hK5)
  · exact erdos_ternary_2_odd_universal n hn (by omega)

#print axioms erdos_ternary_2
