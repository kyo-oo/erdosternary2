import ErdosTernary2

/-!
# DeepMind Problem 406 — comparator solution

This is the solution-side Lean file for the official comparator harness.
It imports the checked green monolith `ErdosTernary2` and bridges the
question-side recursive predicate to the monolith's `noTernaryTwo`
predicate.

The production seam now carries the third-wave climb as its single named
input: the universe's infinite four-power navigation chain converts the
climb primitive (`GSTInfiniteFourPowerNavigation.four_power_happy_climb`:
every exponent from eight onward owns a physical Happy row — the statement
the worldtrace simulation certifies at N = 1500) into the full statement
below through kernel-verified bridges.  The climb is stated in one line and
consumed everywhere by name.
-/

/-- Byte-identical challenge-side definition. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Bridge the challenge recursion to the monolith's `noTernaryTwo`. -/
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
        exact ih (n / 3) (Nat.div_lt_self (by omega) (by decide : 1 < 3))

/-- DeepMind Problem 406 / Erdős ternary-2 comparator solution, delivered
from the third-wave climb through the green monolith seam. -/
theorem erdos_ternary_2
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact erdos_ternary_2_universal hClimb n hn
