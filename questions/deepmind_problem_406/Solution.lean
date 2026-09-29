import ErdosTernary2
import GSTFourPowerHappyBaseCamp

/-!
# Erdős Problem 406 — ternary powers of two

Comparator wiring, repaired and staged.

The challenge predicate bridge is the monolith's own green idiom; the
statement below is the challenge statement with the war's one remaining
seam as an explicit named premise: the tail climb (every exponent above
the kernel-checked base camp of 500 owns a physical Happy row).  The
premise is the open content; every other link — the kernel base camp
(8..500), the residue rows, the creation-master bridge, the two-wave
conversion, the conjecture-form crown, the odd theorem — is
machine-checked on this branch.

The official comparator requires the unconditional statement; the exact
gap between this file and that requirement is the named premise.
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

/-- The war's one remaining seam, named: every exponent above the
kernel-checked base camp owns a physical Happy row. -/
def erdos_ternary_2_tail_climb : Prop :=
  GSTFourPowerHappyBaseCamp.four_power_happy_climb_tail

/-- Erdős Problem 406: every `2^n` with `n ≥ 9` has a ternary digit two —
from the named seam, unconditionally in `n`. -/
theorem erdos_ternary_2 (htail : erdos_ternary_2_tail_climb) :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact GSTFourPowerHappyBaseCamp.erdos_ternary_2_universal_of_climb_tail
    htail n hn

#print axioms erdos_ternary_2
