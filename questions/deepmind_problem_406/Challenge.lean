import Mathlib

/-!
# Erdős Problem 406 — ternary digits of powers of two

Challenge statement: every power `2^n` with `n ≥ 9` contains a ternary
digit `2`.
-/

def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

theorem erdos_ternary_2 :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  sorry
