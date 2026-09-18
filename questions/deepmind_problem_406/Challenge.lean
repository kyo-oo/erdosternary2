import Mathlib

/-!
# Erdős Problem 406 — Challenge

For every exponent `n ≥ 9`, the ternary expansion of `2^n` contains
the digit `2`.

The `sorry` is intentional on the challenge side.  The solution file must
prove the same theorem with no additional hypothesis.
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
