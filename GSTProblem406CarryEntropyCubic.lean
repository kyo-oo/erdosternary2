import GSTProblem406CarryEntropyBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact GST survivor-count cubic recurrence

The original source-neighbor finite carry automaton has four states
0,1,2,3. When counting surviving words, states 1 and 2 have exactly the
same continuation count at every length, yielding a three-dimensional
system and an exact CUBIC recurrence.

No custom hGate or generic surrogate-to-physical inference is used.
Prefix isometry (proved separately) transfers the counts to the number
of actual four-power exponent residue classes surviving p rows.
-/

namespace GSTProblem406CarryEntropyCubic

open GSTProblem406CarryEntropyBound

/-- The two central carry states have the same exact continuation count. -/
theorem middle_carry_counts_equal (n : Nat) :
    survivingCount n 1 = survivingCount n 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (survivingCount n 0+survivingCount n 1+survivingCount n 3) =
        (survivingCount n 0+survivingCount n 2+survivingCount n 3)
      omega

theorem next_zero (n : Nat) :
    survivingCount (n+1) 0 =
      survivingCount n 0 + survivingCount n 1 := by
  simp [survivingCount]

theorem next_one (n : Nat) :
    survivingCount (n+1) 1 =
      survivingCount n 0 + survivingCount n 1 +
        survivingCount n 3 := by
  simp [survivingCount]

theorem next_three (n : Nat) :
    survivingCount (n+1) 3 =
      2 * survivingCount n 1 := by
  change survivingCount n 1+survivingCount n 2 =
    2*survivingCount n 1
  rw [← middle_carry_counts_equal n]
  omega

/-- Exact third-order recurrence for the ORIGINAL initial physical
carry 1: a_(n+3) + 2a_n = 2a_(n+2) + 2a_(n+1). -/
theorem original_carry_cubic_recurrence (n : Nat) :
    survivingCount (n+3) 1 + 2*survivingCount n 1 =
      2*survivingCount (n+2) 1 +
        2*survivingCount (n+1) 1 := by
  have h0 := next_zero n
  have h1 := next_one n
  have h3 := next_three n
  have h01 :
      survivingCount (n+2) 0 =
        survivingCount (n+1) 0+survivingCount (n+1) 1 := by
    simpa [show n+1+1=n+2 by omega] using next_zero (n+1)
  have h11 :
      survivingCount (n+2) 1 =
        survivingCount (n+1) 0+survivingCount (n+1) 1+
          survivingCount (n+1) 3 := by
    simpa [show n+1+1=n+2 by omega] using next_one (n+1)
  have h31 :
      survivingCount (n+2) 3 =
        2*survivingCount (n+1) 1 := by
    simpa [show n+1+1=n+2 by omega] using next_three (n+1)
  have h12 :
      survivingCount (n+3) 1 =
        survivingCount (n+2) 0+survivingCount (n+2) 1+
          survivingCount (n+2) 3 := by
    simpa [show n+2+1=n+3 by omega] using next_one (n+2)
  omega

/-- Every carry state supports at least 2^n noncollision continuations,
so the genuine noncollision tree cannot become extinct at any fixed
finite exponent-prefix depth. -/
theorem uniform_binary_lower_bound (n : Nat) :
    ∀ c : Nat, c<4 → 2^n ≤ survivingCount n c := by
  induction n with
  | zero =>
      intro c hc
      simp [survivingCount]
  | succ n ih =>
      have h0 := ih 0 (by omega)
      have h1 := ih 1 (by omega)
      have h2 := ih 2 (by omega)
      have h3 := ih 3 (by omega)
      intro c hc
      have hPow : 2^(n+1) = 2*2^n := by rw [pow_succ]; ring
      rw [hPow]
      interval_cases c <;> simp [survivingCount] <;> omega

/-- Sharpened exact lower/upper bounds, original initial carry one.
Combines the new binary lower bound with the prior 7-of-9 contraction. -/
theorem physical_carry_survivor_sandwich (m : Nat) :
    2^(2*m) ≤ survivingCount (2*m) 1 ∧
      survivingCount (2*m) 1 ≤ 7^m := by
  exact ⟨uniform_binary_lower_bound (2*m) 1 (by omega),
    original_affine_pair_survivor_bound m⟩

#print axioms middle_carry_counts_equal
#print axioms next_zero
#print axioms next_one
#print axioms next_three
#print axioms original_carry_cubic_recurrence
#print axioms uniform_binary_lower_bound
#print axioms physical_carry_survivor_sandwich

end GSTProblem406CarryEntropyCubic
