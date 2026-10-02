import ErdosTernary2
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Four-power direct-existence closure

This file is the surgical replacement surface for the single historical
`gst_four_power_direct_existence_inline` boundary.  Every lemma here must be
assumption-free apart from the explicit arithmetic hypotheses in the target;
no provider/gate/grant proposition is accepted as a substitute for the
mathematics.
-/

namespace GSTFourPowerDirectExistenceClosure

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue81

/-- A certified full-power GST+/NULL witness is already the exact same-row
`CommonTwo` event.  The monolith's graph witness supplies digit two in a good
carry state; the checked one-step x4 carry law preserves digit two at that
same row in the next power. -/
theorem commonTwo_of_div_three
    (K : Nat) (hK5 : 5 ≤ K) (hK3 : K % 3 = 0) :
    CommonTwo K := by
  obtain ⟨p, hp, _hpN, hd, hspace⟩ :=
    gst_graph_witness_four_pow_div_three K hK5 hK3
  have hCmod : gstCarry (4^K) p % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero (4^K) p hspace
  have hClt : gstCarry (4^K) p < 4 :=
    gstCarry_lt_four (4^K) p hp
  have hgood : gstCarry (4^K) p = 0 ∨ gstCarry (4^K) p = 3 := by
    omega
  have hlift :=
    gst_pure_lift_or_forced_cascade (4^K) p hp hd hgood
  have hdnext : gstDigit (4 * 4^K) p = 2 := by
    rcases hlift with h | h
    · exact h.1
    · exact h.1
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTFourPowerDirectResidue.digit3, gstDigit] using hd
  · have hpow : 4^(K+1) = 4 * 4^K := by
      rw [Nat.pow_succ]
      ring
    rw [hpow]
    simpa [GSTFourPowerDirectResidue.digit3, gstDigit] using hdnext

/-- Every counterexample surviving the already-certified production layers is
simultaneously outside the divisible-by-three branch, both exact row-two
classes, all four row-three classes, and all fourteen row-four classes.

This packages the genuine unconditional arithmetic already present in the
production tree into one descent invariant.  It is deliberately a theorem
about `¬ CommonTwo K`, not a new gate or provider hypothesis. -/
theorem noCommonTwo_survivor_constraints
    (K : Nat) (hK5 : 5 ≤ K) (hNo : ¬ CommonTwo K) :
    K % 3 ≠ 0 ∧
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 ∧
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25 ∧
    ¬ RowFourClass (K % 81) := by
  have h3 : K % 3 ≠ 0 := by
    intro h
    exact hNo (commonTwo_of_div_three K hK5 h)
  have h9 := noCommonTwo_excludes_mod9_five_six K hNo
  have h27 := noCommonTwo_excludes_mod27_row_three K hNo
  have h81 := noCommonTwo_excludes_mod81_row_four K hNo
  exact ⟨h3, h9.1, h9.2, h27.1, h27.2.1, h27.2.2.1,
    h27.2.2.2, h81⟩

/-- Positive formulation of the same certified low-layer closure.  Any
exponent caught by one of the production residue layers has an actual
same-position digit-two witness for consecutive powers of four. -/
theorem commonTwo_of_certified_low_layer
    (K : Nat) (hK5 : 5 ≤ K)
    (h :
      K % 3 = 0 ∨
      K % 9 = 5 ∨ K % 9 = 6 ∨
      K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25 ∨
      RowFourClass (K % 81)) :
    CommonTwo K := by
  rcases h with h3 | h5 | h6 | h14 | h18 | h19 | h25 | h81
  · exact commonTwo_of_div_three K hK5 h3
  · exact commonTwo_of_mod9_five_or_six K (Or.inl h5)
  · exact commonTwo_of_mod9_five_or_six K (Or.inr h6)
  · exact commonTwo_of_mod27_row_three K (Or.inl h14)
  · exact commonTwo_of_mod27_row_three K (Or.inr (Or.inl h18))
  · exact commonTwo_of_mod27_row_three K (Or.inr (Or.inr (Or.inl h19)))
  · exact commonTwo_of_mod27_row_three K (Or.inr (Or.inr (Or.inr h25)))
  · exact commonTwo_of_mod81_row_four K h81

#check commonTwo_of_div_three
#check noCommonTwo_survivor_constraints
#check commonTwo_of_certified_low_layer
#print axioms commonTwo_of_div_three
#print axioms noCommonTwo_survivor_constraints
#print axioms commonTwo_of_certified_low_layer

end GSTFourPowerDirectExistenceClosure
