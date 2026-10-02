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

#check commonTwo_of_div_three
#print axioms commonTwo_of_div_three

end GSTFourPowerDirectExistenceClosure
