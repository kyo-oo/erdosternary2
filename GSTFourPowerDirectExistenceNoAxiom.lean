import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectExistence
import GSTFourPowerDirectAdditionCarry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Separate no-axiom attempt for `FourPowerDirectExistence`

This file is intentionally *not* wired into the monolith.  It tests the final
missing seam in isolation:

`FourPowerDirectExistence.FourPowerDirectExistence`

Mathematical bridge:
* for `K = 5,6`, row `p = 2` is checked directly;
* for `K ≥ 8`, the existing four-power navigation stack supplies a Happy cell;
* a Happy cell means source digit is `2` and the multiplication-by-four carry is
  `0` or `3`, hence the next power has the same digit `2` at the same position.
-/

namespace GSTFourPowerDirectExistenceNoAxiom

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry
open GSTInfiniteFourPowerNavigation

/-- A Happy cell for `4^K` is exactly a same-row common-two witness for
`4^K` and `4^(K+1)`. -/
theorem happyCell_to_commonTwo
    (K p : Nat) (hp : 1 ≤ p)
    (hHappy : HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    CommonTwo K := by
  rcases hHappy with ⟨hd, hc⟩
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTFourPowerDirectResidue.digit3] using hd
  · have hsrc : GSTFourPowerDirectResidue.digit3 (4^K) p = 2 := by
      simpa [GSTFourPowerDirectResidue.digit3] using hd
    have hcarryMod : directCarry4 (4^K) p % 3 = 0 := by
      rcases hc with h0 | h3
      · simpa [directCarry4, carry4, h0]
      · simpa [directCarry4, carry4, h3]
    have hmulFormula := digit3_four_mul (4^K) p
    have hmul : GSTFourPowerDirectResidue.digit3 (4 * (4^K)) p = 2 := by
      rw [hmulFormula, hsrc]
      omega
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Direct base case `K = 5`, witnessed at row two. -/
theorem commonTwo_five : CommonTwo 5 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

/-- Direct base case `K = 6`, witnessed at row two. -/
theorem commonTwo_six : CommonTwo 6 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

/-- Candidate replacement for the production-boundary axiom
`gst_four_power_direct_existence_inline`. -/
theorem fourPowerDirectExistence_noAxiom : FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ :=
      GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK8
    exact happyCell_to_commonTwo K p (by omega) hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact commonTwo_five
    · exact commonTwo_six
    · exact (hK7 rfl).elim

#print axioms happyCell_to_commonTwo
#print axioms commonTwo_five
#print axioms commonTwo_six
#print axioms fourPowerDirectExistence_noAxiom

end GSTFourPowerDirectExistenceNoAxiom
