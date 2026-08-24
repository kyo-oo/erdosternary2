import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTGraphV2InfiniteControl
open GSTU2DEventTransport
open GSTGraphV2HandwrittenOmegaUBlock

namespace GSTFinalResidualConnector

/-- A residual child Navigation witness is a literal Happy cell on the
full perfect-power Graph-V2 sheet at the corresponding absolute gate row. -/
theorem residual_child_witness_to_left_happy
    (s k m : Nat) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+k) m)) :
    ∃ j,
      HappyCell
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
          0 (s+k+1+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
          0 (s+k+1+j)).seven.digit := by
  obtain ⟨j, hd, hspace⟩ := hchild
  have hmod : gstCarry (gstNavigationConstant (s+k) m) j % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero _ j hspace
  have hlt : gstCarry (gstNavigationConstant (s+k) m) j < 4 := by
    cases j with
    | zero => simp [gstCarry, Nat.mod_one]
    | succ t => exact gstCarry_lt_four _ (t+1) (by omega)
  have hcarry :
      gstCarry (gstNavigationConstant (s+k) m) j = 0 ∨
      gstCarry (gstNavigationConstant (s+k) m) j = 3 := by
    omega
  refine ⟨j, ?_⟩
  have hb3 : 3 ≤ s+k+1 := by omega
  have hpow : 3^3 ≤ 3^(s+k+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hb3
  have hfour : 4 < 3^(s+k+1) := by
    norm_num at hpow ⊢
    omega
  have hone : 1 < 3^(s+k+1) := by omega
  have hE :
      4^0 * GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m =
        1 + 3^(s+k+1) * gstNavigationConstant (s+k) m := by
    simpa [GSTGraphV2HandwrittenOmegaUBlock.residualEnergy] using
      gst_navigation_decomposition (s+k) m (by omega)
  have hiff := graph_prefix_slice_happy_iff
    (GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m)
    0 (s+k+1) 1 (gstNavigationConstant (s+k) m) j hE hone
  apply hiff.2
  have hseed : (4 * 1) / 3^(s+k+1) = 0 := Nat.div_eq_of_lt hfour
  simpa [digit3, gstDigit, seededCarry, gstCarry, hseed] using
    ⟨hd, hcarry⟩

#check residual_child_witness_to_left_happy
#print axioms residual_child_witness_to_left_happy

end GSTFinalResidualConnector
