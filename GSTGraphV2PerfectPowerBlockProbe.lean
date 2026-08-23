import ErdosTernary2
import GSTGraphV2PerfectPowerAncestry

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Aug-23 canonical finite-prefix bridge probe.  This deliberately targets
one actual child gate; no arbitrary affine tail is quantified. -/
theorem gst_graph_v2_child_gate_parent_prefix_probe
    (s n q : Nat) (hs : 1 ≤ s)
    (hgate : GSTSeededHappyS 0 (gstNavigationConstant (s+1) n) q) :
    let a := (1 + 3*n) % 3^(q+1)
    gstCarryS (gstNavigationConstant s a) (q+1) = 0 ∨
      gstCarryS (gstNavigationConstant s a) (q+1) = 3 := by
  dsimp only
  have hchild :
      gstDigitS (gstNavigationConstant (s+1) n) q = 2 ∧
      (gstCarryS (gstNavigationConstant (s+1) n) q = 0 ∨
       gstCarryS (gstNavigationConstant (s+1) n) q = 3) := by
    simpa [GSTSeededHappyS, gst_seed_zero_affine_carry_eq_physicalS] using hgate
  have hcut := gst_canonical_origin_cut_carryS
    s ((1 + 3*n) % 3^(q+1)) (q+1) ((1 + 3*n) / 3^(q+1)) hs
  have hdecomp :
      (1 + 3*n) % 3^(q+1) +
          3^(q+1) * ((1 + 3*n) / 3^(q+1)) = 1 + 3*n :=
    Nat.mod_add_div (1 + 3*n) (3^(q+1))
  rw [hdecomp] at hcut
  -- The remaining step is the exact canonical block relation between the
  -- child Q_(s+1)(n) gate and the parent Q_s(1+3n) carry one row later.
  have hparentShape := gst_hard_tail_parent_navigationS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    gstCanonicalPrefixOffsetS gst_navigation_constant_unit_prefixS
    s n hs
  rw [hparentShape] at hcut
  rw [gst_prefixed_one_carry_shiftS] at hcut
  -- Normalize the canonical hard tail against the phase-one shared carrier.
  simpa [GSTHardPrefixOneTailS, gstCanonicalPrefixOffsetS] using hchild.2

#check gst_graph_v2_child_gate_parent_prefix_probe
#print axioms gst_graph_v2_child_gate_parent_prefix_probe
