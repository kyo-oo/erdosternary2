import ErdosPreOmega
import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Earliest canonical Happy-Gate control

An arbitrary Happy Gate need not have a short physical BIG1 chord.  The
earliest gate does: every lower row is a bad prefix, so the all-scale U
potential controls the lower ternary residue.  In the carry-three case this
gives the sharp inequality needed by the first three binary columns.
-/

/-- A Navigation witness has an earliest digit-two gate.  Below it the exact
four-state bad language holds, and a carry-three earliest gate has lower
residue strictly below seven eighths of its ternary place. -/
theorem gpt56_first_navigation_gate_u_control
    (R : Nat) (hnav : GSTNavigationWitness R) :
    ∃ q,
      gstDigit R q = 2 ∧
      (gstCarry R q = 0 ∨ gstCarry R q = 3) ∧
      (∀ j, j < q →
        GSTBadPairS (gstAffineCarryS 0 R j) (gstDigitS R j)) ∧
      (gstCarry R q = 3 → 8 * (R % 3^q) < 7 * 3^q) := by
  have hex : ∃ j,
      gstDigit R j = 2 ∧
        (gstCarry R j = 0 ∨ gstCarry R j = 3) := by
    obtain ⟨j, hd2, hspace⟩ := hnav
    have hCmod : gstCarry R j % 3 = 0 :=
      gstGoodSpace_carry_mod3_zero R j hspace
    have hClt : gstCarry R j < 4 := by
      cases j with
      | zero =>
          simp only [gstCarry, Nat.pow_zero, Nat.mod_one, Nat.mul_zero,
            Nat.zero_div]
          decide
      | succ k => exact gstCarry_lt_four R (k+1) (by omega)
    have hC : gstCarry R j = 0 ∨ gstCarry R j = 3 := by omega
    exact ⟨j, hd2, hC⟩
  let q := Nat.find hex
  have hgate := Nat.find_spec hex
  have hbad : ∀ j, j < q →
      GSTBadPairS (gstAffineCarryS 0 R j) (gstDigitS R j) := by
    intro j hj hhappy
    have hgood :
        gstDigit R j = 2 ∧
          (gstCarry R j = 0 ∨ gstCarry R j = 3) := by
      simpa [GSTHappyPairS, gstAffineCarryS, gstDigitS, gstDigit, gstCarry]
        using hhappy
    have hqle : q ≤ j := by
      dsimp [q]
      exact Nat.find_min' hex hgood
    omega
  refine ⟨q, hgate.1, hgate.2, hbad, ?_⟩
  intro hC3
  have hU := gst_bad_prefix_u_potential_boundS 0 R q (by decide) hbad
  have hU' :
      24 * (R % 3^q) + 5 ≤ 3^q * 21 := by
    simpa [gstAffineCarryS, gstCarry, gstHandwrittenUChargeS, hC3] using hU
  omega

#check gpt56_first_navigation_gate_u_control
#print axioms gpt56_first_navigation_gate_u_control
