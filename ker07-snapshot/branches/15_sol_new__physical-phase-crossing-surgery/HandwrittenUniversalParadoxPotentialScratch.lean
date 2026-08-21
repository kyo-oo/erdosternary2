import OmegaUPotentialBridgeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Handwritten universal-paradox U-potential

This module turns the local finite GST state table into a telescoping potential
inequality for an arbitrary seeded bad prefix.  It uses only the handwritten
U/Ω state coordinates already formalized in the V2 graph.
-/

/-- Four-state U-charge used by the handwritten potential. -/
def gstHandwrittenUChargeS (C : Nat) : Nat :=
  match C with
  | 0 => 0
  | 1 => 5
  | 2 => 9
  | _ => 12

/-- The exact finite twelve-state U inequality.  Every bad GST cell loses
enough potential to pay for its emitted ternary digit. -/
theorem gst_handwritten_u_local_bad_boundS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : GSTBadPairS C d) :
    24*d + gstHandwrittenUChargeS C ≤
      3 * gstHandwrittenUChargeS (gstStepCarryS C d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    simp [GSTBadPairS, GSTHappyPairS, gstHandwrittenUChargeS,
      gstStepCarryS] at hbad ⊢

/-- Exact next ternary-prefix decomposition used by the telescoping potential. -/
theorem gst_prefix_residue_succ_exactS (X K : Nat) :
    X % 3^(K+1) =
      X % 3^K + 3^K * gstDigitS X K := by
  unfold gstDigitS
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A finite bad prefix telescopes the local U-potential inequalities.

  24*(X mod 3^K) + q(D)
    <= 3^K * q(carry_K).
-/
theorem gst_bad_prefix_u_potential_boundS
    (D X K : Nat) (hD : D < 4)
    (hbad : ∀ j, j < K →
      GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)) :
    24*(X % 3^K) + gstHandwrittenUChargeS D ≤
      3^K * gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K) := by
  induction K with
  | zero =>
      simp [gstAffineMulCarryS, gstHandwrittenUChargeS]
  | succ K ih =>
      have hprev :
          24*(X % 3^K) + gstHandwrittenUChargeS D ≤
            3^K * gstHandwrittenUChargeS (gstAffineMulCarryS 4 D X K) :=
        ih (fun j hj => hbad j (by omega))
      have hcarrylt : gstAffineMulCarryS 4 D X K < 4 :=
        gst_affine_carry_lt_multiplierS 4 D X K (by decide) hD
      have hdigitlt : gstDigitS X K < 3 := by
        unfold gstDigitS
        exact Nat.mod_lt _ (by decide)
      have hlocal := gst_handwritten_u_local_bad_boundS
        (gstAffineMulCarryS 4 D X K) (gstDigitS X K)
        hcarrylt hdigitlt (hbad K (by omega))
      have hcarryStep := gstAffineS_forward_exact_all D X K
      have hres := gst_prefix_residue_succ_exactS X K
      rw [hcarryStep] at hlocal
      rw [hres, Nat.pow_succ]
      have hpow : 0 < 3^K := Nat.pow_pos (by decide)
      nlinarith

#check gst_bad_prefix_u_potential_boundS
#print axioms gst_bad_prefix_u_potential_boundS
