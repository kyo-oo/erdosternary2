import ErdosTernary2

/-!
# Handwritten equations — exact finite GST formalization

This file translates the two handwritten pages into finite, kernel-checkable
statements.  No analytic infinity is introduced: “all depths / all time” is
represented by universal quantification over `K : Nat`.

Equation I: All-Depth Navigation–Nullspace Flux.
Equation II: Binary–Ternary 2–3–6 Synchronization.
-/

/-- The part of the affine carrier not yet promoted through the ternary scale
`3^K`.  This is the exact finite `N`/nullspace residue at depth `K`. -/
def gstNavigationNullspaceS (D X K : Nat) : Nat :=
  (D + 4 * (X % 3^K)) % 3^K

/-- HANDWRITTEN EQUATION I — ALL-DEPTH NAVIGATION–NULLSPACE FLUX.
At every finite information depth `K`, the incoming seed plus the visible
multiply-by-four ternary information splits *exactly* into the navigated carry
and the unresolved nullspace residue.  This is the rigorous `K → ∞` family:
there is one exact equality for every `K`.
-/
theorem gst_all_depth_navigation_nullspace_fluxS (D X K : Nat) :
    D + 4 * (X % 3^K) =
      3^K * gstAffineMulCarryS 4 D X K + gstNavigationNullspaceS D X K := by
  unfold gstAffineMulCarryS gstNavigationNullspaceS
  have h := Nat.mod_add_div (D + 4 * (X % 3^K)) (3^K)
  omega

/-- The one-cell graph form of Equation I.  Every physical `×4` cell splits
its mass into an output trit and three times the next carry. -/
theorem gst_all_space_cell_fluxS (C d : Nat) :
    gstCellMassV2S C d =
      gstCellOutputV2S C d + 3 * gstCellNextCarryV2S C d := by
  exact gst_cell_mass_conservationV2S C d

/-- HANDWRITTEN EQUATION II — BINARY–TERNARY 2–3–6 SYNCHRONIZATION.
The binary and ternary scale factors synchronize into the base-six world at
*every* depth. -/
theorem gst_binary_ternary_236_synchronizationS (j : Nat) :
    2^j * 3^j = 6^j := by
  calc
    2^j * 3^j = (2 * 3)^j := (mul_pow_local 2 3 j).symm
    _ = 6^j := by norm_num

/-- The physical two-micro-layer right chord is the depth-two instance of the
2–3–6 synchronization: its code is the complete base-six word `6^2 - 1 = 35`.
-/
theorem gst_physical_chord_is_236_square_minus_oneS
    (R p : Nat)
    (hd2 : gstDigitS R p = 2)
    (hI : GSTPhysicalTwoDigitBig1ClearS R p) :
    gstFirstMicroMassS (gstCarryS R p) (gstDigitS R p) +
        6 * gstSecondMicroMassS (gstCarryS R p) (gstDigitS R p) =
      2^2 * 3^2 - 1 := by
  rw [gst_physical_two_digit_chord_35S R p hd2 hI]
  norm_num

/-- Explicit replacement for the red seam: no `gst_end` is used here.
Once the residual origin is not already closed, the certified residual lift
constructs the parent Navigation witness.  The exact exponent factorization
then makes that witness contradict `hnoParent`.
-/
theorem gst_red_seam_closed_without_gst_endS
    (s k m n : Nat)
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hm : 1 ≤ m) (hm3 : m % 3 ≠ 0)
    (hnotClosed : ¬ GSTOriginClosed s k (m % 3))
    (hparentArg : 1 + 3*n = 1 + 3^k*m)
    (hnoParent : ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)))
    (hchildCore : GSTNavigationWitness (gstNavigationConstant (s+k) m)) :
    False := by
  have hparentCore :
      GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) :=
    gst_residual_navigation_lift s k m hs hk hm hm3 hnotClosed hchildCore
  apply hnoParent
  rw [hparentArg]
  exact hparentCore
