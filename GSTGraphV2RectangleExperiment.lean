import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2RectangleExperiment

/-!
# Exact 2D x2/base3 rectangle cancellation

For a microscopic grid satisfying

    a(r,p) + 2*d(r,p) = d(r+1,p) + 3*a(r,p+1),

all interior information cancels.  The proof is recursive rather than using
subtraction: the horizontal binary boundary word is built by repeatedly
shifting by two, and the vertical ternary boundary word is built by repeatedly
appending a ternary digit.
-/

/-- Binary carry word on a horizontal boundary, read from left to right. -/
def gstBinaryBoundaryWordR (a : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | L+1, p => 2 * gstBinaryBoundaryWordR a L p + a L p

/-- Ternary information word below height K on a fixed horizontal boundary. -/
def gstTernaryBoundaryWordR (d : Nat → Nat → Nat) (r : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => gstTernaryBoundaryWordR d r K + 3^K * d r K

/-- Exact microscopic rectangle-cell law. -/
def GSTBinaryRectangleCellsR
    (a d : Nat → Nat → Nat) (L K : Nat) : Prop :=
  ∀ r p, r < L → p < K →
    a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)

/-- One complete horizontal row telescopes to its two information endpoints
and the two binary carry words. -/
theorem gst_binary_rectangle_row_exactR
    (a d : Nat → Nat → Nat) (L p : Nat)
    (hcell : ∀ r, r < L →
      a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)) :
    2^L * d 0 p + gstBinaryBoundaryWordR a L p =
      d L p + 3 * gstBinaryBoundaryWordR a L (p+1) := by
  induction L with
  | zero => simp [gstBinaryBoundaryWordR]
  | succ L ih =>
      have ih' :
          2^L * d 0 p + gstBinaryBoundaryWordR a L p =
            d L p + 3 * gstBinaryBoundaryWordR a L (p+1) :=
        ih (fun r hr => hcell r (by omega))
      have hlast := hcell L (by omega)
      calc
        2^(L+1) * d 0 p + gstBinaryBoundaryWordR a (L+1) p =
            2 * (2^L * d 0 p + gstBinaryBoundaryWordR a L p) + a L p := by
              simp only [gstBinaryBoundaryWordR, Nat.pow_succ]
              ring
        _ = 2 * (d L p + 3 * gstBinaryBoundaryWordR a L (p+1)) + a L p := by
              rw [ih']
        _ = d (L+1) p +
              3 * (2 * gstBinaryBoundaryWordR a L (p+1) + a L (p+1)) := by
              omega
        _ = d (L+1) p + 3 * gstBinaryBoundaryWordR a (L+1) (p+1) := by
              rfl

/-- Boss's rectangle law.  Every interior x2/base3 cell cancels and only the
four physical boundaries remain:

  bottom binary word + 2^L * left ternary word
    = right ternary word + 3^K * top binary word.
-/
theorem gst_binary_rectangle_cancellation_exactR
    (a d : Nat → Nat → Nat) (L K : Nat)
    (hgrid : GSTBinaryRectangleCellsR a d L K) :
    gstBinaryBoundaryWordR a L 0 +
        2^L * gstTernaryBoundaryWordR d 0 K =
      gstTernaryBoundaryWordR d L K +
        3^K * gstBinaryBoundaryWordR a L K := by
  induction K with
  | zero => simp [gstTernaryBoundaryWordR]
  | succ K ih =>
      have hprefix : GSTBinaryRectangleCellsR a d L K := by
        intro r p hr hp
        exact hgrid r p hr (by omega)
      have ih' := ih hprefix
      have hrow := gst_binary_rectangle_row_exactR a d L K
        (fun r hr => hgrid r K hr (by omega))
      calc
        gstBinaryBoundaryWordR a L 0 +
            2^L * gstTernaryBoundaryWordR d 0 (K+1) =
          (gstBinaryBoundaryWordR a L 0 +
            2^L * gstTernaryBoundaryWordR d 0 K) +
            3^K * (2^L * d 0 K) := by
              simp only [gstTernaryBoundaryWordR]
              ring
        _ = (gstTernaryBoundaryWordR d L K +
              3^K * gstBinaryBoundaryWordR a L K) +
              3^K * (2^L * d 0 K) := by
              rw [ih']
        _ = gstTernaryBoundaryWordR d L K +
              3^K * (gstBinaryBoundaryWordR a L K + 2^L * d 0 K) := by
              ring
        _ = gstTernaryBoundaryWordR d L K +
              3^K * (d L K + 3 * gstBinaryBoundaryWordR a L (K+1)) := by
              rw [show gstBinaryBoundaryWordR a L K + 2^L * d 0 K =
                  d L K + 3 * gstBinaryBoundaryWordR a L (K+1) by
                    simpa [Nat.add_comm] using hrow]
        _ = gstTernaryBoundaryWordR d L (K+1) +
              3^(K+1) * gstBinaryBoundaryWordR a L (K+1) := by
              simp only [gstTernaryBoundaryWordR, Nat.pow_succ]
              ring

/-- At an `i = N` top boundary whose future binary carry word is zero, the
rectangle collapses to an exact equality involving only the other three
boundaries. -/
theorem gst_binary_rectangle_top_zeroR
    (a d : Nat → Nat → Nat) (L K : Nat)
    (hgrid : GSTBinaryRectangleCellsR a d L K)
    (htop : gstBinaryBoundaryWordR a L K = 0) :
    gstBinaryBoundaryWordR a L 0 +
        2^L * gstTernaryBoundaryWordR d 0 K =
      gstTernaryBoundaryWordR d L K := by
  have h := gst_binary_rectangle_cancellation_exactR a d L K hgrid
  simpa [htop] using h

end GSTGraphV2RectangleExperiment
