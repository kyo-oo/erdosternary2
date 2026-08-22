import GSTPrefixOnePhaseIncidenceControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2
open GSTV2

namespace GSTStrideTwoV2

/-!
# GST V2 stride-two / x4 cell

This layer is deliberately built from the clean Aug-22 production root.  It
contains no residual-termination import and no historical snapshot import.
The point is to align the local conservation law with the actual canonical
boundary events, which live two binary columns apart.
-/

/-- Abstract x2/base3 cell law. -/
def X2CellLaw (a d : Nat → Nat → Nat) : Prop :=
  ∀ r p,
    a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)

/-- Two adjacent x2 cells compose to one exact x4/base3 cell.  The middle
binary digit cancels algebraically; no bound, support horizon, or termination
assumption is used. -/
theorem stride_two_cell_exact
    (a d : Nat → Nat → Nat)
    (hcell : X2CellLaw a d)
    (r p : Nat) :
    2 * a r p + a (r+1) p + 4 * d r p =
      d (r+2) p + 3 * (2 * a r (p+1) + a (r+1) (p+1)) := by
  have h0 := hcell r p
  have h1 := hcell (r+1) p
  omega

/-- The concrete physical GST binary landscape satisfies the x2 cell law. -/
theorem physical_x2_cell_exact
    (R r p : Nat) :
    GSTPhysicalKernel.binaryColumnCarry R p r +
        2 * GSTPhysicalKernel.binaryColumnDigit R p r =
      GSTPhysicalKernel.binaryColumnDigit R p (r+1) +
        3 * GSTPhysicalKernel.binaryColumnCarry R (p+1) r := by
  let X := 2^r * R
  have hq :
      (2 * X) / 3^p =
        GSTPhysicalKernel.binaryColumnCarry R p r + 2 * (X / 3^p) := by
    dsimp [X]
    simpa [GSTPhysicalKernel.binaryColumnCarry] using
      GSTPhysicalKernel.binary_mul_two_quotient_decomposition (2^r * R) p
  have hq1 :
      (2 * X) / 3^(p+1) =
        GSTPhysicalKernel.binaryColumnCarry R (p+1) r + 2 * (X / 3^(p+1)) := by
    dsimp [X]
    simpa [GSTPhysicalKernel.binaryColumnCarry] using
      GSTPhysicalKernel.binary_mul_two_quotient_decomposition (2^r * R) (p+1)
  have hv : X / 3^p = X / 3^p % 3 + 3 * (X / 3^(p+1)) := by
    calc
      X / 3^p = (X / 3^p) % 3 + 3 * ((X / 3^p) / 3) :=
        (Nat.mod_add_div (X / 3^p) 3).symm
      _ = (X / 3^p) % 3 + 3 * (X / 3^(p+1)) := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hv2 : (2 * X) / 3^p =
      (2 * X) / 3^p % 3 + 3 * ((2 * X) / 3^(p+1)) := by
    calc
      (2 * X) / 3^p = ((2 * X) / 3^p) % 3 +
          3 * (((2 * X) / 3^p) / 3) :=
        (Nat.mod_add_div ((2 * X) / 3^p) 3).symm
      _ = ((2 * X) / 3^p) % 3 + 3 * ((2 * X) / 3^(p+1)) := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hpow : 2^(r+1) * R = 2 * X := by
    dsimp [X]
    rw [Nat.pow_succ]
    ac_rfl
  simp only [GSTPhysicalKernel.binaryColumnDigit]
  rw [hpow]
  omega

/-- Physical x4/base3 stride-two cell.  This is the microscopic conservation
law aligned with the child columns `(0,2)` and parent columns `(L,L+2)` in the
canonical full-energy grid. -/
theorem physical_stride_two_cell_exact
    (R r p : Nat) :
    2 * GSTPhysicalKernel.binaryColumnCarry R p r +
        GSTPhysicalKernel.binaryColumnCarry R p (r+1) +
        4 * GSTPhysicalKernel.binaryColumnDigit R p r =
      GSTPhysicalKernel.binaryColumnDigit R p (r+2) +
        3 * (2 * GSTPhysicalKernel.binaryColumnCarry R (p+1) r +
          GSTPhysicalKernel.binaryColumnCarry R (p+1) (r+1)) := by
  apply stride_two_cell_exact
    (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r)
    (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r)
  intro r p
  exact physical_x2_cell_exact R r p

/-- The stride-two incoming mass; it is the x4 carry-channel companion of one
visible ternary digit. -/
def strideCarry (R r p : Nat) : Nat :=
  2 * GSTPhysicalKernel.binaryColumnCarry R p r +
    GSTPhysicalKernel.binaryColumnCarry R p (r+1)

/-- Compact x4 form of the same local law. -/
theorem physical_stride_two_cell_compact
    (R r p : Nat) :
    strideCarry R r p + 4 * GSTPhysicalKernel.binaryColumnDigit R p r =
      GSTPhysicalKernel.binaryColumnDigit R p (r+2) +
        3 * strideCarry R r (p+1) := by
  simpa [strideCarry, Nat.add_assoc] using physical_stride_two_cell_exact R r p

#check stride_two_cell_exact
#check physical_x2_cell_exact
#check physical_stride_two_cell_exact
#check physical_stride_two_cell_compact
#print axioms stride_two_cell_exact
#print axioms physical_x2_cell_exact
#print axioms physical_stride_two_cell_exact
#print axioms physical_stride_two_cell_compact

end GSTStrideTwoV2
