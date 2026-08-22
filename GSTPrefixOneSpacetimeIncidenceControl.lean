import GSTPrefixOnePhaseIncidenceControl
import GSTResidueSpacetimeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTSpacetimeV2

/-!
# Physical GST V2 spacetime rectangle

The horizontal coordinate is a genuine binary generation `r`; the vertical
coordinate is a genuine ternary position `p`.  No same-index child/parent
identification is made.  The local x2/base3 conservation law is summed over an
arbitrary rectangle, so the theorem is uniform in both depths and has no
terminal or finite-support hypothesis.
-/

/-- Binary carry word along a horizontal boundary. -/
def binaryBoundaryWord (a : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | L+1, p => 2 * binaryBoundaryWord a L p + a L p

/-- Ternary digit word below height `K` on one binary generation. -/
def ternaryBoundaryWord (d : Nat → Nat → Nat) (r : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => ternaryBoundaryWord d r K + 3^K * d r K

/-- Exact microscopic x2/base3 cell law on an arbitrary rectangle. -/
def RectangleCells
    (a d : Nat → Nat → Nat) (L K : Nat) : Prop :=
  ∀ r p, r < L → p < K →
    a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)

/-- A horizontal row telescopes to its two digit endpoints and two carry words. -/
theorem rectangle_row_exact
    (a d : Nat → Nat → Nat) (L p : Nat)
    (hcell : ∀ r, r < L →
      a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)) :
    2^L * d 0 p + binaryBoundaryWord a L p =
      d L p + 3 * binaryBoundaryWord a L (p+1) := by
  induction L with
  | zero => simp [binaryBoundaryWord]
  | succ L ih =>
      have ih' :
          2^L * d 0 p + binaryBoundaryWord a L p =
            d L p + 3 * binaryBoundaryWord a L (p+1) :=
        ih (fun r hr => hcell r (by omega))
      have hlast := hcell L (by omega)
      calc
        2^(L+1) * d 0 p + binaryBoundaryWord a (L+1) p =
            2 * (2^L * d 0 p + binaryBoundaryWord a L p) + a L p := by
              simp only [binaryBoundaryWord, Nat.pow_succ]
              ring
        _ = 2 * (d L p + 3 * binaryBoundaryWord a L (p+1)) + a L p := by
              rw [ih']
        _ = d (L+1) p +
              3 * (2 * binaryBoundaryWord a L (p+1) + a L (p+1)) := by
              omega
        _ = d (L+1) p + 3 * binaryBoundaryWord a (L+1) (p+1) := by
              rfl

/-- Full two-dimensional cancellation.  Every interior term disappears; only
the four physical boundaries remain. -/
theorem rectangle_cancellation_exact
    (a d : Nat → Nat → Nat) (L K : Nat)
    (hgrid : RectangleCells a d L K) :
    binaryBoundaryWord a L 0 +
        2^L * ternaryBoundaryWord d 0 K =
      ternaryBoundaryWord d L K +
        3^K * binaryBoundaryWord a L K := by
  induction K with
  | zero => simp [ternaryBoundaryWord]
  | succ K ih =>
      have hprefix : RectangleCells a d L K := by
        intro r p hr hp
        exact hgrid r p hr (by omega)
      have ih' := ih hprefix
      have hrow := rectangle_row_exact a d L K
        (fun r hr => hgrid r K hr (by omega))
      calc
        binaryBoundaryWord a L 0 +
            2^L * ternaryBoundaryWord d 0 (K+1) =
          (binaryBoundaryWord a L 0 +
            2^L * ternaryBoundaryWord d 0 K) +
            3^K * (2^L * d 0 K) := by
              simp only [ternaryBoundaryWord]
              ring
        _ = (ternaryBoundaryWord d L K +
              3^K * binaryBoundaryWord a L K) +
              3^K * (2^L * d 0 K) := by
              rw [ih']
        _ = ternaryBoundaryWord d L K +
              3^K * (binaryBoundaryWord a L K + 2^L * d 0 K) := by
              ring
        _ = ternaryBoundaryWord d L K +
              3^K * (d L K + 3 * binaryBoundaryWord a L (K+1)) := by
              rw [show binaryBoundaryWord a L K + 2^L * d 0 K =
                  d L K + 3 * binaryBoundaryWord a L (K+1) by
                    simpa [Nat.add_comm] using hrow]
        _ = ternaryBoundaryWord d L (K+1) +
              3^(K+1) * binaryBoundaryWord a L (K+1) := by
              simp only [ternaryBoundaryWord, Nat.pow_succ]
              ring

/-- Binary-generation quotient recurrence at one ternary cut. -/
theorem physical_binary_quotient_succ
    (R r p : Nat) :
    (2^(r+1) * R) / 3^p =
      GSTPhysicalKernel.binaryColumnCarry R p r +
        2 * ((2^r * R) / 3^p) := by
  have hpow : 2^(r+1) * R = 2 * (2^r * R) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow]
  simpa [GSTPhysicalKernel.binaryColumnCarry] using
    GSTPhysicalKernel.binary_mul_two_quotient_decomposition (2^r * R) p

/-- Ternary quotient recurrence at one binary generation. -/
theorem physical_ternary_quotient_succ
    (X p : Nat) :
    X / 3^p = (X / 3^p) % 3 + 3 * (X / 3^(p+1)) := by
  calc
    X / 3^p = (X / 3^p) % 3 + 3 * ((X / 3^p) / 3) := by
      exact (Nat.mod_add_div (X / 3^p) 3).symm
    _ = (X / 3^p) % 3 + 3 * (X / 3^(p+1)) := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- The abstract rectangle cell is the literal GST physical binary column. -/
theorem physical_cell_exact
    (R r p : Nat) :
    GSTPhysicalKernel.binaryColumnCarry R p r +
        2 * GSTPhysicalKernel.binaryColumnDigit R p r =
      GSTPhysicalKernel.binaryColumnDigit R p (r+1) +
        3 * GSTPhysicalKernel.binaryColumnCarry R (p+1) r := by
  have hr := physical_binary_quotient_succ R r p
  have hr1 := physical_binary_quotient_succ R r (p+1)
  have hv := physical_ternary_quotient_succ (2^r * R) p
  have hv1 := physical_ternary_quotient_succ (2^(r+1) * R) p
  simp only [GSTPhysicalKernel.binaryColumnDigit] at hv hv1 ⊢
  omega

/-- Every finite window cut from the unbounded physical GST spacetime satisfies
the same uniform cell law. -/
theorem physical_rectangle_cells
    (R L K : Nat) :
    RectangleCells
      (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r) L K := by
  intro r p _hr _hp
  exact physical_cell_exact R r p

/-- A physical ternary boundary word is exactly the corresponding residue. -/
theorem physical_ternary_boundary_exact
    (R r K : Nat) :
    ternaryBoundaryWord
        (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r) r K =
      (2^r * R) % 3^K := by
  induction K with
  | zero =>
      rw [ternaryBoundaryWord, Nat.pow_zero, Nat.mod_one]
  | succ K ih =>
      rw [ternaryBoundaryWord, ih]
      simpa [gstPrefixedModulusS, GSTPhysicalKernel.binaryColumnDigit,
        gstDigitS] using
        (gst_prefixed_residue_stepS 0 1 (2^r * R) K).symm

/-- A physical binary boundary word is exactly the wide carry across its
ternary cut. -/
theorem physical_binary_boundary_exact
    (R L p : Nat) :
    binaryBoundaryWord
        (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r) L p =
      (2^L * (R % 3^p)) / 3^p := by
  induction L with
  | zero =>
      have hp : 0 < 3^p := Nat.pow_pos (by decide)
      have hr : R % 3^p < 3^p := Nat.mod_lt _ hp
      simp [binaryBoundaryWord, Nat.div_eq_of_lt hr]
  | succ L ih =>
      have hmod :
          (2^L * (R % 3^p)) % 3^p = (2^L * R) % 3^p := by
        simp only [Nat.mul_mod, Nat.mod_mod]
      have hcarry :
          GSTPhysicalKernel.binaryColumnCarry (R % 3^p) p L =
            GSTPhysicalKernel.binaryColumnCarry R p L := by
        simp only [GSTPhysicalKernel.binaryColumnCarry, hmod]
      have hstep := physical_binary_quotient_succ (R % 3^p) L p
      rw [binaryBoundaryWord, ih]
      rw [hcarry] at hstep
      omega

/-- Fully instantiated GST V2 rectangle.  It is valid for every binary width
and every ternary height, and retains the top wide-carry boundary instead of
assuming termination. -/
theorem physical_rectangle_exact
    (R L K : Nat) :
    2^L * (R % 3^K) =
      (2^L * R) % 3^K +
        3^K * ((2^L * (R % 3^K)) / 3^K) := by
  have h := rectangle_cancellation_exact
    (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r)
    (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r)
    L K (physical_rectangle_cells R L K)
  rw [physical_binary_boundary_exact,
      physical_ternary_boundary_exact,
      physical_ternary_boundary_exact,
      physical_binary_boundary_exact] at h
  simpa only [Nat.mod_one, Nat.mul_zero, Nat.zero_add] using h

end GSTSpacetimeV2

#check GSTSpacetimeV2.physical_cell_exact
#check GSTSpacetimeV2.physical_rectangle_exact
#print axioms GSTSpacetimeV2.physical_rectangle_exact
