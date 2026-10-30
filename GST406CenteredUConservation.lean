import GST406PhysicalUTerminal
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Genuine physical source — centered GST U flux conservation

The raw all-source Equation III has a persistent -315 potential on
the terminal zero row; this produces a persistent -630 derivative.
The centered physical potential is zero after terminal depth.
Thus an exact weighted sum across ALL source rows is a finite
boundary equation. This removes the false zero-endpoint intuition
without assuming or relabeling the universal CommonTwo gate.

The original parent and child are literal 4^(K+3) and 4^K.
-/

namespace GST406CenteredUConservation

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GST406PhysicalUTerminal

/-- The exact physical right-minus-64-times-left handwritten-U jump. -/
def physicalUDifference (K p : Nat) : Int :=
    gstUJumpExact
        (graph (4^K) 3 p).seven.carry
        (graph (4^K) 3 p).seven.digit -
      ((4^3 : Nat) : Int) *
        gstUJumpExact
          (graph (4^K) 0 p).seven.carry
          (graph (4^K) 0 p).seven.digit

/-- The centered U potential is ZERO above the finite physical word. -/
def centeredPotential (K p : Nat) : Int :=
    potentialWith gstUChargeExact (4^3)
      (unifiedState (4^K) 3 p).core + 315

/-- The correct physical Equation-III derivative includes the +630
vacuum compensation; it is NOT globally nonnegative. -/
theorem centered_equationIII (K p : Nat) :
    physicalUDifference K p + 630 =
      3 * centeredPotential K (p+1) -
        centeredPotential K p := by
  have h := unified_equationIII_graph_closed (4^K) 3 p
  norm_num at h
  dsimp [physicalUDifference, centeredPotential]
  linarith

/-- The terminal potential is *literally* 0 for all K at and
beyond the finite physical end. -/
theorem centered_terminal_zero (K p : Nat)
    (hp : (4:Nat)^(K+4) ≤ p) :
    centeredPotential K p = 0 := by
  simp only [centeredPotential, physical_terminal_u_potential K p hp]
  omega

/-- ALL-K, ALL-depth compensated two-scale conservation. This is
an exact mathematical identity, not a hypothesis or scan. -/
theorem centered_exact_vertical_telescope
    (K b n : Nat) :
    Finset.sum (Finset.range n) (fun j =>
        (((3^j : Nat) : Int)) *
        (physicalUDifference K (b+j) + 630)) =
      (((3^n : Nat) : Int)) * centeredPotential K (b+n) -
        centeredPotential K b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hs := centered_equationIII K (b+n)
      have hi : b+(n+1) = (b+n)+1 := by omega
      rw [Finset.sum_range_succ, ih, hi, pow_succ]
      push_cast
      rw [hs]
      ring

/-- Closed all-K physical U-budget from a starting row b to
ANY height H above the true terminal point. The retained charges
and compensation are all real arithmetic source observables.
No infinite summation, hidden support assumption or sorryAx. -/
theorem physical_full_word_compensated_budget
    (K b H : Nat) (hheight : b ≤ H)
    (hterminal : (4:Nat)^(K+4) ≤ H) :
    Finset.sum (Finset.range (H-b)) (fun j =>
        (((3^j : Nat) : Int)) *
        (physicalUDifference K (b+j) + 630)) =
      - centeredPotential K b := by
  have h := centered_exact_vertical_telescope K b (H-b)
  have he : b+(H-b) = H := by omega
  rw [he, centered_terminal_zero K H hterminal] at h
  simpa using h

#print axioms centered_equationIII
#print axioms centered_terminal_zero
#print axioms centered_exact_vertical_telescope
#print axioms physical_full_word_compensated_budget

end GST406CenteredUConservation
