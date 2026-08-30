import GSTGraphV2PerfectPowerBlockProbe
import GSTU2DPureDivergence83
import GSTGraphV2CanonicalDescentOntology
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PerfectPowerBlockCollision

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTGraphV2CoupledUFlux
open GSTU2DPureDivergence83
open GSTFinalPurePowerResidueTransplant
open GSTInfiniteFourPowerNavigation

/-!
A second phase chart selected by the twelve physical cells.  Unlike the
SURVIVE-aware phase density, this is a *pure* x4/base3 divergence: there is no
interior source term.  Its only positive physical cells are the two Happy
states.  It is used below as a boundary certificate for the canonical
perfect-power strip.
-/

def blockDigitPotential (d : Nat) : Int :=
  if d = 0 then -64 else if d = 1 then -8 else 0

def blockCarryPotential (C : Nat) : Int :=
  if C = 0 then 21 else if C = 1 then 7 else if C = 2 then -1 else -3

def blockDensity (C d : Nat) : Int :=
  blockDigitPotential (outDigit C d) - blockDigitPotential d +
    blockCarryPotential C - 3 * blockCarryPotential (nextCarry C d)

theorem blockDensity_physical_table :
    blockDensity 0 0 = -42 ∧ blockDensity 0 1 = 0 ∧ blockDensity 0 2 = 24 ∧
    blockDensity 1 0 = 0 ∧ blockDensity 1 1 = -6 ∧ blockDensity 1 2 = -48 ∧
    blockDensity 2 0 = 0 ∧ blockDensity 2 1 = -54 ∧ blockDensity 2 2 = 0 ∧
    blockDensity 3 0 = -24 ∧ blockDensity 3 1 = 0 ∧ blockDensity 3 2 = 6 := by
  decide

theorem happy_iff_blockDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < blockDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [HappyCell, blockDensity, blockDigitPotential,
      blockCarryPotential, outDigit, nextCarry]

theorem blockDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    blockDensity C d ≤ 0 := by
  have hiff := happy_iff_blockDensity_positive C d hC hd
  by_contra h
  have hpos : 0 < blockDensity C d := by omega
  exact hbad (hiff.mpr hpos)

/-- Exact vertical telescope of the pure density in one graph column. -/
theorem blockDensity_column_exact
    (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        blockDensity
          (graph E t (b+j)).seven.carry
          (graph E t (b+j)).seven.digit) =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          (blockDigitPotential (graph E (t+1) (b+j)).seven.digit -
           blockDigitPotential (graph E t (b+j)).seven.digit)) +
      blockCarryPotential (graph E t b).seven.carry -
        (((3^K : Nat) : Int)) *
          blockCarryPotential (graph E t (b+K)).seven.carry := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hc := graph_cell_exact E t (b+K)
      rw [blockDensity, hc.1]
      have hcarry :
          nextCarry (graph E t (b+K)).seven.carry
              (graph E t (b+K)).seven.digit =
            (graph E t (b+(K+1))).seven.carry := by
        simpa [Nat.add_assoc] using hc.2
      rw [hcarry, Nat.pow_succ]
      push_cast
      ring

/-- All-depth badness makes every finite pure-density observation nonpositive. -/
theorem blockDensity_prefix_nonpositive_of_bad
    (E t b K : Nat)
    (hBad : ∀ j, j < K → ¬ HappyCell
      (graph E t (b+j)).seven.carry
      (graph E t (b+j)).seven.digit) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        blockDensity
          (graph E t (b+j)).seven.carry
          (graph E t (b+j)).seven.digit) ≤ 0 := by
  apply Finset.sum_nonpos
  intro j hj
  have hjK := Finset.mem_range.mp hj
  have hlocal := blockDensity_nonpositive_of_not_happy
    (graph E t (b+j)).seven.carry
    (graph E t (b+j)).seven.digit
    (graph_carry_lt_four E t (b+j))
    (graph_digit_lt_three E t (b+j))
    (hBad j hjK)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlocal

/-- Width-three pure-power conservation at an arbitrary production cut. -/
theorem power_width_three_exact_conservation_at_cut
    (K b q : Nat) (hb : 2 ≤ b) :
    64 * (graph (4^K) 0 (b+q)).seven.digit +
        wideCarry 64 (4^K) (b+q) =
      (graph (4^K) 3 (b+q)).seven.digit +
        3 * wideCarry 64 (4^K) ((b+q)+1) := by
  have h := exactPowerRectangle_conservation (b-2) 2 K q
  have hcut : b - 2 + 2 + q = b + q := by omega
  norm_num [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    Nat.add_assoc, Nat.pow_add] at h ⊢
  simpa [hcut, Nat.mul_comm] using h

/-- A disappearing child Happy gate at any cut creates a positive exact
width-three U defect. -/
theorem power_width_three_u_derivative_positive_at_cut
    (K b q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (b+q)).seven.carry
      (graph (4^K) 0 (b+q)).seven.digit)
    (hRight : ¬ HappyCell
      (graph (4^K) 3 (b+q)).seven.carry
      (graph (4^K) 3 (b+q)).seven.digit) :
    0 <
      3 * potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 ((b+q)+1)).core -
        potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 (b+q)).core := by
  have hEq := unified_equationIII_graph_closed (4^K) 3 (b+q)
  have hChildNeg := gst_u_jump_negative_of_happy_local
    (graph (4^K) 0 (b+q)).seven.carry
    (graph (4^K) 0 (b+q)).seven.digit hChild
  have hRightNonneg := gst_u_jump_nonnegative_of_not_happy_local
    (graph (4^K) 3 (b+q)).seven.carry
    (graph (4^K) 3 (b+q)).seven.digit
    (graph_carry_lt_four (4^K) 3 (b+q))
    (graph_digit_lt_three (4^K) 3 (b+q)) hRight
  rw [← hEq]
  norm_num
  nlinarith

/-- The green width-three collision theorem, lifted to an arbitrary cut. -/
theorem power_three_step_collision_at_cut
    (K b q : Nat) (hb : 2 ≤ b)
    (hChild : HappyCell
      (graph (4^K) 0 (b+q)).seven.carry
      (graph (4^K) 0 (b+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (b+j)).seven.carry
      (graph (4^K) 3 (b+j)).seven.digit) :
    False := by
  let E := 4^K
  let N : Nat := 3
  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, Nat.add_assoc] using hChild
  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, Nat.add_assoc] using hRightBad j
  have hleftAbs : HappyCell
      (graph 1 K (b+q)).seven.carry
      (graph 1 K (b+q)).seven.digit := by
    have hiff := power_origin_happy_iff K 0 (b+q)
    exact hiff.mp (by simpa [E, Nat.add_assoc] using hChild)
  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (K+N) (b+j)).seven.carry
      (graph 1 (K+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := power_origin_happy_iff K N (b+j)
    exact hiff.mpr (by simpa [E, N] using h)
  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hWidth3 := power_width_three_exact_conservation_at_cut K b q hb
  have hUPositive := power_width_three_u_derivative_positive_at_cut K b q
    hChild (hRightBad q)
  dsimp [E, N] at hleft hright hleftAbs hrightAbs hU ⊢
  omega

/-- One certified Happy gate propagates across one width-three power block
without lowering the production cut. -/
theorem power_happy_add_three_at_cut
    (K b q : Nat) (hb : 2 ≤ b)
    (hChild : HappyCell (carry4 (4^K) (b+q)) (digit3 (4^K) (b+q))) :
    ∃ j, HappyCell
      (carry4 (4^(K+3)) (b+j))
      (digit3 (4^(K+3)) (b+j)) := by
  by_contra hnone
  have hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (b+j)).seven.carry
      (graph (4^K) 3 (b+j)).seven.digit := by
    intro j hRight
    apply hnone
    refine ⟨j, ?_⟩
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
      ← Nat.pow_add, Nat.add_comm, Nat.add_assoc] using hRight
  apply power_three_step_collision_at_cut K b q hb
  · simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hChild
  · exact hRightBad

/-- Iteration of the same green width-three mechanism through `m` blocks. -/
theorem power_happy_add_three_mul_at_cut
    (K b q m : Nat) (hb : 2 ≤ b)
    (hChild : HappyCell (carry4 (4^K) (b+q)) (digit3 (4^K) (b+q))) :
    ∃ j, HappyCell
      (carry4 (4^(K + 3*m)) (b+j))
      (digit3 (4^(K + 3*m)) (b+j)) := by
  induction m generalizing q with
  | zero =>
      exact ⟨q, by simpa using hChild⟩
  | succ m ih =>
      obtain ⟨j, hj⟩ := ih q hChild
      obtain ⟨j', hj'⟩ :=
        power_happy_add_three_at_cut (K + 3*m) b j hb hj
      refine ⟨j', ?_⟩
      convert hj' using 1 <;> congr 2 <;> omega

/-- Exact Aug-23 target: a certified child Happy event on the canonical
perfect-power sheet cannot coexist with an all-depth bad right boundary one
`3^s` block later. -/
theorem canonical_perfect_power_block_collision
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit) :
    False := by
  let K := 3^(s+1) * n
  let m := 3^(s-1)
  have hb : 2 ≤ s+2 := by omega
  have hChildPower : HappyCell
      (carry4 (4^K) (s+2+q))
      (digit3 (4^K) (s+2+q)) := by
    simpa [K, canonicalEnergy, graph, cell,
      GSTCanonicalSevenAxisBridge.vertex] using hChild
  obtain ⟨j, hj⟩ :=
    power_happy_add_three_mul_at_cut K (s+2) q m hb hChildPower
  have hwidth : 3 * m = 3^s := by
    dsimp [m]
    rw [show s = (s-1)+1 by omega, Nat.pow_succ]
    ring
  apply hRightBad j
  simpa [K, canonicalEnergy, canonicalWidth, graph, cell,
    GSTCanonicalSevenAxisBridge.vertex, ← Nat.pow_add,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hwidth] using hj

#check blockDensity_physical_table
#check happy_iff_blockDensity_positive
#check blockDensity_column_exact
#check canonical_perfect_power_block_collision
#print axioms blockDensity_column_exact
#print axioms canonical_perfect_power_block_collision

end GSTGraphV2PerfectPowerBlockCollision

-- exact full-field ontology probe trigger: 2026-08-30-b
