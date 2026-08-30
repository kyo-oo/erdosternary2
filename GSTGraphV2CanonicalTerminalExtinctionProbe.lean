import GSTGraphV2HandwrittenAnchoredCocycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalTerminalExtinctionProbe

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2CoupledUFlux
open GSTGraphV2UnifiedPowerRectangle

/-- A concrete bridge from a physical Happy Graph-V2 cell to the strict
negative U-jump used by the handwritten vertical conservation law. -/
theorem physical_happy_forces_negative_u_jump
    (E t p : Nat)
    (hH : HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    gstUJumpExact
      (graph E t p).seven.carry
      (graph E t p).seven.digit < 0 := by
  exact (happy_iff_gst_u_jump_negative _ _
    (graph_carry_lt_four E t p)
    (graph_digit_lt_three E t p)).1 hH

/-- A physical bad Graph-V2 cell contributes a nonnegative U-jump. -/
theorem physical_bad_forces_nonnegative_u_jump
    (E t p : Nat)
    (hB : ¬ HappyCell
      (graph E t p).seven.carry
      (graph E t p).seven.digit) :
    0 ≤ gstUJumpExact
      (graph E t p).seven.carry
      (graph E t p).seven.digit := by
  exact gst_u_jump_nonnegative_of_not_happy _ _
    (graph_carry_lt_four E t p)
    (graph_digit_lt_three E t p) hB

/-- The exact one-row U derivative across a canonical width is strictly
positive whenever the left endpoint is Happy and the right endpoint is bad.
No width-three transport and no collision theorem is imported here. -/
theorem canonical_width_u_derivative_positive
    (s n p : Nat)
    (hLeft : HappyCell
      (graph 1 (3^(s+1) * n) p).seven.carry
      (graph 1 (3^(s+1) * n) p).seven.digit)
    (hRight : ¬ HappyCell
      (graph 1 (3^(s+1) * n + 3^s) p).seven.carry
      (graph 1 (3^(s+1) * n + 3^s) p).seven.digit) :
    0 <
      3 * graphUPotential
        1 (3^(s+1) * n) (3^s) (p+1)
      - graphUPotential
        1 (3^(s+1) * n) (3^s) p := by
  simpa [Nat.add_assoc] using
    graph_u_derivative_positive_of_child_happy_right_bad
      1 (3^(s+1) * n) (3^s) p hLeft hRight

/-- If every carry in a finite horizontal observation vanishes, the retained
reverse-base-four carry word is exactly zero. -/
theorem carryWord_eq_zero_of_window_neutral
    (E p start : Nat) : ∀ N : Nat,
    (∀ j, j < N → (graph E (start+j) p).seven.carry = 0) →
      carryWord E p start N = 0 := by
  intro N h
  induction N with
  | zero => simp [carryWord]
  | succ N ih =>
      rw [carryWord]
      have hprev : ∀ j, j < N → (graph E (start+j) p).seven.carry = 0 := by
        intro j hj
        exact h j (by omega)
      rw [ih hprev]
      have hlast := h N (by omega)
      simpa using hlast

/-- A finite horizontal U packet on a completely neutral row is not zero:
the charge normalization leaves the exact vacuum baseline `5 - 4^N * 5`.
Keeping this term is essential for a sound terminal telescope. -/
theorem graph_u_potential_vacuum_baseline_of_window_neutral
    (E start N p : Nat)
    (hLeft : (graph E start p).seven.carry = 0)
    (hRight : (graph E (start+N) p).seven.carry = 0)
    (hWindow : ∀ j, j < N →
      (graph E (start+j) p).seven.carry = 0) :
    graphUPotential E start N p =
      5 - (((4^N : Nat) : Int)) * 5 := by
  have hWord : carryWord E p start N = 0 :=
    carryWord_eq_zero_of_window_neutral E p start N hWindow
  unfold graphUPotential
  rw [hLeft, hRight, hWord]
  norm_num [gstUChargeExact]

/-- Direct arithmetic neutralization of a unit-sheet cell above its finite
x4 energy.  Both physical coordinates are zero, not merely non-Happy. -/
theorem unit_graph_cell_neutral_of_pow_lt
    (t p : Nat) (hpow : 4^(t+1) < 3^p) :
    (graph 1 t p).seven.carry = 0 ∧
      (graph 1 t p).seven.digit = 0 := by
  have ht : 4^t < 3^p := by
    have hle : 4^t ≤ 4^(t+1) := by
      rw [Nat.pow_succ]
      omega
    omega
  constructor
  · simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex, carry4]
    rw [Nat.mul_one, Nat.mod_eq_of_lt ht]
    have hshape : 4 * 4^t = 4^(t+1) := by
      rw [Nat.pow_succ]
      ring
    rw [hshape, Nat.div_eq_of_lt hpow]
  · simp only [graph, cell, GSTCanonicalSevenAxisBridge.vertex, digit3]
    rw [Nat.mul_one, Nat.div_eq_of_lt ht]

#check physical_happy_forces_negative_u_jump
#check physical_bad_forces_nonnegative_u_jump
#check canonical_width_u_derivative_positive
#check carryWord_eq_zero_of_window_neutral
#check graph_u_potential_vacuum_baseline_of_window_neutral
#check unit_graph_cell_neutral_of_pow_lt
#print axioms physical_happy_forces_negative_u_jump
#print axioms physical_bad_forces_nonnegative_u_jump
#print axioms canonical_width_u_derivative_positive
#print axioms carryWord_eq_zero_of_window_neutral
#print axioms graph_u_potential_vacuum_baseline_of_window_neutral
#print axioms unit_graph_cell_neutral_of_pow_lt

end GSTGraphV2CanonicalTerminalExtinctionProbe
