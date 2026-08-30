import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2UnifiedVerticalTelescope
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2TransparentWidthThree

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTFinalPurePowerResidueTransplant
open GSTU2DEventTransport

/-- Transparent width-three conservation.  This is the literal `B = 64`
instance of the generic quotient/remainder strip law; it does not use the
historical `exactPowerRectangle_conservation` dependency. -/
theorem power_width_three_exact_conservation_at_cut
    (K b q : Nat) :
    64 * (graph (4^K) 0 (b+q)).seven.digit +
        wideCarry 64 (4^K) (b+q) =
      (graph (4^K) 3 (b+q)).seven.digit +
        3 * wideCarry 64 (4^K) ((b+q)+1) := by
  have h := stripConservation_exact 64 (4^K) (b+q)
  norm_num [wideDigit, graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.digit3] at h ⊢
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- On a physical Happy cell the exact handwritten-U jump is strictly negative. -/
theorem u_jump_negative_of_happy
    (C d : Nat) (h : HappyCell C d) :
    gstUJumpExact C d < 0 := by
  rcases h with ⟨rfl, h0 | h3⟩
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- Every non-Happy physical cell has nonnegative exact handwritten-U jump. -/
theorem u_jump_nonnegative_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    0 ≤ gstUJumpExact C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- If a Happy cell disappears three x4 columns later, Equation III produces
strictly positive vertical U derivative at that row. -/
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
  have hChildNeg := u_jump_negative_of_happy
    (graph (4^K) 0 (b+q)).seven.carry
    (graph (4^K) 0 (b+q)).seven.digit hChild
  have hRightNonneg := u_jump_nonnegative_of_not_happy
    (graph (4^K) 3 (b+q)).seven.carry
    (graph (4^K) 3 (b+q)).seven.digit
    (graph_carry_lt_four (4^K) 3 (b+q))
    (graph_digit_lt_three (4^K) 3 (b+q)) hRight
  rw [← hEq]
  norm_num
  nlinarith

/-- Transparent three-column collision at an arbitrary vertical cut. -/
theorem power_three_step_collision_at_cut
    (K b q : Nat)
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
  have hWidth3 := power_width_three_exact_conservation_at_cut K b q
  have hUPositive := power_width_three_u_derivative_positive_at_cut K b q
    hChild (hRightBad q)

  dsimp [E, N] at hleft hright hleftAbs hrightAbs hU ⊢
  omega

/-- One Happy gate propagates across one transparent width-three power block. -/
theorem power_happy_add_three_at_cut
    (K b q : Nat)
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
  apply power_three_step_collision_at_cut K b q
  · simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hChild
  · exact hRightBad

/-- Iterate the same transparent three-column mechanism through `m` blocks. -/
theorem power_happy_add_three_mul_at_cut
    (K b q m : Nat)
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
        power_happy_add_three_at_cut (K + 3*m) b j hj
      refine ⟨j', ?_⟩
      convert hj' using 1 <;> congr 2 <;> omega

#check power_width_three_exact_conservation_at_cut
#check power_three_step_collision_at_cut
#check power_happy_add_three_mul_at_cut
#print axioms power_width_three_exact_conservation_at_cut
#print axioms power_three_step_collision_at_cut
#print axioms power_happy_add_three_mul_at_cut

end GSTGraphV2TransparentWidthThree
