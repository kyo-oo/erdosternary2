import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2UnifiedVerticalTelescope
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteFourPowerNavigation

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

/-- Exact width-three pure-power conservation at the production cut. -/
theorem power_width_three_exact_conservation (K q : Nat) :
    64 * (graph (4^K) 0 (3+q)).seven.digit +
        wideCarry 64 (4^K) (3+q) =
      (graph (4^K) 3 (3+q)).seven.digit +
        3 * wideCarry 64 (4^K) ((3+q)+1) := by
  have h := exactPowerRectangle_conservation 1 2 K q
  norm_num [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    Nat.add_assoc, Nat.pow_add] at h ⊢
  simpa [Nat.mul_comm] using h

/-- On a physical Happy cell the exact handwritten-U jump is strictly negative. -/
theorem gst_u_jump_negative_of_happy_local
    (C d : Nat) (h : HappyCell C d) :
    gstUJumpExact C d < 0 := by
  rcases h with ⟨rfl, h0 | h3⟩
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- Every non-Happy physical cell has nonnegative exact handwritten-U jump. -/
theorem gst_u_jump_nonnegative_of_not_happy_local
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    0 ≤ gstUJumpExact C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- A disappearing child Happy gate creates a strictly positive exact U defect. -/
theorem power_width_three_u_derivative_positive
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRight : ¬ HappyCell
      (graph (4^K) 3 (3+q)).seven.carry
      (graph (4^K) 3 (3+q)).seven.digit) :
    0 <
      3 * potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 ((3+q)+1)).core -
        potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 (3+q)).core := by
  have hEq := unified_equationIII_graph_closed (4^K) 3 (3+q)
  have hChildNeg := gst_u_jump_negative_of_happy_local
    (graph (4^K) 0 (3+q)).seven.carry
    (graph (4^K) 0 (3+q)).seven.digit hChild
  have hRightNonneg := gst_u_jump_nonnegative_of_not_happy_local
    (graph (4^K) 3 (3+q)).seven.carry
    (graph (4^K) 3 (3+q)).seven.digit
    (graph_carry_lt_four (4^K) 3 (3+q))
    (graph_digit_lt_three (4^K) 3 (3+q)) hRight
  rw [← hEq]
  norm_num
  nlinarith

/-- Power-specific three-step collision.  This is the only induction seam. -/
theorem power_three_step_collision
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  let E := 4^K
  let N : Nat := 3
  let b : Nat := 3

  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hleftAbs : HappyCell
      (graph 1 K (b+q)).seven.carry
      (graph 1 K (b+q)).seven.digit := by
    have hiff := power_origin_happy_iff K 0 (b+q)
    exact hiff.mp (by simpa [E, b, Nat.add_assoc] using hChild)

  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (K+N) (b+j)).seven.carry
      (graph 1 (K+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := power_origin_happy_iff K N (b+j)
    exact hiff.mpr (by simpa [E, N] using h)

  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hWidth3 := power_width_three_exact_conservation K q
  have hUPositive := power_width_three_u_derivative_positive K q hChild
    (hRightBad q)

  dsimp [E, N, b] at hleft hright hleftAbs hrightAbs hU hWidth3 ⊢
  dsimp [potentialWith, unifiedState] at hUPositive
  trace_state
  omega

/-- From exponent 8 onward a Happy gate exists at a ternary coordinate at least 3. -/
theorem four_power_happy_ge_three (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^k) p) (digit3 (4^k) p) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk11 : 11 ≤ k
      · have hk3 : 8 ≤ k - 3 := by omega
        obtain ⟨p, hp3, hpHappy⟩ := ih (k - 3) (by omega) hk3
        let q := p - 3
        have hpq : 3 + q = p := by
          dsimp [q]
          omega
        have hChild : HappyCell
            (graph (4^(k-3)) 0 (3+q)).seven.carry
            (graph (4^(k-3)) 0 (3+q)).seven.digit := by
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hpq] using hpHappy
        by_contra hno
        have hRightBad : ∀ j, ¬ HappyCell
            (graph (4^(k-3)) 3 (3+j)).seven.carry
            (graph (4^(k-3)) 3 (3+j)).seven.digit := by
          intro j hright
          apply hno
          refine ⟨3+j, by omega, ?_⟩
          have hpow : 4^3 * 4^(k-3) = 4^k := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [← hpow]
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hright
        exact power_three_step_collision (k-3) q hChild hRightBad
      · have hkCases : k = 8 ∨ k = 9 ∨ k = 10 := by omega
        rcases hkCases with rfl | rfl | rfl
        · refine ⟨4, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨7, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨10, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]

/-- A Happy cell is the first branch of the historical creation certificate. -/
theorem happy_to_creation_certificate
    (R p : Nat) (hp : 1 ≤ p)
    (hHappy : HappyCell (carry4 R p) (digit3 R p)) :
    R / 3^p % 3 = 2 ∧
      ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
        R / 3^(p+1) % 3 = 2)) := by
  rcases hHappy with ⟨hd, hC⟩
  constructor
  · simpa [digit3] using hd
  · left
    change carry4 R p % 3 = 0
    rcases hC with h0 | h3
    · simp [h0]
    · simp [h3]

/-- Universal replacement for the broken recursive `h_creation_for_4pow`. -/
theorem gst_four_power_navigation_universal
    (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧
        (4^k) / 3^(p+1) % 3 = 2)) := by
  by_cases hk8 : 8 ≤ k
  · obtain ⟨p, hp3, hHappy⟩ := four_power_happy_ge_three k hk8
    obtain ⟨hd, hc⟩ := happy_to_creation_certificate (4^k) p (by omega) hHappy
    exact ⟨p, by omega, hd, hc⟩
  · have hkCases : k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hkCases with rfl | rfl | rfl
    · refine ⟨2, by decide, ?_⟩
      norm_num
    · refine ⟨2, by decide, ?_⟩
      norm_num
    · exact (hk7 rfl).elim

#print axioms power_width_three_exact_conservation
#print axioms power_width_three_u_derivative_positive
#print axioms power_three_step_collision
#print axioms four_power_happy_ge_three
#print axioms gst_four_power_navigation_universal

end GSTInfiniteFourPowerNavigation
