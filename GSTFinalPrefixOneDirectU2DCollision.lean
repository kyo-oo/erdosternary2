import GSTFinalResidualConnector
import GSTU2DSharpCrossingBlock
import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneDirectU2DCollision

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
open GSTU2DExactCrossingCharge
open GSTFinalResidualConnector

private def collisionC (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.carry

private def collisionD (s n : Nat) : Nat → Nat → Nat :=
  fun t p => (graph (residualEnergy s 1 n) t (s + 2 + p)).seven.digit

theorem residualWidth_pos_of_s_pos
    (s : Nat) (hs : 1 ≤ s) : 1 ≤ residualWidth s := by
  unfold residualWidth
  exact Nat.one_le_pow _ _ (by decide)

theorem residual_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (residualEnergy s 1 n) 0 (s+2)).seven.carry = 0 := by
  let E := residualEnergy s 1 n
  let b := s + 2
  have hmod : E % 3^b = 1 := by
    have h := pow4_scaled_mod_next (s+1) n
    simpa [E, b, residualEnergy, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  have hc : carry4 E b = 0 := by
    unfold carry4
    rw [hmod]
    apply Nat.div_eq_of_lt
    have hb27 : 27 ≤ 3^b := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b]; omega)
    omega
  simpa [E, b, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

theorem collision_rectangle_exact
    (s n K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseCrossCode (fun t => collisionC s n t p)
          (fun t => collisionD s n t p) (residualWidth s)) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (collisionD s n (residualWidth s) p) -
            (((4^(residualWidth s) : Nat) : Int)) *
              digitPotential (collisionD s n 0 p) +
            84 * reverseSurviveCode (fun t => collisionC s n t p)
              (fun t => collisionD s n t p) (residualWidth s))) +
      reverseCarryCode (fun t => collisionC s n t 0) (residualWidth s) -
        (((3^K : Nat) : Int)) *
          reverseCarryCode (fun t => collisionC s n t K) (residualWidth s) := by
  apply reverseCrossRectangle_exact
  intro t p ht hp
  exact ⟨graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p),
    graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p),
    (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1,
    by
      simpa [collisionC, Nat.add_assoc] using
        (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).2⟩

theorem canonical_right_bad_forces_weighted_cross_nonpositive
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit) :
    weightedCrossPrefix (collisionC s n) (collisionD s n)
      (residualWidth s) (q+1) ≤ 0 := by
  let E := residualEnergy s 1 n
  let N := residualWidth s
  let b := s + 2
  have hBaseCarryZero : (graph E 0 b).seven.carry = 0 := by
    simpa [E, b] using residual_base_carry_zero s n hs
  have hController :
      GSTV2.InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control E N b hBaseCarryZero
    intro j
    simpa [E, N, b, Nat.add_assoc] using hRightBad j
  have hRightLocal : ∀ j,
      crossDensity (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit ≤ 0 := by
    intro j
    exact crossDensity_nonpositive_of_not_happy
      (graph E N (b+j)).seven.carry (graph E N (b+j)).seven.digit
      (graph_carry_lt_four E N (b+j)) (graph_digit_lt_three E N (b+j))
      (by simpa [E, N, b, Nat.add_assoc] using hRightBad j)
  have hRightPrefix :
      Finset.sum (Finset.range (q+1)) (fun p =>
        (((3^p : Nat) : Int)) * crossDensity
          (graph E N (b+p)).seven.carry (graph E N (b+p)).seven.digit) ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hRightLocal p)
  have hRect := collision_rectangle_exact s n (q+1)
  dsimp [collisionC, collisionD, E, N, b] at hRect ⊢
  trace_state
  omega

theorem canonical_perfect_power_block_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  obtain ⟨q, hChild⟩ :=
    residual_child_witness_to_left_happy s 1 n hs (by decide) hchild
  have hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit :=
    residual_bad_trace_to_right_bad s 1 n hs (by decide) hBad
  have hPositive :
      0 < weightedCrossPrefix (collisionC s n) (collisionD s n)
        (residualWidth s) (q+1) := by
    apply weightedCrossPrefix_positive_of_top_leading_happy
    · exact residualWidth_pos_of_s_pos s hs
    · intro t p ht hp
      exact graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p)
    · intro t p ht hp
      exact graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p)
    · intro t p ht hp
      exact (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1
    · simpa [collisionC, collisionD, Nat.add_assoc] using hChild
  have hNonpositive :=
    canonical_right_bad_forces_weighted_cross_nonpositive s n q hs hn hRightBad
  omega

theorem gst_prefix_one_information_bad_descends_u2d
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  exact canonical_perfect_power_block_collision s n hs hn hchild hBad

#check residual_base_carry_zero
#check collision_rectangle_exact
#check canonical_right_bad_forces_weighted_cross_nonpositive
#check canonical_perfect_power_block_collision
#check gst_prefix_one_information_bad_descends_u2d
#print axioms canonical_perfect_power_block_collision
#print axioms gst_prefix_one_information_bad_descends_u2d

end GSTFinalPrefixOneDirectU2DCollision
