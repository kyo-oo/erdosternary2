import GSTGraphV2InfiniteControllerBridge
import GSTPerfectPowerTailNavigation
import GSTGraphV2HandwrittenOmegaUBlock

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFinalPrefixOneStep6Infinite

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTU2DExactCrossingCharge
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2HandwrittenOmegaUBlock
open GSTPerfectPowerTailNavigation

private def infE (s n : Nat) : Nat := residualEnergy s 1 n
private def infN (s : Nat) : Nat := residualWidth s
private def infB (s : Nat) : Nat := s + 2

/-- The canonical child starts the all-depth controller with the true zero carry. -/
theorem infinite_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (infE s n) 0 (infB s)).seven.carry = 0 := by
  let E := infE s n
  let b := infB s
  let T := canonicalTail (s+1) n
  have hE : E = 1 + 3^b * T := by
    have h := canonical_tail_decomposition (s+1) n
    simpa [E, b, T, infE, infB, residualEnergy, Nat.add_assoc] using h
  have hb : 1 < 3^b := by
    have h9 : 9 ≤ 3^b := by
      rw [show (9 : Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b, infB]; omega)
    omega
  have hmod : E % 3^b = 1 := by
    rw [hE]
    have hmul : (3^b * T) % 3^b = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
    calc
      (1 + 3^b * T) % 3^b = (1 % 3^b + (3^b * T) % 3^b) % 3^b := Nat.add_mod _ _ _
      _ = (1 % 3^b) % 3^b := by rw [hmul, Nat.add_zero]
      _ = 1 % 3^b := Nat.mod_mod_of_dvd _ (dvd_refl (3^b))
      _ = 1 := Nat.mod_eq_of_lt hb
  have hc : carry4 E b = 0 := by
    unfold carry4
    rw [hmod]
    apply Nat.div_eq_of_lt
    have hb27 : 27 ≤ 3^b := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [b, infB]; omega)
    omega
  simpa [E, b, infE, infB, graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hc

/-- All-depth parent badness is packaged once as one InfiniteBadCoupledControl. -/
theorem canonical_infinite_bad_control
    (s n : Nat) (hs : 1 ≤ s)
    (hRightBad : ∀ j,
      ¬ HappyCell
        (graph (infE s n) (infN s) (infB s + j)).seven.carry
        (graph (infE s n) (infN s) (infB s + j)).seven.digit) :
    GSTV2.InfiniteBadCoupledControl
      (4^(infN s)) (graphCoupledState (infE s n) (infN s) (infB s)) := by
  apply graph_infinite_bad_control
  · exact infinite_base_carry_zero s n hs
  · intro j
    exact hRightBad j

/-- The same canonical physical rectangle carries the stronger all-depth Past/Future ledger. -/
theorem canonical_infinite_ledger
    (s n : Nat) :
    GSTV2.InfiniteCoupledLedger
      (4^(infN s)) (graphCoupledState (infE s n) (infN s) (infB s)) := by
  apply GSTV2.infinite_coupled_ledger
  · positivity
  · exact graphCoupledState_invariant (infE s n) (infN s) (infB s)

/-- Atomic all-depth synchronization: controller orbit equals the physical graph state at every K. -/
theorem canonical_controller_graph_all_depth
    (s n : Nat) : ∀ K,
    GSTV2.coupledOrbit (4^(infN s))
        (graphCoupledState (infE s n) (infN s) (infB s)) K =
      graphCoupledState (infE s n) (infN s) (infB s + K) := by
  intro K
  exact graphCoupledOrbit_exact (infE s n) (infN s) (infB s) K

/-- Atomic all-depth synchronization law: no terminal height and no bounded horizon. -/
theorem canonical_past_future_synchronized_all_depth
    (s n : Nat) : ∀ K,
    let initial := graphCoupledState (infE s n) (infN s) (infB s)
    initial.parentPast (4^(infN s)) K +
        3^K * (GSTV2.coupledOrbit (4^(infN s)) initial K).childResidue =
      initial.childResidue + (4^(infN s)) * initial.childPast K := by
  intro K
  exact (canonical_infinite_ledger s n).pastSynchronized K

/-- The exact Step-6 linear combination of crossing and mixed charge has no
microscopic SURVIVE source.  This is the algebraic atom used before coupling
the rectangle to the all-depth controller ledger. -/
theorem cross_mixed_survive_cancel
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    2 * crossDensity C d - 3 * mixedDensity C d =
      2 *
        (digitPotential (outDigit C d) - 4 * digitPotential d +
          carryPotentialX C - 3 * carryPotentialX (nextCarry C d)) -
      3 *
        (infoPotential (outDigit C d) - infoPotential d +
          7 * carryPotential C - 21 * carryPotential (nextCarry C d)) := by
  rw [crossDensity, mixed_cell_emergence C d hC hd]
  ring

#check infinite_base_carry_zero
#check canonical_infinite_bad_control
#check canonical_infinite_ledger
#check canonical_controller_graph_all_depth
#check canonical_past_future_synchronized_all_depth
#check cross_mixed_survive_cancel
#print axioms infinite_base_carry_zero
#print axioms canonical_infinite_bad_control
#print axioms canonical_infinite_ledger
#print axioms canonical_controller_graph_all_depth
#print axioms canonical_past_future_synchronized_all_depth
#print axioms cross_mixed_survive_cancel

end GSTFinalPrefixOneStep6Infinite