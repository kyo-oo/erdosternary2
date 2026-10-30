import GST406CenteredUConservation
import GSTGraphV2PerfectPowerBlockProbe
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST direct collision: exact local-sign obstruction at the GENUINE 4^8

A child physical Happy at row 4 does not create an all-depth
monotonicity of the signed right-minus-64-left U derivative, even
while the right edge is BAD through rows 3..8. The right edge
is 4^11, itself a true perfect power, and eventually it has
a Happy row at p=10.

This is NOT a counterexample to the original 406 theorem.
It is a counterexample to a false finite-window comparison
that would have been needed to close the original
power_three_step_collision with only the current signed
Equation III and window inequalities.
-/

namespace GST406PhysicalULocalSign

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GST406CenteredUConservation

/-- An actual child power has a Happy cell at p=4 and its
parent 4^11 stays BAD through the full window p=3..8. -/
theorem genuine_power_prefix_right_bad :
    HappyCell
      (graph (4^8) 0 4).seven.carry
      (graph (4^8) 0 4).seven.digit ∧
    (∀ p : Fin 6,
      ¬ HappyCell
        (graph (4^8) 3 (3+p.val)).seven.carry
        (graph (4^8) 3 (3+p.val)).seven.digit) := by
  decide

/-- Exact, competing phase signs in the real K=8, K+3=11
width-three rectangle. Both facts are compatible with
exact power-width conservation and the U flux equation. -/
theorem genuine_power_phase_window_signs :
    graphPhaseWindow (4^8) 0 3 2 = 2 ∧
    graphPhaseWindow (4^8) 3 3 2 = -4 := by
  decide

/-- Before the right edge ever hits, the very same true power
exhibits both a positive and a negative local U derivative.
Therefore no monotonicity lemma follows just from a BAD right prefix. -/
theorem genuine_power_u_sign_reversal :
    physicalUDifference 8 4 = 518 ∧
    physicalUDifference 8 8 = -1536 ∧
    centeredPotential 8 4 = 130 ∧
    centeredPotential 8 5 = 426 := by
  decide

/-- The right edge DOES later become Happy (p=10), so this
local sign obstruction must never be misreported as a
counterexample to the infinite BAD hypothesis. -/
theorem genuine_power_right_later_happy :
    HappyCell
      (graph (4^8) 3 10).seven.carry
      (graph (4^8) 3 10).seven.digit := by
  decide

#print axioms genuine_power_prefix_right_bad
#print axioms genuine_power_phase_window_signs
#print axioms genuine_power_u_sign_reversal
#print axioms genuine_power_right_later_happy

end GST406PhysicalULocalSign
