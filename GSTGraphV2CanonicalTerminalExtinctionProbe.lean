import GSTGraphV2CanonicalEscape
import GSTGraphV2HandwrittenAnchoredCocycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalTerminalExtinctionProbe

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalDescentOntology
open GSTGraphV2HandwrittenAnchoredCocycle

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
This is the kernel-level inequality the final collision proof must telescope. -/
theorem canonical_width_u_derivative_positive
    (s n p : Nat)
    (hLeft : HappyCell
      (graph 1 (3^(s+1) * n) p).seven.carry
      (graph 1 (3^(s+1) * n) p).seven.digit)
    (hRight : ¬ HappyCell
      (graph 1 (3^(s+1) * n + 3^s) p).seven.carry
      (graph 1 (3^(s+1) * n + 3^s) p).seven.digit) :
    0 <
      3 * GSTGraphV2HandwrittenAnchoredCocycle.graphUPotential
        1 (3^(s+1) * n) (3^s) (p+1)
      - GSTGraphV2HandwrittenAnchoredCocycle.graphUPotential
        1 (3^(s+1) * n) (3^s) p := by
  simpa [Nat.add_assoc] using
    graph_u_derivative_positive_of_child_happy_right_bad
      1 (3^(s+1) * n) (3^s) p hLeft hRight

#check physical_happy_forces_negative_u_jump
#check physical_bad_forces_nonnegative_u_jump
#check canonical_width_u_derivative_positive
#print axioms physical_happy_forces_negative_u_jump
#print axioms physical_bad_forces_nonnegative_u_jump
#print axioms canonical_width_u_derivative_positive

end GSTGraphV2CanonicalTerminalExtinctionProbe
