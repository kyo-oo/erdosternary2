import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectExistenceNoAxiom

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerHappyGeThreeClean

/-- Clean public provider for the physical Happy-row theorem from exponent eight onward.
This file does not mutate the monolith and does not introduce any axiom boundary; it
only re-exports the candidate theorem so CI can audit its kernel dependency surface. -/
theorem four_power_happy_ge_three_clean
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  simpa using GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK

/-- No-axiom direct existence obtained by feeding the clean Happy-row provider into
the already isolated bridge. -/
theorem fourPowerDirectExistence_noAxiom :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  exact
    GSTFourPowerDirectExistenceNoAxiom.fourPowerDirectExistence_from_physical_happy_ge_three
      four_power_happy_ge_three_clean

#print axioms four_power_happy_ge_three_clean
#print axioms fourPowerDirectExistence_noAxiom

end GSTFourPowerHappyGeThreeClean
