import GSTFourPowerPrefixKillingHappy
import GSTFourPowerDirectResidue729

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace GSTFourPowerRowSixPhysicalRelocation

open GSTFourPowerDirectHappyBridge

/-- Row six extends fresh production to all 122 exact overlap classes modulo 729. The target classifier supplies literal digit-2 facts at row six; the direct CommonTwo-to-Happy bridge constructs an actual relocated physical Happy row. -/
theorem next_mod_sevenhundredtwentynine_row_six_relocated_happy
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : GSTFourPowerDirectResidue729.RowSixClass ((K+1) % 729)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  have hrow :=
    GSTFourPowerDirectResidue729.row_six_overlap_of_mod729_classes (K+1) hNext
  have hTargetCommon : CommonTwo (K+1) := ⟨6, by norm_num, hrow.1, hrow.2⟩
  exact commonTwo_to_physical_happy_row (K+1) hTargetCommon

#check next_mod_sevenhundredtwentynine_row_six_relocated_happy
#print axioms next_mod_sevenhundredtwentynine_row_six_relocated_happy

end GSTFourPowerRowSixPhysicalRelocation
