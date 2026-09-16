import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerPrefixKillingHappy

open GSTFourPowerDirectExistence
open GSTFourPowerExponentTritObstruction
open GSTFourPowerDirectHappyBridge

/-- A prefix equality together with the actual killing exponent trit constructs
an honest common-two row `p+1`, hence an actual physical Happy row there.
This is the direct current-production relocation mechanism: no navigation,
packet transport, surrogate witness, or contradiction principle is used. -/
theorem prefix_killing_trit_to_physical_happy
    (K p : Nat)
    (heq :
      GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3
          (4^((exponentPrefix K p)+1)) (p+1))
    (hkill :
      exponentTrit K p =
        2 - GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix K p)) (p+1)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) q)
        (GSTCanonicalTailStateIso.digit3 (4^K) q) := by
  have hrow :=
    (row_common_two_iff_prefix_killing_trit K p).2 ⟨heq, hkill⟩
  have hcommon : CommonTwo K := by
    exact ⟨p+1, by omega, hrow.1, hrow.2⟩
  exact commonTwo_to_physical_happy_row K hcommon

#check prefix_killing_trit_to_physical_happy
#print axioms prefix_killing_trit_to_physical_happy

end GSTFourPowerPrefixKillingHappy
