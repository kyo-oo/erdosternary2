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

/-- Direct next-sheet relocation constructor.  Starting from the exact
production source Happy hypothesis, a killing-prefix certificate for exponent
`K+1` constructs an actual physical Happy row on `4^(K+1)`.  The source
hypothesis is converted only to its arithmetic `CommonTwo K` content; no
navigation or witness transport is used.  This isolates the remaining Task 3.3
burden to producing the target exponent's prefix certificate. -/
theorem source_happy_and_next_prefix_kill_to_relocated_happy
    (K sourceRow p : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (heq :
      GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix (K+1) p)) (p+1) =
        GSTFourPowerDirectResidue.digit3
          (4^((exponentPrefix (K+1) p)+1)) (p+1))
    (hkill :
      exponentTrit (K+1) p =
        2 - GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix (K+1) p)) (p+1)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  exact prefix_killing_trit_to_physical_happy (K+1) p heq hkill

#check prefix_killing_trit_to_physical_happy
#check source_happy_and_next_prefix_kill_to_relocated_happy
#print axioms prefix_killing_trit_to_physical_happy
#print axioms source_happy_and_next_prefix_kill_to_relocated_happy

end GSTFourPowerPrefixKillingHappy
