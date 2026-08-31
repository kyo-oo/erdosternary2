import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalTerminalExtinctionProbe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalSignedPrefixBridge

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalTerminalExtinctionProbe
open GSTGraphV2CoupledUFlux

/-- Canonical specialization of the exact signed U-prefix certificate.
The child is the seed-zero canonical tail; the all-bad right boundary is the
seed-one canonical parent. -/
theorem canonical_seeded_u_gap_positive
    (s n q : Nat)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    0 < Finset.sum (Finset.range (q+1)) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (GSTV2.affineCarry 1 (canonicalParentTail s n) j)
            (GSTV2.digit (canonicalParentTail s n) j) -
          (((4^(3^s) : Nat) : Int)) *
            gstUJumpExact
              (GSTV2.affineCarry 0 (canonicalChildTail s n) j)
              (GSTV2.digit (canonicalChildTail s n) j))) := by
  apply seeded_coupled_weighted_u_gap_positive
  · positivity
  · have h := (seedHappy_zero_iff (canonicalChildTail s n) q).1 hChild
    simpa [GSTV2.Happy, HappyCell, GSTV2.naturalCarry, GSTV2.digit,
      carry4, digit3] using h
  · intro j hHappy
    apply hRightBad j
    rw [seedHappy_one_iff]
    simpa [GSTV2.Happy, HappyCell,
      GSTGraphV2InfiniteControl.seededCarry,
      GSTV2.affineCarry, GSTV2.digit, digit3] using hHappy

#check canonical_seeded_u_gap_positive
#print axioms canonical_seeded_u_gap_positive

end GSTGraphV2CanonicalSignedPrefixBridge
