import GSTFourPowerDirectHappyBridge
import GSTFourPowerDirectResidue243

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

/-- A real physical Happy row already contains an exact prefix-killing
certificate for its own exponent. -/
theorem physical_happy_exposes_prefix_killing_certificate
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow)) :
    ∃ p : Nat, sourceRow = p+1 ∧
      GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3
          (4^((exponentPrefix K p)+1)) (p+1) ∧
      exponentTrit K p =
        2 - GSTFourPowerDirectResidue.digit3
          (4^(exponentPrefix K p)) (p+1) := by
  obtain ⟨p, rfl⟩ : ∃ p : Nat, sourceRow = p+1 := by
    exact ⟨sourceRow - 1, by omega⟩
  have hcommon : CommonTwo K :=
    physical_happy_to_commonTwo K (p+1) (by omega) hSource
  rcases hcommon with ⟨q, hq, hs, ht⟩
  have hs' : GSTFourPowerDirectResidue.digit3 (4^K) (p+1) = 2 := by
    unfold GSTCanonicalTailStateIso.HappyCell at hSource
    simpa [GSTCanonicalTailStateIso.digit3,
      GSTFourPowerDirectResidue.digit3] using hSource.1
  have hc : GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) (p+1) = 0 ∨
      GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) (p+1) = 3 := by
    unfold GSTCanonicalTailStateIso.HappyCell at hSource
    simpa [GSTCanonicalTailStateIso.carry4,
      GSTFourPowerDirectAdditionCarry.directCarry4] using hSource.2
  have ht4 : GSTFourPowerDirectResidue.digit3 (4 * (4^K)) (p+1) = 2 := by
    rw [GSTFourPowerDirectAdditionCarry.digit3_four_mul, hs']
    rcases hc with hc | hc <;> simp [hc]
  have ht' : GSTFourPowerDirectResidue.digit3 (4^(K+1)) (p+1) = 2 := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht4
  have hcert :=
    (row_common_two_iff_prefix_killing_trit K p).1 ⟨hs', ht'⟩
  exact ⟨p, rfl, hcert.1, hcert.2⟩

/-- Direct next-sheet relocation constructor from a target prefix certificate. -/
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

/-- Exact low-scale target relocation class.  If the next exponent is `5` or
`6 mod 9`, the row-two overlap theorem constructs `CommonTwo (K+1)` and the
direct physical bridge returns an actual Happy row `q ≥ 1`. -/
theorem next_mod_nine_five_or_six_relocated_happy
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 9 = 5 ∨ (K+1) % 9 = 6) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  have hTargetCommon : CommonTwo (K+1) :=
    commonTwo_of_mod9_five_or_six (K+1) hNext
  exact commonTwo_to_physical_happy_row (K+1) hTargetCommon

/-- The next direct residue layer.  For each of the four exact mod-27 target
classes already certified by row three, construct the relocated physical Happy
row directly on `4^(K+1)`. -/
theorem next_mod_twentyseven_row_three_relocated_happy
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext :
      (K+1) % 27 = 14 ∨ (K+1) % 27 = 18 ∨
      (K+1) % 27 = 19 ∨ (K+1) % 27 = 25) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  have hTargetCommon : CommonTwo (K+1) :=
    commonTwo_of_mod27_row_three (K+1) hNext
  exact commonTwo_to_physical_happy_row (K+1) hTargetCommon

/-- Row four gives the next fresh-production relocation layer.  Any target
exponent in one of the fourteen exact overlap classes modulo 81 has a literal
common-two witness at row four, hence a physical Happy row on `4^(K+1)`. -/
theorem next_mod_eightyone_row_four_relocated_happy
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext :
      GSTFourPowerDirectResidue81.RowFourClass ((K+1) % 81)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  have hTargetCommon : CommonTwo (K+1) :=
    commonTwo_of_mod81_row_four (K+1) hNext
  exact commonTwo_to_physical_happy_row (K+1) hTargetCommon

/-- Row five extends the same fresh arithmetic construction to all forty exact
overlap classes modulo `243`.  The row-five classifier gives literal digit-2
facts at row five for `4^(K+1)` and `4^(K+2)`; packaging those facts as
`CommonTwo (K+1)` and applying the direct physical bridge yields an actual
relocated Happy row. -/
theorem next_mod_twohundredfortythree_row_five_relocated_happy
    (K sourceRow : Nat) (hsourceRow : 1 ≤ sourceRow)
    (hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : GSTFourPowerDirectResidue243.RowFiveClass ((K+1) % 243)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have _hSourceCommon : CommonTwo K :=
    physical_happy_to_commonTwo K sourceRow hsourceRow hSource
  have hrow :=
    GSTFourPowerDirectResidue243.row_five_overlap_of_mod243_classes (K+1) hNext
  have hTargetCommon : CommonTwo (K+1) := ⟨5, by norm_num, hrow.1, hrow.2⟩
  exact commonTwo_to_physical_happy_row (K+1) hTargetCommon

#check prefix_killing_trit_to_physical_happy
#check physical_happy_exposes_prefix_killing_certificate
#check source_happy_and_next_prefix_kill_to_relocated_happy
#check next_mod_nine_five_or_six_relocated_happy
#check next_mod_twentyseven_row_three_relocated_happy
#check next_mod_eightyone_row_four_relocated_happy
#check next_mod_twohundredfortythree_row_five_relocated_happy
#print axioms prefix_killing_trit_to_physical_happy
#print axioms physical_happy_exposes_prefix_killing_certificate
#print axioms source_happy_and_next_prefix_kill_to_relocated_happy
#print axioms next_mod_nine_five_or_six_relocated_happy
#print axioms next_mod_twentyseven_row_three_relocated_happy
#print axioms next_mod_eightyone_row_four_relocated_happy
#print axioms next_mod_twohundredfortythree_row_five_relocated_happy

end GSTFourPowerPrefixKillingHappy
