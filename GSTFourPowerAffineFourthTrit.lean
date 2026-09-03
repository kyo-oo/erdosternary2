import GSTFourPowerAffineThirdTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFourthTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod81_eq_54_of_exponent
    {N : Nat} (hN : N % 81 = 54) : affineOrbit N % 81 = 54 := by
  have h :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq 4 N 54).2 (by
      norm_num
      exact hN)
  norm_num [affineOrbit] at h
  exact h

/-- Fourth-trit affine kill for exponent residue 54. The affine source reads
`0,0,0,2`: channel 1 enters state 0 on the first trit, remains in state 0
for the next two trits, and the fourth read `2` forces a common-two witness. -/
theorem commonTwo_of_mod81_fiftyfour
    (N : Nat) (hN : N % 81 = 54) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hAmod : A % 81 = 54 := by
    dsimp [A]
    exact affineOrbit_mod81_eq_54_of_exponent hN
  have hd0 : lowDigit A = 0 := by
    unfold lowDigit
    omega
  have hd1 : lowDigit (tail3 A) = 0 := by
    unfold lowDigit tail3
    omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by
    unfold lowDigit tail3
    omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by
    unfold lowDigit tail3
    omega
  have hbad1 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad0 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad1
    simpa using hbad1
  have hbad00 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad0
    simpa using hbad0
  have hbad000 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad00
    simpa using hbad00
  rw [badChannel_zero_iff, hd3] at hbad000
  simpa using hbad000

/-- The new fourth-trit kill class produces an actual physical Happy row. -/
theorem physical_happy_of_mod81_fiftyfour
    (N : Nat) (hN : N % 81 = 54) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyfour N hN)

/-- Task-3.3-shaped relocation constructor for the first genuinely new
fourth-trit sector. -/
theorem four_power_happy_propagates_of_next_mod81_fiftyfour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 81 = 54) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod81_fiftyfour (K+1) hNext

#check commonTwo_of_mod81_fiftyfour
#check physical_happy_of_mod81_fiftyfour
#check four_power_happy_propagates_of_next_mod81_fiftyfour
#print axioms commonTwo_of_mod81_fiftyfour
#print axioms physical_happy_of_mod81_fiftyfour
#print axioms four_power_happy_propagates_of_next_mod81_fiftyfour

end GSTFourPowerAffineFourthTrit
