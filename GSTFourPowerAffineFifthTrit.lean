import GSTFourPowerAffineFourthTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFifthTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

/-- Exact fifth-prefix transfer from the exponent to the affine orbit. -/
private theorem affineOrbit_mod243_eq_of_exponent
    {N r : Nat} (hr : r < 243) (hN : N % 243 = r) :
    affineOrbit N % 243 = affineOrbit r % 243 := by
  exact (affineOrbit_residue_eq_iff_exponent_residue_eq 5 N r).2 (by
    simpa [Nat.mod_eq_of_lt hr] using hN)

/-- The new fifth-read exponent class `48 mod 243` has affine prefix
`0,1,1,0,2` (least-significant ternary digit first). -/
private theorem affineOrbit_mod243_eq_174_of_exponent
    {N : Nat} (hN : N % 243 = 48) : affineOrbit N % 243 = 174 := by
  have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 48) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

/-- The `0,1,1,0,2` affine prefix cannot remain in the bad channel.
The certified channel path is `1 -> 0 -> 1 -> 1 -> 0`, after which source
trit `2` is an immediate common-two success. -/
private theorem commonTwo_of_mod243_pattern_01102
    (N : Nat) (hAmod : affineOrbit N % 243 = 174) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3
    dsimp [A]
    omega
  have hbad1 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad10 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad1
    simpa using hbad1
  have hbad101 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad10
    simpa using hbad10
  have hbad1011 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad101
    simpa using hbad101
  have hbad10110 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad1011
    simpa using hbad1011
  rw [badChannel_zero_iff, hd4] at hbad10110
  simpa using hbad10110

/-- First genuinely new fifth-trit kill class on the exponent side. -/
theorem commonTwo_of_mod243_fortyeight
    (N : Nat) (hN : N % 243 = 48) : CommonTwo N := by
  exact commonTwo_of_mod243_pattern_01102 N
    (affineOrbit_mod243_eq_174_of_exponent hN)

/-- Convert the fifth-trit affine kill into an actual physical Happy row. -/
theorem physical_happy_of_mod243_fortyeight
    (N : Nat) (hN : N % 243 = 48) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod243_fortyeight N hN)

/-- Task-3.3-shaped direct relocation constructor for the first fifth-trit
sector. The incoming Happy row is not transported; a fresh physical row on
`4^(K+1)` is constructed from the affine kill certificate. -/
theorem four_power_happy_propagates_of_next_mod243_fortyeight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 243 = 48) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod243_fortyeight (K+1) hNext

#check commonTwo_of_mod243_fortyeight
#check physical_happy_of_mod243_fortyeight
#check four_power_happy_propagates_of_next_mod243_fortyeight
#print axioms commonTwo_of_mod243_fortyeight
#print axioms physical_happy_of_mod243_fortyeight
#print axioms four_power_happy_propagates_of_next_mod243_fortyeight

end GSTFourPowerAffineFifthTrit
