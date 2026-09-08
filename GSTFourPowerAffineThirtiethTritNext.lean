import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineThirtiethTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod205891132094649_eq_139351182292722_of_exponent_669
    (N : Nat) (hN : N % 205891132094649 = 669) : affineOrbit N % 205891132094649 = 139351182292722 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 30 N 669).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod205891132094649_pattern_011210000120111202112101120002_669
    (N : Nat) (hAmod : affineOrbit N % 205891132094649 = 139351182292722) : CommonTwo N := by
  by_contra hNo
  let A0 := affineOrbit N
  let A1 := tail3 A0
  let A2 := tail3 A1
  let A3 := tail3 A2
  let A4 := tail3 A3
  let A5 := tail3 A4
  let A6 := tail3 A5
  let A7 := tail3 A6
  let A8 := tail3 A7
  let A9 := tail3 A8
  let A10 := tail3 A9
  let A11 := tail3 A10
  let A12 := tail3 A11
  let A13 := tail3 A12
  let A14 := tail3 A13
  let A15 := tail3 A14
  let A16 := tail3 A15
  let A17 := tail3 A16
  let A18 := tail3 A17
  let A19 := tail3 A18
  let A20 := tail3 A19
  let A21 := tail3 A20
  let A22 := tail3 A21
  let A23 := tail3 A22
  let A24 := tail3 A23
  let A25 := tail3 A24
  let A26 := tail3 A25
  let A27 := tail3 A26
  let A28 := tail3 A27
  let A29 := tail3 A28
  have hR0 : A0 % 205891132094649 = 139351182292722 := by simpa [A0] using hAmod
  have hR1 : A1 % 68630377364883 = 46450394097574 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 22876792454961 = 15483464699191 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 7625597484987 = 5161154899730 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 2541865828329 = 1720384966576 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 847288609443 = 573461655525 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 282429536481 = 191153885175 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 94143178827 = 63717961725 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 31381059609 = 21239320575 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 10460353203 = 7079773525 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 3486784401 = 2359924508 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 1162261467 = 786641502 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 387420489 = 262213834 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 129140163 = 87404611 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 43046721 = 29134870 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 14348907 = 9711623 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 4782969 = 3237207 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 1594323 = 1079069 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 531441 = 359689 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 177147 = 119896 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 59049 = 39965 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 19683 = 13321 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 6561 = 4440 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 2187 = 1480 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 729 = 493 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 243 = 164 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 81 = 54 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 27 = 18 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 9 = 6 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 3 = 2 := by dsimp [A29, tail3]; omega
  have hd0 : lowDigit A0 = 0 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 1 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 2 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 1 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 0 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 0 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 0 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 1 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 2 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 0 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 1 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 1 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 2 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 0 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 1 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 2 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 1 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 0 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 1 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 1 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 2 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 0 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 0 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 0 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_zero_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 1 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 3 A4 := by rw [badChannel_one_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 2 A5 := by rw [badChannel_three_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 0 A6 := by rw [badChannel_two_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 0 A7 := by rw [badChannel_zero_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_zero_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 0 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 1 A10 := by rw [badChannel_zero_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 3 A11 := by rw [badChannel_one_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 1 A12 := by rw [badChannel_three_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 1 A13 := by rw [badChannel_one_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 1 A14 := by rw [badChannel_one_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 1 A15 := by rw [badChannel_one_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 3 A16 := by rw [badChannel_one_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_three_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 2 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 2 A20 := by rw [badChannel_two_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 3 A21 := by rw [badChannel_two_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 2 A22 := by rw [badChannel_three_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 0 A23 := by rw [badChannel_two_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 1 A24 := by rw [badChannel_zero_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 1 A25 := by rw [badChannel_one_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 3 A26 := by rw [badChannel_one_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 1 A27 := by rw [badChannel_three_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 0 A28 := by rw [badChannel_one_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 0 A29 := by rw [badChannel_zero_iff, hd28] at hbad28; simpa [A29] using hbad28
  rw [badChannel_zero_iff, hd29] at hbad29
  simpa using hbad29

theorem commonTwo_of_mod205891132094649_669
    (N : Nat) (hN : N % 205891132094649 = 669) : CommonTwo N := by
  exact commonTwo_of_mod205891132094649_pattern_011210000120111202112101120002_669 N
    (affineOrbit_mod205891132094649_eq_139351182292722_of_exponent_669 N hN)

theorem physical_happy_of_mod205891132094649_669
    (N : Nat) (hN : N % 205891132094649 = 669) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod205891132094649_669 N hN)

theorem four_power_happy_propagates_of_next_mod205891132094649_669
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 205891132094649 = 669) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod205891132094649_669 (K+1) hNext

#check commonTwo_of_mod205891132094649_669
#check physical_happy_of_mod205891132094649_669
#check four_power_happy_propagates_of_next_mod205891132094649_669
#print axioms commonTwo_of_mod205891132094649_669
#print axioms physical_happy_of_mod205891132094649_669
#print axioms four_power_happy_propagates_of_next_mod205891132094649_669

end GSTFourPowerAffineThirtiethTritNext