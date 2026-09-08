import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineThirtySixthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod150094635296999121_eq_141621126362128568_of_exponent_2627
    (N : Nat) (hN : N % 150094635296999121 = 2627) : affineOrbit N % 150094635296999121 = 141621126362128568 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 36 N 2627).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod150094635296999121_pattern_200001001112110001011012012112011122_2627
    (N : Nat) (hAmod : affineOrbit N % 150094635296999121 = 141621126362128568) : CommonTwo N := by
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
  let A30 := tail3 A29
  let A31 := tail3 A30
  let A32 := tail3 A31
  let A33 := tail3 A32
  let A34 := tail3 A33
  let A35 := tail3 A34
  have hR0 : A0 % 150094635296999121 = 141621126362128568 := by simpa [A0] using hAmod
  have hR1 : A1 % 50031545098999707 = 47207042120709522 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 16677181699666569 = 15735680706903174 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 5559060566555523 = 5245226902301058 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 1853020188851841 = 1748408967433686 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 617673396283947 = 582802989144562 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 205891132094649 = 194267663048187 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 68630377364883 = 64755887682729 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 22876792454961 = 21585295894243 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 7625597484987 = 7195098631414 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 2541865828329 = 2398366210471 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 847288609443 = 799455403490 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 282429536481 = 266485134496 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 94143178827 = 88828378165 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 31381059609 = 29609459388 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 10460353203 = 9869819796 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 3486784401 = 3289939932 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 1162261467 = 1096646644 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 387420489 = 365548881 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 129140163 = 121849627 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 43046721 = 40616542 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 14348907 = 13538847 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 4782969 = 4512949 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 1594323 = 1504316 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 531441 = 501438 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 177147 = 167146 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 59049 = 55715 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 19683 = 18571 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 6561 = 6190 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 2187 = 2063 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 729 = 687 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 243 = 229 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 81 = 76 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 27 = 25 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 9 = 8 := by dsimp [A34, tail3]; omega
  have hR35 : A35 % 3 = 2 := by dsimp [A35, tail3]; omega
  have hd0 : lowDigit A0 = 2 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 0 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 0 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 0 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 0 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 1 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 0 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 1 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 1 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 2 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 1 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 0 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 0 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 0 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 1 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 0 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 1 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 1 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 0 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 1 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 2 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 0 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 1 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 2 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 1 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 1 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 2 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 0 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 1 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 1 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 1 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 2 := by dsimp [lowDigit]; omega
  have hd35 : lowDigit A35 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_three_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 0 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 0 A4 := by rw [badChannel_zero_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 0 A5 := by rw [badChannel_zero_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 1 A6 := by rw [badChannel_zero_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 0 A7 := by rw [badChannel_one_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_zero_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 1 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 1 A10 := by rw [badChannel_one_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 1 A11 := by rw [badChannel_one_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 3 A12 := by rw [badChannel_one_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 2 A13 := by rw [badChannel_three_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 2 A14 := by rw [badChannel_two_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 0 A15 := by rw [badChannel_two_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 0 A16 := by rw [badChannel_zero_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 0 A17 := by rw [badChannel_zero_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 1 A18 := by rw [badChannel_zero_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 0 A19 := by rw [badChannel_one_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 1 A20 := by rw [badChannel_zero_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_one_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 0 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 1 A23 := by rw [badChannel_zero_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 3 A24 := by rw [badChannel_one_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 1 A25 := by rw [badChannel_three_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 1 A26 := by rw [badChannel_one_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 3 A27 := by rw [badChannel_one_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 2 A28 := by rw [badChannel_three_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 2 A29 := by rw [badChannel_two_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 3 A30 := by rw [badChannel_two_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 1 A31 := by rw [badChannel_three_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 1 A32 := by rw [badChannel_one_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 1 A33 := by rw [badChannel_one_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 1 A34 := by rw [badChannel_one_iff, hd33] at hbad33; simpa [A34] using hbad33
  have hbad35 : BadChannel 3 A35 := by rw [badChannel_one_iff, hd34] at hbad34; simpa [A35] using hbad34
  rw [badChannel_three_iff, hd35] at hbad35
  simpa using hbad35

theorem commonTwo_of_mod150094635296999121_2627
    (N : Nat) (hN : N % 150094635296999121 = 2627) : CommonTwo N := by
  exact commonTwo_of_mod150094635296999121_pattern_200001001112110001011012012112011122_2627 N
    (affineOrbit_mod150094635296999121_eq_141621126362128568_of_exponent_2627 N hN)

theorem physical_happy_of_mod150094635296999121_2627
    (N : Nat) (hN : N % 150094635296999121 = 2627) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod150094635296999121_2627 N hN)

theorem four_power_happy_propagates_of_next_mod150094635296999121_2627
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 150094635296999121 = 2627) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod150094635296999121_2627 (K+1) hNext

#check commonTwo_of_mod150094635296999121_2627
#check physical_happy_of_mod150094635296999121_2627
#check four_power_happy_propagates_of_next_mod150094635296999121_2627

end GSTFourPowerAffineThirtySixthTritNext
