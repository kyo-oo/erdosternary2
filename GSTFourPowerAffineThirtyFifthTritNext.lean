import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineThirtyFifthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod50031545098999707_eq_34180577015143370_of_exponent_560
    (N : Nat) (hN : N % 50031545098999707 = 560) : affineOrbit N % 50031545098999707 = 34180577015143370 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 35 N 560).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod50031545098999707_pattern_21212101200101120202010100100011002_560
    (N : Nat) (hAmod : affineOrbit N % 50031545098999707 = 34180577015143370) : CommonTwo N := by
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
  have hR0 : A0 % 50031545098999707 = 34180577015143370 := by simpa [A0] using hAmod
  have hR1 : A1 % 16677181699666569 = 11393525671714456 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 5559060566555523 = 3797841890571485 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 1853020188851841 = 1265947296857161 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 617673396283947 = 421982432285720 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 205891132094649 = 140660810761906 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 68630377364883 = 46886936920635 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 22876792454961 = 15628978973545 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 7625597484987 = 5209659657848 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 2541865828329 = 1736553219282 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 847288609443 = 578851073094 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 282429536481 = 192950357698 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 94143178827 = 64316785899 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 31381059609 = 21438928633 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 10460353203 = 7146309544 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 3486784401 = 2382103181 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 1162261467 = 794034393 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 387420489 = 264678131 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 129140163 = 88226043 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 43046721 = 29408681 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 14348907 = 9802893 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 4782969 = 3267631 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 1594323 = 1089210 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 531441 = 363070 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 177147 = 121023 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 59049 = 40341 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 19683 = 13447 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 6561 = 4482 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 2187 = 1494 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 729 = 498 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 243 = 166 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 81 = 55 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 27 = 18 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 9 = 6 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 3 = 2 := by dsimp [A34, tail3]; omega
  have hd0 : lowDigit A0 = 2 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 2 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 2 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 1 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 1 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 2 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 0 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 0 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 1 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 0 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 1 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 2 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 0 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 0 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 2 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 0 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 1 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 0 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 1 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 0 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 0 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 1 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 0 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 0 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 0 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 1 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 1 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 0 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 0 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 2 A2 := by rw [badChannel_three_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 3 A3 := by rw [badChannel_two_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 2 A4 := by rw [badChannel_three_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 3 A5 := by rw [badChannel_two_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 2 A6 := by rw [badChannel_three_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 0 A7 := by rw [badChannel_two_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 1 A8 := by rw [badChannel_zero_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 3 A9 := by rw [badChannel_one_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 1 A10 := by rw [badChannel_three_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 0 A11 := by rw [badChannel_one_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 1 A12 := by rw [badChannel_zero_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 0 A13 := by rw [badChannel_one_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 1 A14 := by rw [badChannel_zero_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 1 A15 := by rw [badChannel_one_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 3 A16 := by rw [badChannel_one_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_three_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 1 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 3 A20 := by rw [badChannel_one_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_three_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 1 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 0 A23 := by rw [badChannel_one_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 1 A24 := by rw [badChannel_zero_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 0 A25 := by rw [badChannel_one_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 0 A26 := by rw [badChannel_zero_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 1 A27 := by rw [badChannel_zero_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 0 A28 := by rw [badChannel_one_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 0 A29 := by rw [badChannel_zero_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 0 A30 := by rw [badChannel_zero_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 1 A31 := by rw [badChannel_zero_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 1 A32 := by rw [badChannel_one_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 0 A33 := by rw [badChannel_one_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 0 A34 := by rw [badChannel_zero_iff, hd33] at hbad33; simpa [A34] using hbad33
  rw [badChannel_zero_iff, hd34] at hbad34
  simpa using hbad34

theorem commonTwo_of_mod50031545098999707_560
    (N : Nat) (hN : N % 50031545098999707 = 560) : CommonTwo N := by
  exact commonTwo_of_mod50031545098999707_pattern_21212101200101120202010100100011002_560 N
    (affineOrbit_mod50031545098999707_eq_34180577015143370_of_exponent_560 N hN)

theorem physical_happy_of_mod50031545098999707_560
    (N : Nat) (hN : N % 50031545098999707 = 560) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod50031545098999707_560 N hN)

theorem four_power_happy_propagates_of_next_mod50031545098999707_560
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 50031545098999707 = 560) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod50031545098999707_560 (K+1) hNext

#check commonTwo_of_mod50031545098999707_560
#check physical_happy_of_mod50031545098999707_560
#check four_power_happy_propagates_of_next_mod50031545098999707_560

end GSTFourPowerAffineThirtyFifthTritNext
