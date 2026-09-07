import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineTwentyThirdTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod94143178827_eq_65377258364_of_exponent_287
    (N : Nat) (hN : N % 94143178827 = 287) : affineOrbit N % 94143178827 = 65377258364 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 23 N 287).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod94143178827_pattern_20111111211202020202002_287
    (N : Nat) (hAmod : affineOrbit N % 94143178827 = 65377258364) : CommonTwo N := by
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
  have hR0 : A0 % 94143178827 = 65377258364 := by simpa [A0] using hAmod
  have hR1 : A1 % 31381059609 = 21792419454 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 10460353203 = 7264139818 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 3486784401 = 2421379939 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 1162261467 = 807126646 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 387420489 = 269042215 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 129140163 = 89680738 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 43046721 = 29893579 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 14348907 = 9964526 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 4782969 = 3321508 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 1594323 = 1107169 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 531441 = 369056 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 177147 = 123018 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 59049 = 41006 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 19683 = 13668 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 6561 = 4556 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 2187 = 1518 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 729 = 506 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 243 = 168 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 81 = 56 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 27 = 18 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 9 = 6 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 3 = 2 := by dsimp [A22, tail3]; omega
  have hd0 : lowDigit A0 = 2 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 0 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 1 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 1 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 1 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 1 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 1 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 2 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 1 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 2 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 0 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 2 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 0 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 2 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 0 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 0 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 2 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 0 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 0 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_three_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 1 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 1 A4 := by rw [badChannel_one_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 1 A5 := by rw [badChannel_one_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 1 A6 := by rw [badChannel_one_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 1 A7 := by rw [badChannel_one_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 1 A8 := by rw [badChannel_one_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 3 A9 := by rw [badChannel_one_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 2 A10 := by rw [badChannel_three_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 2 A11 := by rw [badChannel_two_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 3 A12 := by rw [badChannel_two_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 1 A13 := by rw [badChannel_three_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 3 A14 := by rw [badChannel_one_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 1 A15 := by rw [badChannel_three_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 3 A16 := by rw [badChannel_one_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_three_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 1 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 3 A20 := by rw [badChannel_one_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_three_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 0 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  rw [badChannel_zero_iff, hd22] at hbad22
  simpa using hbad22

theorem commonTwo_of_mod94143178827_287
    (N : Nat) (hN : N % 94143178827 = 287) : CommonTwo N := by
  exact commonTwo_of_mod94143178827_pattern_20111111211202020202002_287 N
    (affineOrbit_mod94143178827_eq_65377258364_of_exponent_287 N hN)

theorem physical_happy_of_mod94143178827_287
    (N : Nat) (hN : N % 94143178827 = 287) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod94143178827_287 N hN)

theorem four_power_happy_propagates_of_next_mod94143178827_287
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 94143178827 = 287) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod94143178827_287 (K+1) hNext

#check commonTwo_of_mod94143178827_287
#check physical_happy_of_mod94143178827_287
#check four_power_happy_propagates_of_next_mod94143178827_287
#print axioms commonTwo_of_mod94143178827_287
#print axioms physical_happy_of_mod94143178827_287
#print axioms four_power_happy_propagates_of_next_mod94143178827_287

end GSTFourPowerAffineTwentyThirdTritNext
