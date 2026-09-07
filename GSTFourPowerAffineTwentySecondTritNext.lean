import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineTwentySecondTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod31381059609_eq_21645485382_of_exponent_435
    (N : Nat) (hN : N % 31381059609 = 435) : affineOrbit N % 31381059609 = 21645485382 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 22 N 435).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod31381059609_pattern_0121120210121112121002_435
    (N : Nat) (hAmod : affineOrbit N % 31381059609 = 21645485382) : CommonTwo N := by
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
  have hR0 : A0 % 31381059609 = 21645485382 := by simpa [A0] using hAmod
  have hR1 : A1 % 10460353203 = 7215161794 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 3486784401 = 2405053931 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 1162261467 = 801684643 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 387420489 = 267228214 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 129140163 = 89076071 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 43046721 = 29692023 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 14348907 = 9897341 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 4782969 = 3299113 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 1594323 = 1099704 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 531441 = 366568 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 177147 = 122189 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 59049 = 40729 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 19683 = 13576 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 6561 = 4525 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 2187 = 1508 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 729 = 502 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 243 = 167 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 81 = 55 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 27 = 18 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 9 = 6 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 3 = 2 := by dsimp [A21, tail3]; omega
  have hd0 : lowDigit A0 = 0 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 2 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 1 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 2 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 2 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 1 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 0 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 2 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 1 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 1 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 2 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 1 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 0 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 0 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_zero_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 3 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 2 A4 := by rw [badChannel_three_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 2 A5 := by rw [badChannel_two_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 3 A6 := by rw [badChannel_two_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 1 A7 := by rw [badChannel_three_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 3 A8 := by rw [badChannel_one_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 2 A9 := by rw [badChannel_three_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 0 A10 := by rw [badChannel_two_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 1 A11 := by rw [badChannel_zero_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 3 A12 := by rw [badChannel_one_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 2 A13 := by rw [badChannel_three_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 2 A14 := by rw [badChannel_two_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 2 A15 := by rw [badChannel_two_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 3 A16 := by rw [badChannel_two_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 2 A17 := by rw [badChannel_three_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_two_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 2 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 0 A20 := by rw [badChannel_two_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 0 A21 := by rw [badChannel_zero_iff, hd20] at hbad20; simpa [A21] using hbad20
  rw [badChannel_zero_iff, hd21] at hbad21
  simpa using hbad21

theorem commonTwo_of_mod31381059609_435
    (N : Nat) (hN : N % 31381059609 = 435) : CommonTwo N := by
  exact commonTwo_of_mod31381059609_pattern_0121120210121112121002_435 N
    (affineOrbit_mod31381059609_eq_21645485382_of_exponent_435 N hN)

theorem physical_happy_of_mod31381059609_435
    (N : Nat) (hN : N % 31381059609 = 435) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod31381059609_435 N hN)

theorem four_power_happy_propagates_of_next_mod31381059609_435
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 31381059609 = 435) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod31381059609_435 (K+1) hNext

#check commonTwo_of_mod31381059609_435
#check physical_happy_of_mod31381059609_435
#check four_power_happy_propagates_of_next_mod31381059609_435
#print axioms commonTwo_of_mod31381059609_435
#print axioms physical_happy_of_mod31381059609_435
#print axioms four_power_happy_propagates_of_next_mod31381059609_435

end GSTFourPowerAffineTwentySecondTritNext
