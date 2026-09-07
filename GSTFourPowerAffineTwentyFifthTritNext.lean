import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineTwentyFifthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod847288609443_eq_776965252927_of_exponent_436
    (N : Nat) (hN : N % 847288609443 = 436) : affineOrbit N % 847288609443 = 776965252927 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 25 N 436).2 (by simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

private theorem commonTwo_of_mod847288609443_pattern_1101010012101001111202022_436
    (N : Nat) (hAmod : affineOrbit N % 847288609443 = 776965252927) : CommonTwo N := by
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
  have hR0 : A0 % 847288609443 = 776965252927 := by simpa [A0] using hAmod
  have hR1 : A1 % 282429536481 = 258988417642 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 94143178827 = 86329472547 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 31381059609 = 28776490849 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 10460353203 = 9592163616 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 3486784401 = 3197387872 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 1162261467 = 1065795957 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 387420489 = 355265319 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 129140163 = 118421773 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 43046721 = 39473924 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 14348907 = 13157974 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 4782969 = 4385991 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 1594323 = 1461997 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 531441 = 487332 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 177147 = 162444 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 59049 = 54148 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 19683 = 18049 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 6561 = 6016 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 2187 = 2005 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 729 = 668 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 243 = 222 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 81 = 74 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 27 = 24 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 9 = 8 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 3 = 2 := by dsimp [A24, tail3]; omega
  have hd0 : lowDigit A0 = 1 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 0 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 0 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 1 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 0 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 1 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 2 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 0 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 1 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 0 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 0 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 1 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 1 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 1 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 2 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 0 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 2 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 0 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 2 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_one_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 0 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 1 A4 := by rw [badChannel_zero_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 0 A5 := by rw [badChannel_one_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 1 A6 := by rw [badChannel_zero_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 0 A7 := by rw [badChannel_one_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_zero_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 1 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 3 A10 := by rw [badChannel_one_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 2 A11 := by rw [badChannel_three_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 0 A12 := by rw [badChannel_two_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 1 A13 := by rw [badChannel_zero_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 0 A14 := by rw [badChannel_one_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 0 A15 := by rw [badChannel_zero_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 1 A16 := by rw [badChannel_zero_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_one_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 1 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 1 A19 := by rw [badChannel_one_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 3 A20 := by rw [badChannel_one_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_three_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 3 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 1 A23 := by rw [badChannel_three_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 3 A24 := by rw [badChannel_one_iff, hd23] at hbad23; simpa [A24] using hbad23
  rw [badChannel_three_iff, hd24] at hbad24
  simpa using hbad24

theorem commonTwo_of_mod847288609443_436
    (N : Nat) (hN : N % 847288609443 = 436) : CommonTwo N := by
  exact commonTwo_of_mod847288609443_pattern_1101010012101001111202022_436 N
    (affineOrbit_mod847288609443_eq_776965252927_of_exponent_436 N hN)

theorem physical_happy_of_mod847288609443_436
    (N : Nat) (hN : N % 847288609443 = 436) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod847288609443_436 N hN)

theorem four_power_happy_propagates_of_next_mod847288609443_436
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 847288609443 = 436) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod847288609443_436 (K+1) hNext

#check commonTwo_of_mod847288609443_436
#check physical_happy_of_mod847288609443_436
#check four_power_happy_propagates_of_next_mod847288609443_436
#print axioms commonTwo_of_mod847288609443_436
#print axioms physical_happy_of_mod847288609443_436
#print axioms four_power_happy_propagates_of_next_mod847288609443_436

end GSTFourPowerAffineTwentyFifthTritNext
