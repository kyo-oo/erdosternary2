import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFortyFourthTritNext

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private def affineOrbitMod (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (4 * affineOrbitMod m n + 1) % m

private theorem affineOrbit_mod_eq_affineOrbitMod (m n : Nat) :
    affineOrbit n % m = affineOrbitMod m n := by
  induction n with
  | zero => simp [affineOrbit, affineOrbitMod]
  | succ n ih =>
      simp [affineOrbit, affineOrbitMod, Nat.add_mod, Nat.mul_mod, ih]

private theorem affineOrbit_mod984770902183611232881_eq_686846491986537116967_of_exponent_18543
    (N : Nat) (hN : N % 984770902183611232881 = 18543) : affineOrbit N % 984770902183611232881 = 686846491986537116967 := by
  have hExp : N % 3 ^ 44 = 18543 % 3 ^ 44 := by
    norm_num
    exact hN
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 44 N 18543).2 hExp
  have hRef : affineOrbit 18543 % 984770902183611232881 = 686846491986537116967 := by
    rw [affineOrbit_mod_eq_affineOrbitMod]
    decide
  have hPow : 3 ^ 44 = 984770902183611232881 := by norm_num
  rw [hPow] at h
  exact h.trans hRef

private theorem commonTwo_of_mod984770902183611232881_pattern_01111010011111212010111012112020120011112002_18543
    (N : Nat) (hAmod : affineOrbit N % 984770902183611232881 = 686846491986537116967) : CommonTwo N := by
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
  let A36 := tail3 A35
  let A37 := tail3 A36
  let A38 := tail3 A37
  let A39 := tail3 A38
  let A40 := tail3 A39
  let A41 := tail3 A40
  let A42 := tail3 A41
  let A43 := tail3 A42
  have hR0 : A0 % 984770902183611232881 = 686846491986537116967 := by simpa [A0] using hAmod
  have hR1 : A1 % 328256967394537077627 = 228948830662179038989 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 109418989131512359209 = 76316276887393012996 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 36472996377170786403 = 25438758962464337665 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 12157665459056928801 = 8479586320821445888 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 4052555153018976267 = 2826528773607148629 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 1350851717672992089 = 942176257869049543 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 450283905890997363 = 314058752623016514 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 150094635296999121 = 104686250874338838 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 50031545098999707 = 34895416958112946 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 16677181699666569 = 11631805652704315 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 5559060566555523 = 3877268550901438 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 1853020188851841 = 1292422850300479 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 617673396283947 = 430807616766826 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 205891132094649 = 143602538922275 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 68630377364883 = 47867512974091 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 22876792454961 = 15955837658030 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 7625597484987 = 5318612552676 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 2541865828329 = 1772870850892 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 847288609443 = 590956950297 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 282429536481 = 196985650099 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 94143178827 = 65661883366 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 31381059609 = 21887294455 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 10460353203 = 7295764818 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 3486784401 = 2431921606 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 1162261467 = 810640535 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 387420489 = 270213511 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 129140163 = 90071170 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 43046721 = 30023723 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 14348907 = 10007907 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 4782969 = 3335969 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 1594323 = 1111989 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 531441 = 370663 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 177147 = 123554 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 59049 = 41184 := by dsimp [A34, tail3]; omega
  have hR35 : A35 % 19683 = 13728 := by dsimp [A35, tail3]; omega
  have hR36 : A36 % 6561 = 4576 := by dsimp [A36, tail3]; omega
  have hR37 : A37 % 2187 = 1525 := by dsimp [A37, tail3]; omega
  have hR38 : A38 % 729 = 508 := by dsimp [A38, tail3]; omega
  have hR39 : A39 % 243 = 169 := by dsimp [A39, tail3]; omega
  have hR40 : A40 % 81 = 56 := by dsimp [A40, tail3]; omega
  have hR41 : A41 % 27 = 18 := by dsimp [A41, tail3]; omega
  have hR42 : A42 % 9 = 6 := by dsimp [A42, tail3]; omega
  have hR43 : A43 % 3 = 2 := by dsimp [A43, tail3]; omega
  have hd0 : lowDigit A0 = 0 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 1 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 1 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 0 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 1 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 0 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 0 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 1 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 1 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 1 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 2 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 1 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 2 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 0 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 0 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 1 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 1 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 1 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 0 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 1 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 2 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 1 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 1 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 2 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 0 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 2 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 0 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 1 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 2 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 0 := by dsimp [lowDigit]; omega
  have hd35 : lowDigit A35 = 0 := by dsimp [lowDigit]; omega
  have hd36 : lowDigit A36 = 1 := by dsimp [lowDigit]; omega
  have hd37 : lowDigit A37 = 1 := by dsimp [lowDigit]; omega
  have hd38 : lowDigit A38 = 1 := by dsimp [lowDigit]; omega
  have hd39 : lowDigit A39 = 1 := by dsimp [lowDigit]; omega
  have hd40 : lowDigit A40 = 2 := by dsimp [lowDigit]; omega
  have hd41 : lowDigit A41 = 0 := by dsimp [lowDigit]; omega
  have hd42 : lowDigit A42 = 0 := by dsimp [lowDigit]; omega
  have hd43 : lowDigit A43 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_zero_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 1 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 1 A4 := by rw [badChannel_one_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 1 A5 := by rw [badChannel_one_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 0 A6 := by rw [badChannel_one_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 1 A7 := by rw [badChannel_zero_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_one_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 0 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 1 A10 := by rw [badChannel_zero_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 1 A11 := by rw [badChannel_one_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 1 A12 := by rw [badChannel_one_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 1 A13 := by rw [badChannel_one_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 1 A14 := by rw [badChannel_one_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 3 A15 := by rw [badChannel_one_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 2 A16 := by rw [badChannel_three_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 3 A17 := by rw [badChannel_two_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 1 A18 := by rw [badChannel_three_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 1 A19 := by rw [badChannel_one_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 0 A20 := by rw [badChannel_one_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_zero_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 1 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 1 A23 := by rw [badChannel_one_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 0 A24 := by rw [badChannel_one_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 1 A25 := by rw [badChannel_zero_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 3 A26 := by rw [badChannel_one_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 2 A27 := by rw [badChannel_three_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 2 A28 := by rw [badChannel_two_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 3 A29 := by rw [badChannel_two_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 1 A30 := by rw [badChannel_three_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 3 A31 := by rw [badChannel_one_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 1 A32 := by rw [badChannel_three_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 1 A33 := by rw [badChannel_one_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 3 A34 := by rw [badChannel_one_iff, hd33] at hbad33; simpa [A34] using hbad33
  have hbad35 : BadChannel 1 A35 := by rw [badChannel_three_iff, hd34] at hbad34; simpa [A35] using hbad34
  have hbad36 : BadChannel 0 A36 := by rw [badChannel_one_iff, hd35] at hbad35; simpa [A36] using hbad35
  have hbad37 : BadChannel 1 A37 := by rw [badChannel_zero_iff, hd36] at hbad36; simpa [A37] using hbad36
  have hbad38 : BadChannel 1 A38 := by rw [badChannel_one_iff, hd37] at hbad37; simpa [A38] using hbad37
  have hbad39 : BadChannel 1 A39 := by rw [badChannel_one_iff, hd38] at hbad38; simpa [A39] using hbad38
  have hbad40 : BadChannel 1 A40 := by rw [badChannel_one_iff, hd39] at hbad39; simpa [A40] using hbad39
  have hbad41 : BadChannel 3 A41 := by rw [badChannel_one_iff, hd40] at hbad40; simpa [A41] using hbad40
  have hbad42 : BadChannel 1 A42 := by rw [badChannel_three_iff, hd41] at hbad41; simpa [A42] using hbad41
  have hbad43 : BadChannel 0 A43 := by rw [badChannel_one_iff, hd42] at hbad42; simpa [A43] using hbad42
  rw [badChannel_zero_iff, hd43] at hbad43
  simpa using hbad43

theorem commonTwo_of_mod984770902183611232881_18543
    (N : Nat) (hN : N % 984770902183611232881 = 18543) : CommonTwo N := by
  exact commonTwo_of_mod984770902183611232881_pattern_01111010011111212010111012112020120011112002_18543 N
    (affineOrbit_mod984770902183611232881_eq_686846491986537116967_of_exponent_18543 N hN)

theorem physical_happy_of_mod984770902183611232881_18543
    (N : Nat) (hN : N % 984770902183611232881 = 18543) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod984770902183611232881_18543 N hN)

theorem four_power_happy_propagates_of_next_mod984770902183611232881_18543
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 984770902183611232881 = 18543) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod984770902183611232881_18543 (K+1) hNext

#check commonTwo_of_mod984770902183611232881_18543
#check physical_happy_of_mod984770902183611232881_18543
#check four_power_happy_propagates_of_next_mod984770902183611232881_18543

end GSTFourPowerAffineFortyFourthTritNext