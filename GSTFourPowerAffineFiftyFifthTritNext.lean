import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 3000000
set_option maxHeartbeats 30000000

namespace GSTFourPowerAffineFiftyFifthTritNext

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

private theorem affineOrbit_mod174449211009120179071170507_eq_124019512228608034172146897_of_exponent_85117
    (N : Nat) (hN : N % 174449211009120179071170507 = 85117) : affineOrbit N % 174449211009120179071170507 = 124019512228608034172146897 := by
  have hExp : N % 3 ^ 55 = 85117 % 3 ^ 55 := by
    norm_num
    exact hN
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 55 N 85117).2 hExp
  have hRef : affineOrbit 85117 % 174449211009120179071170507 = 124019512228608034172146897 := by
    rw [affineOrbit_mod_eq_affineOrbitMod]
    decide
  have hPow : 3 ^ 55 = 174449211009120179071170507 := by norm_num
  rw [hPow] at h
  exact h.trans hRef

private theorem commonTwo_of_mod174449211009120179071170507_pattern_1112010012101010110112000012012001012011120100120210102_85117
    (N : Nat) (hAmod : affineOrbit N % 174449211009120179071170507 = 124019512228608034172146897) : CommonTwo N := by
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
  let A44 := tail3 A43
  let A45 := tail3 A44
  let A46 := tail3 A45
  let A47 := tail3 A46
  let A48 := tail3 A47
  let A49 := tail3 A48
  let A50 := tail3 A49
  let A51 := tail3 A50
  let A52 := tail3 A51
  let A53 := tail3 A52
  let A54 := tail3 A53
  have hR0 : A0 % 174449211009120179071170507 = 124019512228608034172146897 := by simpa [A0] using hAmod
  have hR1 : A1 % 58149737003040059690390169 = 41339837409536011390715632 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 19383245667680019896796723 = 13779945803178670463571877 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 6461081889226673298932241 = 4593315267726223487857292 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 2153693963075557766310747 = 1531105089242074495952430 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 717897987691852588770249 = 510368363080691498650810 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 239299329230617529590083 = 170122787693563832883603 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 79766443076872509863361 = 56707595897854610961201 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 26588814358957503287787 = 18902531965951536987067 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 8862938119652501095929 = 6300843988650512329022 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 2954312706550833698643 = 2100281329550170776340 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 984770902183611232881 = 700093776516723592113 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 328256967394537077627 = 233364592172241197371 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 109418989131512359209 = 77788197390747065790 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 36472996377170786403 = 25929399130249021930 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 12157665459056928801 = 8643133043416340643 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 4052555153018976267 = 2881044347805446881 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 1350851717672992089 = 960348115935148960 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 450283905890997363 = 320116038645049653 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 150094635296999121 = 106705346215016551 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 50031545098999707 = 35568448738338850 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 16677181699666569 = 11856149579446283 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 5559060566555523 = 3952049859815427 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 1853020188851841 = 1317349953271809 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 617673396283947 = 439116651090603 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 205891132094649 = 146372217030201 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 68630377364883 = 48790739010067 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 22876792454961 = 16263579670022 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 7625597484987 = 5421193223340 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 2541865828329 = 1807064407780 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 847288609443 = 602354802593 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 282429536481 = 200784934197 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 94143178827 = 66928311399 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 31381059609 = 22309437133 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 10460353203 = 7436479044 := by dsimp [A34, tail3]; omega
  have hR35 : A35 % 3486784401 = 2478826348 := by dsimp [A35, tail3]; omega
  have hR36 : A36 % 1162261467 = 826275449 := by dsimp [A36, tail3]; omega
  have hR37 : A37 % 387420489 = 275425149 := by dsimp [A37, tail3]; omega
  have hR38 : A38 % 129140163 = 91808383 := by dsimp [A38, tail3]; omega
  have hR39 : A39 % 43046721 = 30602794 := by dsimp [A39, tail3]; omega
  have hR40 : A40 % 14348907 = 10200931 := by dsimp [A40, tail3]; omega
  have hR41 : A41 % 4782969 = 3400310 := by dsimp [A41, tail3]; omega
  have hR42 : A42 % 1594323 = 1133436 := by dsimp [A42, tail3]; omega
  have hR43 : A43 % 531441 = 377812 := by dsimp [A43, tail3]; omega
  have hR44 : A44 % 177147 = 125937 := by dsimp [A44, tail3]; omega
  have hR45 : A45 % 59049 = 41979 := by dsimp [A45, tail3]; omega
  have hR46 : A46 % 19683 = 13993 := by dsimp [A46, tail3]; omega
  have hR47 : A47 % 6561 = 4664 := by dsimp [A47, tail3]; omega
  have hR48 : A48 % 2187 = 1554 := by dsimp [A48, tail3]; omega
  have hR49 : A49 % 729 = 518 := by dsimp [A49, tail3]; omega
  have hR50 : A50 % 243 = 172 := by dsimp [A50, tail3]; omega
  have hR51 : A51 % 81 = 57 := by dsimp [A51, tail3]; omega
  have hR52 : A52 % 27 = 19 := by dsimp [A52, tail3]; omega
  have hR53 : A53 % 9 = 6 := by dsimp [A53, tail3]; omega
  have hR54 : A54 % 3 = 2 := by dsimp [A54, tail3]; omega
  have hd0 : lowDigit A0 = 1 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 1 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 2 := by dsimp [lowDigit]; omega
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
  have hd14 : lowDigit A14 = 1 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 0 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 1 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 1 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 0 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 1 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 1 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 2 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 0 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 0 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 0 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 1 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 2 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 0 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 1 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 2 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 0 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 0 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 0 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 1 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 0 := by dsimp [lowDigit]; omega
  have hd35 : lowDigit A35 = 1 := by dsimp [lowDigit]; omega
  have hd36 : lowDigit A36 = 2 := by dsimp [lowDigit]; omega
  have hd37 : lowDigit A37 = 0 := by dsimp [lowDigit]; omega
  have hd38 : lowDigit A38 = 1 := by dsimp [lowDigit]; omega
  have hd39 : lowDigit A39 = 1 := by dsimp [lowDigit]; omega
  have hd40 : lowDigit A40 = 1 := by dsimp [lowDigit]; omega
  have hd41 : lowDigit A41 = 2 := by dsimp [lowDigit]; omega
  have hd42 : lowDigit A42 = 0 := by dsimp [lowDigit]; omega
  have hd43 : lowDigit A43 = 1 := by dsimp [lowDigit]; omega
  have hd44 : lowDigit A44 = 0 := by dsimp [lowDigit]; omega
  have hd45 : lowDigit A45 = 0 := by dsimp [lowDigit]; omega
  have hd46 : lowDigit A46 = 1 := by dsimp [lowDigit]; omega
  have hd47 : lowDigit A47 = 2 := by dsimp [lowDigit]; omega
  have hd48 : lowDigit A48 = 0 := by dsimp [lowDigit]; omega
  have hd49 : lowDigit A49 = 2 := by dsimp [lowDigit]; omega
  have hd50 : lowDigit A50 = 1 := by dsimp [lowDigit]; omega
  have hd51 : lowDigit A51 = 0 := by dsimp [lowDigit]; omega
  have hd52 : lowDigit A52 = 1 := by dsimp [lowDigit]; omega
  have hd53 : lowDigit A53 = 0 := by dsimp [lowDigit]; omega
  have hd54 : lowDigit A54 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_one_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 1 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 3 A4 := by rw [badChannel_one_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 1 A5 := by rw [badChannel_three_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 1 A6 := by rw [badChannel_one_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 0 A7 := by rw [badChannel_one_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_zero_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 1 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 3 A10 := by rw [badChannel_one_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 2 A11 := by rw [badChannel_three_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 0 A12 := by rw [badChannel_two_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 1 A13 := by rw [badChannel_zero_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 0 A14 := by rw [badChannel_one_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 1 A15 := by rw [badChannel_zero_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 0 A16 := by rw [badChannel_one_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_zero_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 1 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 0 A19 := by rw [badChannel_one_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 1 A20 := by rw [badChannel_zero_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_one_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 3 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 1 A23 := by rw [badChannel_three_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 0 A24 := by rw [badChannel_one_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 0 A25 := by rw [badChannel_zero_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 1 A26 := by rw [badChannel_zero_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 3 A27 := by rw [badChannel_one_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 1 A28 := by rw [badChannel_three_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 1 A29 := by rw [badChannel_one_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 3 A30 := by rw [badChannel_one_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 1 A31 := by rw [badChannel_three_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 0 A32 := by rw [badChannel_one_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 0 A33 := by rw [badChannel_zero_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 1 A34 := by rw [badChannel_zero_iff, hd33] at hbad33; simpa [A34] using hbad33
  have hbad35 : BadChannel 0 A35 := by rw [badChannel_one_iff, hd34] at hbad34; simpa [A35] using hbad34
  have hbad36 : BadChannel 1 A36 := by rw [badChannel_zero_iff, hd35] at hbad35; simpa [A36] using hbad35
  have hbad37 : BadChannel 3 A37 := by rw [badChannel_one_iff, hd36] at hbad36; simpa [A37] using hbad36
  have hbad38 : BadChannel 1 A38 := by rw [badChannel_three_iff, hd37] at hbad37; simpa [A38] using hbad37
  have hbad39 : BadChannel 1 A39 := by rw [badChannel_one_iff, hd38] at hbad38; simpa [A39] using hbad38
  have hbad40 : BadChannel 1 A40 := by rw [badChannel_one_iff, hd39] at hbad39; simpa [A40] using hbad39
  have hbad41 : BadChannel 1 A41 := by rw [badChannel_one_iff, hd40] at hbad40; simpa [A41] using hbad40
  have hbad42 : BadChannel 3 A42 := by rw [badChannel_one_iff, hd41] at hbad41; simpa [A42] using hbad41
  have hbad43 : BadChannel 1 A43 := by rw [badChannel_three_iff, hd42] at hbad42; simpa [A43] using hbad42
  have hbad44 : BadChannel 1 A44 := by rw [badChannel_one_iff, hd43] at hbad43; simpa [A44] using hbad43
  have hbad45 : BadChannel 0 A45 := by rw [badChannel_one_iff, hd44] at hbad44; simpa [A45] using hbad44
  have hbad46 : BadChannel 0 A46 := by rw [badChannel_zero_iff, hd45] at hbad45; simpa [A46] using hbad45
  have hbad47 : BadChannel 1 A47 := by rw [badChannel_zero_iff, hd46] at hbad46; simpa [A47] using hbad46
  have hbad48 : BadChannel 3 A48 := by rw [badChannel_one_iff, hd47] at hbad47; simpa [A48] using hbad47
  have hbad49 : BadChannel 1 A49 := by rw [badChannel_three_iff, hd48] at hbad48; simpa [A49] using hbad48
  have hbad50 : BadChannel 3 A50 := by rw [badChannel_one_iff, hd49] at hbad49; simpa [A50] using hbad49
  have hbad51 : BadChannel 2 A51 := by rw [badChannel_three_iff, hd50] at hbad50; simpa [A51] using hbad50
  have hbad52 : BadChannel 0 A52 := by rw [badChannel_two_iff, hd51] at hbad51; simpa [A52] using hbad51
  have hbad53 : BadChannel 1 A53 := by rw [badChannel_zero_iff, hd52] at hbad52; simpa [A53] using hbad52
  have hbad54 : BadChannel 0 A54 := by rw [badChannel_one_iff, hd53] at hbad53; simpa [A54] using hbad53
  rw [badChannel_zero_iff, hd54] at hbad54
  simpa using hbad54

theorem commonTwo_of_mod174449211009120179071170507_85117
    (N : Nat) (hN : N % 174449211009120179071170507 = 85117) : CommonTwo N := by
  exact commonTwo_of_mod174449211009120179071170507_pattern_1112010012101010110112000012012001012011120100120210102_85117 N
    (affineOrbit_mod174449211009120179071170507_eq_124019512228608034172146897_of_exponent_85117 N hN)

theorem physical_happy_of_mod174449211009120179071170507_85117
    (N : Nat) (hN : N % 174449211009120179071170507 = 85117) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod174449211009120179071170507_85117 N hN)

theorem four_power_happy_propagates_of_next_mod174449211009120179071170507_85117
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 174449211009120179071170507 = 85117) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod174449211009120179071170507_85117 (K+1) hNext

#check commonTwo_of_mod174449211009120179071170507_85117
#check physical_happy_of_mod174449211009120179071170507_85117
#check four_power_happy_propagates_of_next_mod174449211009120179071170507_85117

end GSTFourPowerAffineFiftyFifthTritNext
