import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 5000000
set_option maxHeartbeats 30000000

namespace GSTFourPowerAffineFiftyThirdTritNext

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

private theorem affineOrbit_mod19383245667680019896796723_eq_18090587917995305367585538_of_exponent_279775
    (N : Nat) (hN : N % 19383245667680019896796723 = 279775) : affineOrbit N % 19383245667680019896796723 = 18090587917995305367585538 := by
  have hExp : N % 3 ^ 53 = 279775 % 3 ^ 53 := by
    norm_num
    exact hN
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 53 N 279775).2 hExp
  have hRef : affineOrbit 279775 % 19383245667680019896796723 = 18090587917995305367585538 := by
    rw [affineOrbit_mod_eq_affineOrbitMod]
    decide
  have hPow : 3 ^ 53 = 19383245667680019896796723 := by norm_num
  rw [hPow] at h
  exact h.trans hRef

private theorem commonTwo_of_mod19383245667680019896796723_pattern_10001200120101101210112120121120211011111001101210122_279775
    (N : Nat) (hAmod : affineOrbit N % 19383245667680019896796723 = 18090587917995305367585538) : CommonTwo N := by
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
  have hR0 : A0 % 19383245667680019896796723 = 18090587917995305367585538 := by simpa [A0] using hAmod
  have hR1 : A1 % 6461081889226673298932241 = 6030195972665101789195179 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 2153693963075557766310747 = 2010065324221700596398393 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 717897987691852588770249 = 670021774740566865466131 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 239299329230617529590083 = 223340591580188955155377 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 79766443076872509863361 = 74446863860062985051792 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 26588814358957503287787 = 24815621286687661683930 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 8862938119652501095929 = 8271873762229220561310 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 2954312706550833698643 = 2757291254076406853770 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 984770902183611232881 = 919097084692135617923 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 328256967394537077627 = 306365694897378539307 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 109418989131512359209 = 102121898299126179769 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 36472996377170786403 = 34040632766375393256 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 12157665459056928801 = 11346877588791797752 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 4052555153018976267 = 3782292529597265917 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 1350851717672992089 = 1260764176532421972 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 450283905890997363 = 420254725510807324 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 150094635296999121 = 140084908503602441 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 50031545098999707 = 46694969501200813 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 16677181699666569 = 15564989833733604 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 5559060566555523 = 5188329944577868 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 1853020188851841 = 1729443314859289 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 617673396283947 = 576481104953096 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 205891132094649 = 192160368317698 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 68630377364883 = 64053456105899 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 22876792454961 = 21351152035299 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 7625597484987 = 7117050678433 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 2541865828329 = 2372350226144 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 847288609443 = 790783408714 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 282429536481 = 263594469571 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 94143178827 = 87864823190 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 31381059609 = 29288274396 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 10460353203 = 9762758132 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 3486784401 = 3254252710 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 1162261467 = 1084750903 := by dsimp [A34, tail3]; omega
  have hR35 : A35 % 387420489 = 361583634 := by dsimp [A35, tail3]; omega
  have hR36 : A36 % 129140163 = 120527878 := by dsimp [A36, tail3]; omega
  have hR37 : A37 % 43046721 = 40175959 := by dsimp [A37, tail3]; omega
  have hR38 : A38 % 14348907 = 13391986 := by dsimp [A38, tail3]; omega
  have hR39 : A39 % 4782969 = 4463995 := by dsimp [A39, tail3]; omega
  have hR40 : A40 % 1594323 = 1487998 := by dsimp [A40, tail3]; omega
  have hR41 : A41 % 531441 = 495999 := by dsimp [A41, tail3]; omega
  have hR42 : A42 % 177147 = 165333 := by dsimp [A42, tail3]; omega
  have hR43 : A43 % 59049 = 55111 := by dsimp [A43, tail3]; omega
  have hR44 : A44 % 19683 = 18370 := by dsimp [A44, tail3]; omega
  have hR45 : A45 % 6561 = 6123 := by dsimp [A45, tail3]; omega
  have hR46 : A46 % 2187 = 2041 := by dsimp [A46, tail3]; omega
  have hR47 : A47 % 729 = 680 := by dsimp [A47, tail3]; omega
  have hR48 : A48 % 243 = 226 := by dsimp [A48, tail3]; omega
  have hR49 : A49 % 81 = 75 := by dsimp [A49, tail3]; omega
  have hR50 : A50 % 27 = 25 := by dsimp [A50, tail3]; omega
  have hR51 : A51 % 9 = 8 := by dsimp [A51, tail3]; omega
  have hR52 : A52 % 3 = 2 := by dsimp [A52, tail3]; omega
  have hd0 : lowDigit A0 = 1 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 0 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 0 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 0 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 1 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 2 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 0 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 0 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 1 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 2 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 0 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 1 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 0 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 1 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 0 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 1 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 0 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 1 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 1 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 2 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 1 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 2 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 0 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 1 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 2 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 1 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 1 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 2 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 0 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 2 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 1 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 1 := by dsimp [lowDigit]; omega
  have hd35 : lowDigit A35 = 0 := by dsimp [lowDigit]; omega
  have hd36 : lowDigit A36 = 1 := by dsimp [lowDigit]; omega
  have hd37 : lowDigit A37 = 1 := by dsimp [lowDigit]; omega
  have hd38 : lowDigit A38 = 1 := by dsimp [lowDigit]; omega
  have hd39 : lowDigit A39 = 1 := by dsimp [lowDigit]; omega
  have hd40 : lowDigit A40 = 1 := by dsimp [lowDigit]; omega
  have hd41 : lowDigit A41 = 0 := by dsimp [lowDigit]; omega
  have hd42 : lowDigit A42 = 0 := by dsimp [lowDigit]; omega
  have hd43 : lowDigit A43 = 1 := by dsimp [lowDigit]; omega
  have hd44 : lowDigit A44 = 1 := by dsimp [lowDigit]; omega
  have hd45 : lowDigit A45 = 0 := by dsimp [lowDigit]; omega
  have hd46 : lowDigit A46 = 1 := by dsimp [lowDigit]; omega
  have hd47 : lowDigit A47 = 2 := by dsimp [lowDigit]; omega
  have hd48 : lowDigit A48 = 1 := by dsimp [lowDigit]; omega
  have hd49 : lowDigit A49 = 0 := by dsimp [lowDigit]; omega
  have hd50 : lowDigit A50 = 1 := by dsimp [lowDigit]; omega
  have hd51 : lowDigit A51 = 2 := by dsimp [lowDigit]; omega
  have hd52 : lowDigit A52 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 0 A2 := by rw [badChannel_one_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 0 A3 := by rw [badChannel_zero_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 0 A4 := by rw [badChannel_zero_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 1 A5 := by rw [badChannel_zero_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 3 A6 := by rw [badChannel_one_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 1 A7 := by rw [badChannel_three_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 0 A8 := by rw [badChannel_one_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 1 A9 := by rw [badChannel_zero_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 3 A10 := by rw [badChannel_one_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 1 A11 := by rw [badChannel_three_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 1 A12 := by rw [badChannel_one_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 0 A13 := by rw [badChannel_one_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 1 A14 := by rw [badChannel_zero_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 1 A15 := by rw [badChannel_one_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 0 A16 := by rw [badChannel_one_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_zero_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 2 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 0 A20 := by rw [badChannel_two_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 1 A21 := by rw [badChannel_zero_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 1 A22 := by rw [badChannel_one_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 3 A23 := by rw [badChannel_one_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 2 A24 := by rw [badChannel_three_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 3 A25 := by rw [badChannel_two_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 1 A26 := by rw [badChannel_three_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 1 A27 := by rw [badChannel_one_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 3 A28 := by rw [badChannel_one_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 2 A29 := by rw [badChannel_three_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 2 A30 := by rw [badChannel_two_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 3 A31 := by rw [badChannel_two_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 1 A32 := by rw [badChannel_three_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 3 A33 := by rw [badChannel_one_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 2 A34 := by rw [badChannel_three_iff, hd33] at hbad33; simpa [A34] using hbad33
  have hbad35 : BadChannel 2 A35 := by rw [badChannel_two_iff, hd34] at hbad34; simpa [A35] using hbad34
  have hbad36 : BadChannel 0 A36 := by rw [badChannel_two_iff, hd35] at hbad35; simpa [A36] using hbad35
  have hbad37 : BadChannel 1 A37 := by rw [badChannel_zero_iff, hd36] at hbad36; simpa [A37] using hbad36
  have hbad38 : BadChannel 1 A38 := by rw [badChannel_one_iff, hd37] at hbad37; simpa [A38] using hbad37
  have hbad39 : BadChannel 1 A39 := by rw [badChannel_one_iff, hd38] at hbad38; simpa [A39] using hbad38
  have hbad40 : BadChannel 1 A40 := by rw [badChannel_one_iff, hd39] at hbad39; simpa [A40] using hbad39
  have hbad41 : BadChannel 1 A41 := by rw [badChannel_one_iff, hd40] at hbad40; simpa [A41] using hbad40
  have hbad42 : BadChannel 0 A42 := by rw [badChannel_one_iff, hd41] at hbad41; simpa [A42] using hbad41
  have hbad43 : BadChannel 0 A43 := by rw [badChannel_zero_iff, hd42] at hbad42; simpa [A43] using hbad42
  have hbad44 : BadChannel 1 A44 := by rw [badChannel_zero_iff, hd43] at hbad43; simpa [A44] using hbad43
  have hbad45 : BadChannel 1 A45 := by rw [badChannel_one_iff, hd44] at hbad44; simpa [A45] using hbad44
  have hbad46 : BadChannel 0 A46 := by rw [badChannel_one_iff, hd45] at hbad45; simpa [A46] using hbad45
  have hbad47 : BadChannel 1 A47 := by rw [badChannel_zero_iff, hd46] at hbad46; simpa [A47] using hbad46
  have hbad48 : BadChannel 3 A48 := by rw [badChannel_one_iff, hd47] at hbad47; simpa [A48] using hbad47
  have hbad49 : BadChannel 2 A49 := by rw [badChannel_three_iff, hd48] at hbad48; simpa [A49] using hbad48
  have hbad50 : BadChannel 0 A50 := by rw [badChannel_two_iff, hd49] at hbad49; simpa [A50] using hbad49
  have hbad51 : BadChannel 1 A51 := by rw [badChannel_zero_iff, hd50] at hbad50; simpa [A51] using hbad50
  have hbad52 : BadChannel 3 A52 := by rw [badChannel_one_iff, hd51] at hbad51; simpa [A52] using hbad51
  rw [badChannel_three_iff, hd52] at hbad52
  simpa using hbad52

theorem commonTwo_of_mod19383245667680019896796723_279775
    (N : Nat) (hN : N % 19383245667680019896796723 = 279775) : CommonTwo N := by
  exact commonTwo_of_mod19383245667680019896796723_pattern_10001200120101101210112120121120211011111001101210122_279775 N
    (affineOrbit_mod19383245667680019896796723_eq_18090587917995305367585538_of_exponent_279775 N hN)

theorem physical_happy_of_mod19383245667680019896796723_279775
    (N : Nat) (hN : N % 19383245667680019896796723 = 279775) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod19383245667680019896796723_279775 N hN)

theorem four_power_happy_propagates_of_next_mod19383245667680019896796723_279775
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 19383245667680019896796723 = 279775) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod19383245667680019896796723_279775 (K+1) hNext

#check commonTwo_of_mod19383245667680019896796723_279775
#check physical_happy_of_mod19383245667680019896796723_279775
#check four_power_happy_propagates_of_next_mod19383245667680019896796723_279775

end GSTFourPowerAffineFiftyThirdTritNext
