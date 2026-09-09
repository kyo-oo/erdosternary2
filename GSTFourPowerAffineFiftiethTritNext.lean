import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFiftiethTritNext

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

private theorem affineOrbit_mod717897987691852588770249_eq_675033603700193096846763_of_exponent_65883
    (N : Nat) (hN : N % 717897987691852588770249 = 65883) : affineOrbit N % 717897987691852588770249 = 675033603700193096846763 := by
  have hExp : N % 3 ^ 50 = 65883 % 3 ^ 50 := by
    norm_num
    exact hN
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 50 N 65883).2 hExp
  have hRef : affineOrbit 65883 % 717897987691852588770249 = 675033603700193096846763 := by
    rw [affineOrbit_mod_eq_affineOrbitMod]
    decide
  have hPow : 3 ^ 50 = 717897987691852588770249 := by norm_num
  rw [hPow] at h
  exact h.trans hRef

private theorem commonTwo_of_mod717897987691852588770249_pattern_01212011121101201212100011000012112121202011101122_65883
    (N : Nat) (hAmod : affineOrbit N % 717897987691852588770249 = 675033603700193096846763) : CommonTwo N := by
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
  have hR0 : A0 % 717897987691852588770249 = 675033603700193096846763 := by simpa [A0] using hAmod
  have hR1 : A1 % 239299329230617529590083 = 225011201233397698948921 := by dsimp [A1, tail3]; omega
  have hR2 : A2 % 79766443076872509863361 = 75003733744465899649640 := by dsimp [A2, tail3]; omega
  have hR3 : A3 % 26588814358957503287787 = 25001244581488633216546 := by dsimp [A3, tail3]; omega
  have hR4 : A4 % 8862938119652501095929 = 8333748193829544405515 := by dsimp [A4, tail3]; omega
  have hR5 : A5 % 2954312706550833698643 = 2777916064609848135171 := by dsimp [A5, tail3]; omega
  have hR6 : A6 % 984770902183611232881 = 925972021536616045057 := by dsimp [A6, tail3]; omega
  have hR7 : A7 % 328256967394537077627 = 308657340512205348352 := by dsimp [A7, tail3]; omega
  have hR8 : A8 % 109418989131512359209 = 102885780170735116117 := by dsimp [A8, tail3]; omega
  have hR9 : A9 % 36472996377170786403 = 34295260056911705372 := by dsimp [A9, tail3]; omega
  have hR10 : A10 % 12157665459056928801 = 11431753352303901790 := by dsimp [A10, tail3]; omega
  have hR11 : A11 % 4052555153018976267 = 3810584450767967263 := by dsimp [A11, tail3]; omega
  have hR12 : A12 % 1350851717672992089 = 1270194816922655754 := by dsimp [A12, tail3]; omega
  have hR13 : A13 % 450283905890997363 = 423398272307551918 := by dsimp [A13, tail3]; omega
  have hR14 : A14 % 150094635296999121 = 141132757435850639 := by dsimp [A14, tail3]; omega
  have hR15 : A15 % 50031545098999707 = 47044252478616879 := by dsimp [A15, tail3]; omega
  have hR16 : A16 % 16677181699666569 = 15681417492872293 := by dsimp [A16, tail3]; omega
  have hR17 : A17 % 5559060566555523 = 5227139164290764 := by dsimp [A17, tail3]; omega
  have hR18 : A18 % 1853020188851841 = 1742379721430254 := by dsimp [A18, tail3]; omega
  have hR19 : A19 % 617673396283947 = 580793240476751 := by dsimp [A19, tail3]; omega
  have hR20 : A20 % 205891132094649 = 193597746825583 := by dsimp [A20, tail3]; omega
  have hR21 : A21 % 68630377364883 = 64532582275194 := by dsimp [A21, tail3]; omega
  have hR22 : A22 % 22876792454961 = 21510860758398 := by dsimp [A22, tail3]; omega
  have hR23 : A23 % 7625597484987 = 7170286919466 := by dsimp [A23, tail3]; omega
  have hR24 : A24 % 2541865828329 = 2390095639822 := by dsimp [A24, tail3]; omega
  have hR25 : A25 % 847288609443 = 796698546607 := by dsimp [A25, tail3]; omega
  have hR26 : A26 % 282429536481 = 265566182202 := by dsimp [A26, tail3]; omega
  have hR27 : A27 % 94143178827 = 88522060734 := by dsimp [A27, tail3]; omega
  have hR28 : A28 % 31381059609 = 29507353578 := by dsimp [A28, tail3]; omega
  have hR29 : A29 % 10460353203 = 9835784526 := by dsimp [A29, tail3]; omega
  have hR30 : A30 % 3486784401 = 3278594842 := by dsimp [A30, tail3]; omega
  have hR31 : A31 % 1162261467 = 1092864947 := by dsimp [A31, tail3]; omega
  have hR32 : A32 % 387420489 = 364288315 := by dsimp [A32, tail3]; omega
  have hR33 : A33 % 129140163 = 121429438 := by dsimp [A33, tail3]; omega
  have hR34 : A34 % 43046721 = 40476479 := by dsimp [A34, tail3]; omega
  have hR35 : A35 % 14348907 = 13492159 := by dsimp [A35, tail3]; omega
  have hR36 : A36 % 4782969 = 4497386 := by dsimp [A36, tail3]; omega
  have hR37 : A37 % 1594323 = 1499128 := by dsimp [A37, tail3]; omega
  have hR38 : A38 % 531441 = 499709 := by dsimp [A38, tail3]; omega
  have hR39 : A39 % 177147 = 166569 := by dsimp [A39, tail3]; omega
  have hR40 : A40 % 59049 = 55523 := by dsimp [A40, tail3]; omega
  have hR41 : A41 % 19683 = 18507 := by dsimp [A41, tail3]; omega
  have hR42 : A42 % 6561 = 6169 := by dsimp [A42, tail3]; omega
  have hR43 : A43 % 2187 = 2056 := by dsimp [A43, tail3]; omega
  have hR44 : A44 % 729 = 685 := by dsimp [A44, tail3]; omega
  have hR45 : A45 % 243 = 228 := by dsimp [A45, tail3]; omega
  have hR46 : A46 % 81 = 76 := by dsimp [A46, tail3]; omega
  have hR47 : A47 % 27 = 25 := by dsimp [A47, tail3]; omega
  have hR48 : A48 % 9 = 8 := by dsimp [A48, tail3]; omega
  have hR49 : A49 % 3 = 2 := by dsimp [A49, tail3]; omega
  have hd0 : lowDigit A0 = 0 := by dsimp [lowDigit]; omega
  have hd1 : lowDigit A1 = 1 := by dsimp [lowDigit]; omega
  have hd2 : lowDigit A2 = 2 := by dsimp [lowDigit]; omega
  have hd3 : lowDigit A3 = 1 := by dsimp [lowDigit]; omega
  have hd4 : lowDigit A4 = 2 := by dsimp [lowDigit]; omega
  have hd5 : lowDigit A5 = 0 := by dsimp [lowDigit]; omega
  have hd6 : lowDigit A6 = 1 := by dsimp [lowDigit]; omega
  have hd7 : lowDigit A7 = 1 := by dsimp [lowDigit]; omega
  have hd8 : lowDigit A8 = 1 := by dsimp [lowDigit]; omega
  have hd9 : lowDigit A9 = 2 := by dsimp [lowDigit]; omega
  have hd10 : lowDigit A10 = 1 := by dsimp [lowDigit]; omega
  have hd11 : lowDigit A11 = 1 := by dsimp [lowDigit]; omega
  have hd12 : lowDigit A12 = 0 := by dsimp [lowDigit]; omega
  have hd13 : lowDigit A13 = 1 := by dsimp [lowDigit]; omega
  have hd14 : lowDigit A14 = 2 := by dsimp [lowDigit]; omega
  have hd15 : lowDigit A15 = 0 := by dsimp [lowDigit]; omega
  have hd16 : lowDigit A16 = 1 := by dsimp [lowDigit]; omega
  have hd17 : lowDigit A17 = 2 := by dsimp [lowDigit]; omega
  have hd18 : lowDigit A18 = 1 := by dsimp [lowDigit]; omega
  have hd19 : lowDigit A19 = 2 := by dsimp [lowDigit]; omega
  have hd20 : lowDigit A20 = 1 := by dsimp [lowDigit]; omega
  have hd21 : lowDigit A21 = 0 := by dsimp [lowDigit]; omega
  have hd22 : lowDigit A22 = 0 := by dsimp [lowDigit]; omega
  have hd23 : lowDigit A23 = 0 := by dsimp [lowDigit]; omega
  have hd24 : lowDigit A24 = 1 := by dsimp [lowDigit]; omega
  have hd25 : lowDigit A25 = 1 := by dsimp [lowDigit]; omega
  have hd26 : lowDigit A26 = 0 := by dsimp [lowDigit]; omega
  have hd27 : lowDigit A27 = 0 := by dsimp [lowDigit]; omega
  have hd28 : lowDigit A28 = 0 := by dsimp [lowDigit]; omega
  have hd29 : lowDigit A29 = 0 := by dsimp [lowDigit]; omega
  have hd30 : lowDigit A30 = 1 := by dsimp [lowDigit]; omega
  have hd31 : lowDigit A31 = 2 := by dsimp [lowDigit]; omega
  have hd32 : lowDigit A32 = 1 := by dsimp [lowDigit]; omega
  have hd33 : lowDigit A33 = 1 := by dsimp [lowDigit]; omega
  have hd34 : lowDigit A34 = 2 := by dsimp [lowDigit]; omega
  have hd35 : lowDigit A35 = 1 := by dsimp [lowDigit]; omega
  have hd36 : lowDigit A36 = 2 := by dsimp [lowDigit]; omega
  have hd37 : lowDigit A37 = 0 := by dsimp [lowDigit]; omega
  have hd38 : lowDigit A38 = 2 := by dsimp [lowDigit]; omega
  have hd39 : lowDigit A39 = 0 := by dsimp [lowDigit]; omega
  have hd40 : lowDigit A40 = 2 := by dsimp [lowDigit]; omega
  have hd41 : lowDigit A41 = 0 := by dsimp [lowDigit]; omega
  have hd42 : lowDigit A42 = 1 := by dsimp [lowDigit]; omega
  have hd43 : lowDigit A43 = 1 := by dsimp [lowDigit]; omega
  have hd44 : lowDigit A44 = 1 := by dsimp [lowDigit]; omega
  have hd45 : lowDigit A45 = 0 := by dsimp [lowDigit]; omega
  have hd46 : lowDigit A46 = 1 := by dsimp [lowDigit]; omega
  have hd47 : lowDigit A47 = 1 := by dsimp [lowDigit]; omega
  have hd48 : lowDigit A48 = 2 := by dsimp [lowDigit]; omega
  have hd49 : lowDigit A49 = 2 := by dsimp [lowDigit]; omega
  have hbad0 : BadChannel 1 A0 := by
    dsimp [A0]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 A1 := by rw [badChannel_one_iff, hd0] at hbad0; simpa [A1] using hbad0
  have hbad2 : BadChannel 1 A2 := by rw [badChannel_zero_iff, hd1] at hbad1; simpa [A2] using hbad1
  have hbad3 : BadChannel 3 A3 := by rw [badChannel_one_iff, hd2] at hbad2; simpa [A3] using hbad2
  have hbad4 : BadChannel 2 A4 := by rw [badChannel_three_iff, hd3] at hbad3; simpa [A4] using hbad3
  have hbad5 : BadChannel 3 A5 := by rw [badChannel_two_iff, hd4] at hbad4; simpa [A5] using hbad4
  have hbad6 : BadChannel 1 A6 := by rw [badChannel_three_iff, hd5] at hbad5; simpa [A6] using hbad5
  have hbad7 : BadChannel 1 A7 := by rw [badChannel_one_iff, hd6] at hbad6; simpa [A7] using hbad6
  have hbad8 : BadChannel 1 A8 := by rw [badChannel_one_iff, hd7] at hbad7; simpa [A8] using hbad7
  have hbad9 : BadChannel 1 A9 := by rw [badChannel_one_iff, hd8] at hbad8; simpa [A9] using hbad8
  have hbad10 : BadChannel 3 A10 := by rw [badChannel_one_iff, hd9] at hbad9; simpa [A10] using hbad9
  have hbad11 : BadChannel 2 A11 := by rw [badChannel_three_iff, hd10] at hbad10; simpa [A11] using hbad10
  have hbad12 : BadChannel 2 A12 := by rw [badChannel_two_iff, hd11] at hbad11; simpa [A12] using hbad11
  have hbad13 : BadChannel 0 A13 := by rw [badChannel_two_iff, hd12] at hbad12; simpa [A13] using hbad12
  have hbad14 : BadChannel 1 A14 := by rw [badChannel_zero_iff, hd13] at hbad13; simpa [A14] using hbad13
  have hbad15 : BadChannel 3 A15 := by rw [badChannel_one_iff, hd14] at hbad14; simpa [A15] using hbad14
  have hbad16 : BadChannel 1 A16 := by rw [badChannel_three_iff, hd15] at hbad15; simpa [A16] using hbad15
  have hbad17 : BadChannel 1 A17 := by rw [badChannel_one_iff, hd16] at hbad16; simpa [A17] using hbad16
  have hbad18 : BadChannel 3 A18 := by rw [badChannel_one_iff, hd17] at hbad17; simpa [A18] using hbad17
  have hbad19 : BadChannel 2 A19 := by rw [badChannel_three_iff, hd18] at hbad18; simpa [A19] using hbad18
  have hbad20 : BadChannel 3 A20 := by rw [badChannel_two_iff, hd19] at hbad19; simpa [A20] using hbad19
  have hbad21 : BadChannel 2 A21 := by rw [badChannel_three_iff, hd20] at hbad20; simpa [A21] using hbad20
  have hbad22 : BadChannel 2 A22 := by rw [badChannel_two_iff, hd21] at hbad21; simpa [A22] using hbad21
  have hbad23 : BadChannel 0 A23 := by rw [badChannel_two_iff, hd22] at hbad22; simpa [A23] using hbad22
  have hbad24 : BadChannel 0 A24 := by rw [badChannel_zero_iff, hd23] at hbad23; simpa [A24] using hbad23
  have hbad25 : BadChannel 1 A25 := by rw [badChannel_zero_iff, hd24] at hbad24; simpa [A25] using hbad24
  have hbad26 : BadChannel 1 A26 := by rw [badChannel_one_iff, hd25] at hbad25; simpa [A26] using hbad25
  have hbad27 : BadChannel 0 A27 := by rw [badChannel_one_iff, hd26] at hbad26; simpa [A27] using hbad26
  have hbad28 : BadChannel 0 A28 := by rw [badChannel_zero_iff, hd27] at hbad27; simpa [A28] using hbad27
  have hbad29 : BadChannel 0 A29 := by rw [badChannel_zero_iff, hd28] at hbad28; simpa [A29] using hbad28
  have hbad30 : BadChannel 0 A30 := by rw [badChannel_zero_iff, hd29] at hbad29; simpa [A30] using hbad29
  have hbad31 : BadChannel 1 A31 := by rw [badChannel_zero_iff, hd30] at hbad30; simpa [A31] using hbad30
  have hbad32 : BadChannel 3 A32 := by rw [badChannel_one_iff, hd31] at hbad31; simpa [A32] using hbad31
  have hbad33 : BadChannel 2 A33 := by rw [badChannel_three_iff, hd32] at hbad32; simpa [A33] using hbad32
  have hbad34 : BadChannel 2 A34 := by rw [badChannel_two_iff, hd33] at hbad33; simpa [A34] using hbad33
  have hbad35 : BadChannel 3 A35 := by rw [badChannel_two_iff, hd34] at hbad34; simpa [A35] using hbad34
  have hbad36 : BadChannel 2 A36 := by rw [badChannel_three_iff, hd35] at hbad35; simpa [A36] using hbad35
  have hbad37 : BadChannel 3 A37 := by rw [badChannel_two_iff, hd36] at hbad36; simpa [A37] using hbad36
  have hbad38 : BadChannel 1 A38 := by rw [badChannel_three_iff, hd37] at hbad37; simpa [A38] using hbad37
  have hbad39 : BadChannel 3 A39 := by rw [badChannel_one_iff, hd38] at hbad38; simpa [A39] using hbad38
  have hbad40 : BadChannel 1 A40 := by rw [badChannel_three_iff, hd39] at hbad39; simpa [A40] using hbad39
  have hbad41 : BadChannel 3 A41 := by rw [badChannel_one_iff, hd40] at hbad40; simpa [A41] using hbad40
  have hbad42 : BadChannel 1 A42 := by rw [badChannel_three_iff, hd41] at hbad41; simpa [A42] using hbad41
  have hbad43 : BadChannel 1 A43 := by rw [badChannel_one_iff, hd42] at hbad42; simpa [A43] using hbad42
  have hbad44 : BadChannel 1 A44 := by rw [badChannel_one_iff, hd43] at hbad43; simpa [A44] using hbad43
  have hbad45 : BadChannel 1 A45 := by rw [badChannel_one_iff, hd44] at hbad44; simpa [A45] using hbad44
  have hbad46 : BadChannel 0 A46 := by rw [badChannel_one_iff, hd45] at hbad45; simpa [A46] using hbad45
  have hbad47 : BadChannel 1 A47 := by rw [badChannel_zero_iff, hd46] at hbad46; simpa [A47] using hbad46
  have hbad48 : BadChannel 1 A48 := by rw [badChannel_one_iff, hd47] at hbad47; simpa [A48] using hbad47
  have hbad49 : BadChannel 3 A49 := by rw [badChannel_one_iff, hd48] at hbad48; simpa [A49] using hbad48
  rw [badChannel_three_iff, hd49] at hbad49
  simpa using hbad49

theorem commonTwo_of_mod717897987691852588770249_65883
    (N : Nat) (hN : N % 717897987691852588770249 = 65883) : CommonTwo N := by
  exact commonTwo_of_mod717897987691852588770249_pattern_01212011121101201212100011000012112121202011101122_65883 N
    (affineOrbit_mod717897987691852588770249_eq_675033603700193096846763_of_exponent_65883 N hN)

theorem physical_happy_of_mod717897987691852588770249_65883
    (N : Nat) (hN : N % 717897987691852588770249 = 65883) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^N) q)
      (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod717897987691852588770249_65883 N hN)

theorem four_power_happy_propagates_of_next_mod717897987691852588770249_65883
    (K p : Nat) (hK : 13 ≤ K) (hp : 1 ≤ p)
    (hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 717897987691852588770249 = 65883) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod717897987691852588770249_65883 (K+1) hNext

#check commonTwo_of_mod717897987691852588770249_65883
#check physical_happy_of_mod717897987691852588770249_65883
#check four_power_happy_propagates_of_next_mod717897987691852588770249_65883

end GSTFourPowerAffineFiftiethTritNext
