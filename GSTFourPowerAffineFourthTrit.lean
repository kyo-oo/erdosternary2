import GSTFourPowerAffineThirdTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFourthTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod81_eq_of_exponent
    {N r : Nat} (hr : r < 81) (hN : N % 81 = r) :
    affineOrbit N % 81 = affineOrbit r % 81 := by
  exact (affineOrbit_residue_eq_iff_exponent_residue_eq 4 N r).2 (by
    simpa [Nat.mod_eq_of_lt hr] using hN)

private theorem affineOrbit_mod81_eq_56_of_exponent
    {N : Nat} (hN : N % 81 = 8) : affineOrbit N % 81 = 56 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 8) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_77_of_exponent
    {N : Nat} (hN : N % 81 = 20) : affineOrbit N % 81 = 77 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 20) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_74_of_exponent
    {N : Nat} (hN : N % 81 = 53) : affineOrbit N % 81 = 74 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 53) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_54_of_exponent
    {N : Nat} (hN : N % 81 = 54) : affineOrbit N % 81 = 54 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 54) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_55_of_exponent
    {N : Nat} (hN : N % 81 = 55) : affineOrbit N % 81 = 55 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 55) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_59_of_exponent
    {N : Nat} (hN : N % 81 = 56) : affineOrbit N % 81 = 59 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 56) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_75_of_exponent
    {N : Nat} (hN : N % 81 = 57) : affineOrbit N % 81 = 75 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 57) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_58_of_exponent
    {N : Nat} (hN : N % 81 = 58) : affineOrbit N % 81 = 58 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 58) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_57_of_exponent
    {N : Nat} (hN : N % 81 = 66) : affineOrbit N % 81 = 57 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 66) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod81_eq_76_of_exponent
    {N : Nat} (hN : N % 81 = 76) : affineOrbit N % 81 = 76 := by
  have h := affineOrbit_mod81_eq_of_exponent (N := N) (r := 76) (by norm_num) hN
  norm_num [affineOrbit] at h
  exact h

private theorem commonTwo_of_mod81_pattern_2002
    (N : Nat) (hAmod : affineOrbit N % 81 = 56) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad3 : BadChannel 3 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad31 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_three_iff, hd1] at hbad3; simpa using hbad3
  have hbad310 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad31; simpa using hbad31
  rw [badChannel_zero_iff, hd3] at hbad310
  simpa using hbad310

private theorem commonTwo_of_mod81_pattern_2122
    (N : Nat) (hAmod : affineOrbit N % 81 = 77) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad3 : BadChannel 3 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad32 : BadChannel 2 (tail3 (tail3 A)) := by rw [badChannel_three_iff, hd1] at hbad3; simpa using hbad3
  have hbad323 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by rw [badChannel_two_iff, hd2] at hbad32; simpa using hbad32
  rw [badChannel_three_iff, hd3] at hbad323
  simpa using hbad323

private theorem commonTwo_of_mod81_pattern_2022
    (N : Nat) (hAmod : affineOrbit N % 81 = 74) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad3 : BadChannel 3 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad31 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_three_iff, hd1] at hbad3; simpa using hbad3
  have hbad313 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad31; simpa using hbad31
  rw [badChannel_three_iff, hd3] at hbad313
  simpa using hbad313

private theorem commonTwo_of_mod81_pattern_0002
    (N : Nat) (hAmod : affineOrbit N % 81 = 54) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad0 : BadChannel 0 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad00 : BadChannel 0 (tail3 (tail3 A)) := by rw [badChannel_zero_iff, hd1] at hbad0; simpa using hbad0
  have hbad000 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_zero_iff, hd2] at hbad00; simpa using hbad00
  rw [badChannel_zero_iff, hd3] at hbad000
  simpa using hbad000

private theorem commonTwo_of_mod81_pattern_1002
    (N : Nat) (hAmod : affineOrbit N % 81 = 55) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad11 : BadChannel 1 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad110 : BadChannel 0 (tail3 (tail3 A)) := by rw [badChannel_one_iff, hd1] at hbad11; simpa using hbad11
  have hbad1100 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_zero_iff, hd2] at hbad110; simpa using hbad110
  rw [badChannel_zero_iff, hd3] at hbad1100
  simpa using hbad1100

private theorem commonTwo_of_mod81_pattern_2102
    (N : Nat) (hAmod : affineOrbit N % 81 = 59) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad3 : BadChannel 3 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad32 : BadChannel 2 (tail3 (tail3 A)) := by rw [badChannel_three_iff, hd1] at hbad3; simpa using hbad3
  have hbad320 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_two_iff, hd2] at hbad32; simpa using hbad32
  rw [badChannel_zero_iff, hd3] at hbad320
  simpa using hbad320

private theorem commonTwo_of_mod81_pattern_0122
    (N : Nat) (hAmod : affineOrbit N % 81 = 75) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad0 : BadChannel 0 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad01 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_zero_iff, hd1] at hbad0; simpa using hbad0
  have hbad013 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad01; simpa using hbad01
  rw [badChannel_three_iff, hd3] at hbad013
  simpa using hbad013

private theorem commonTwo_of_mod81_pattern_1102
    (N : Nat) (hAmod : affineOrbit N % 81 = 58) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad11 : BadChannel 1 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad111 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_one_iff, hd1] at hbad11; simpa using hbad11
  have hbad1110 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad111; simpa using hbad111
  rw [badChannel_zero_iff, hd3] at hbad1110
  simpa using hbad1110

private theorem commonTwo_of_mod81_pattern_0102
    (N : Nat) (hAmod : affineOrbit N % 81 = 57) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad0 : BadChannel 0 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad01 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_zero_iff, hd1] at hbad0; simpa using hbad0
  have hbad010 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad01; simpa using hbad01
  rw [badChannel_zero_iff, hd3] at hbad010
  simpa using hbad010

private theorem commonTwo_of_mod81_pattern_1122
    (N : Nat) (hAmod : affineOrbit N % 81 = 76) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad1 : BadChannel 1 A := by dsimp [A]; exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad11 : BadChannel 1 (tail3 A) := by rw [badChannel_one_iff, hd0] at hbad1; simpa using hbad1
  have hbad111 : BadChannel 1 (tail3 (tail3 A)) := by rw [badChannel_one_iff, hd1] at hbad11; simpa using hbad11
  have hbad1113 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by rw [badChannel_one_iff, hd2] at hbad111; simpa using hbad111
  rw [badChannel_three_iff, hd3] at hbad1113
  simpa using hbad1113

theorem commonTwo_of_mod81_eight (N : Nat) (hN : N % 81 = 8) : CommonTwo N :=
  commonTwo_of_mod81_pattern_2002 N (affineOrbit_mod81_eq_56_of_exponent hN)

theorem commonTwo_of_mod81_twenty (N : Nat) (hN : N % 81 = 20) : CommonTwo N :=
  commonTwo_of_mod81_pattern_2122 N (affineOrbit_mod81_eq_77_of_exponent hN)

theorem commonTwo_of_mod81_fiftythree (N : Nat) (hN : N % 81 = 53) : CommonTwo N :=
  commonTwo_of_mod81_pattern_2022 N (affineOrbit_mod81_eq_74_of_exponent hN)

theorem commonTwo_of_mod81_fiftyfour (N : Nat) (hN : N % 81 = 54) : CommonTwo N :=
  commonTwo_of_mod81_pattern_0002 N (affineOrbit_mod81_eq_54_of_exponent hN)

theorem commonTwo_of_mod81_fiftyfive (N : Nat) (hN : N % 81 = 55) : CommonTwo N :=
  commonTwo_of_mod81_pattern_1002 N (affineOrbit_mod81_eq_55_of_exponent hN)

theorem commonTwo_of_mod81_fiftysix (N : Nat) (hN : N % 81 = 56) : CommonTwo N :=
  commonTwo_of_mod81_pattern_2102 N (affineOrbit_mod81_eq_59_of_exponent hN)

theorem commonTwo_of_mod81_fiftyseven (N : Nat) (hN : N % 81 = 57) : CommonTwo N :=
  commonTwo_of_mod81_pattern_0122 N (affineOrbit_mod81_eq_75_of_exponent hN)

theorem commonTwo_of_mod81_fiftyeight (N : Nat) (hN : N % 81 = 58) : CommonTwo N :=
  commonTwo_of_mod81_pattern_1102 N (affineOrbit_mod81_eq_58_of_exponent hN)

theorem commonTwo_of_mod81_sixtysix (N : Nat) (hN : N % 81 = 66) : CommonTwo N :=
  commonTwo_of_mod81_pattern_0102 N (affineOrbit_mod81_eq_57_of_exponent hN)

theorem commonTwo_of_mod81_seventysix (N : Nat) (hN : N % 81 = 76) : CommonTwo N :=
  commonTwo_of_mod81_pattern_1122 N (affineOrbit_mod81_eq_76_of_exponent hN)

/-- All genuinely new fourth-trit affine kill classes, converted to an actual
physical Happy row. These are exactly the classes whose bad-channel path first
dies on the fourth ternary read rather than in the already-certified mod-9 or
mod-27 sectors. -/
theorem physical_happy_of_mod81_affine_fourth_kills
    (N : Nat)
    (hN : N % 81 = 8 ∨ N % 81 = 20 ∨ N % 81 = 53 ∨ N % 81 = 54 ∨
      N % 81 = 55 ∨ N % 81 = 56 ∨ N % 81 = 57 ∨ N % 81 = 58 ∨
      N % 81 = 66 ∨ N % 81 = 76) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  rcases hN with h8 | h20 | h53 | h54 | h55 | h56 | h57 | h58 | h66 | h76
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_eight N h8)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_twenty N h20)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftythree N h53)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyfour N h54)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyfive N h55)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftysix N h56)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyseven N h57)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyeight N h58)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_sixtysix N h66)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_seventysix N h76)

/-- Backward-compatible single-sector constructor retained for downstream users. -/
theorem physical_happy_of_mod81_fiftyfour
    (N : Nat) (hN : N % 81 = 54) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N (commonTwo_of_mod81_fiftyfour N hN)

/-- Task-3.3-shaped relocation constructor for the complete genuinely new
fourth-trit sector. -/
theorem four_power_happy_propagates_of_next_mod81_affine_fourth_kills
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 81 = 8 ∨ (K+1) % 81 = 20 ∨ (K+1) % 81 = 53 ∨
      (K+1) % 81 = 54 ∨ (K+1) % 81 = 55 ∨ (K+1) % 81 = 56 ∨
      (K+1) % 81 = 57 ∨ (K+1) % 81 = 58 ∨ (K+1) % 81 = 66 ∨
      (K+1) % 81 = 76) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod81_affine_fourth_kills (K+1) hNext

/-- Backward-compatible single-sector relocation constructor. -/
theorem four_power_happy_propagates_of_next_mod81_fiftyfour
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 81 = 54) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod81_fiftyfour (K+1) hNext

#check commonTwo_of_mod81_eight
#check commonTwo_of_mod81_twenty
#check commonTwo_of_mod81_fiftythree
#check commonTwo_of_mod81_fiftyfour
#check commonTwo_of_mod81_fiftyfive
#check commonTwo_of_mod81_fiftysix
#check commonTwo_of_mod81_fiftyseven
#check commonTwo_of_mod81_fiftyeight
#check commonTwo_of_mod81_sixtysix
#check commonTwo_of_mod81_seventysix
#check physical_happy_of_mod81_affine_fourth_kills
#check four_power_happy_propagates_of_next_mod81_affine_fourth_kills
#print axioms physical_happy_of_mod81_affine_fourth_kills
#print axioms four_power_happy_propagates_of_next_mod81_affine_fourth_kills

end GSTFourPowerAffineFourthTrit
