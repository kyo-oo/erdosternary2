import GSTFourPowerAffineFourthTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineFifthTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

/-- Exact fifth-prefix transfer from the exponent to the affine orbit. -/
private theorem affineOrbit_mod243_eq_of_exponent
    {N r : Nat} (hr : r < 243) (hN : N % 243 = r) :
    affineOrbit N % 243 = affineOrbit r % 243 := by
  exact (affineOrbit_residue_eq_iff_exponent_residue_eq 5 N r).2 (by
    simpa [Nat.mod_eq_of_lt hr] using hN)

/-- Exact bad-channel eliminations for every residue whose first certified
kill occurs on the fifth affine ternary read. -/
private theorem commonTwo_of_mod243_pattern_01122
    (N : Nat) (hAmod : affineOrbit N % 243 = 228) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_21122
    (N : Nat) (hAmod : affineOrbit N % 243 = 230) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_01102
    (N : Nat) (hAmod : affineOrbit N % 243 = 174) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_12002
    (N : Nat) (hAmod : affineOrbit N % 243 = 169) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_12102
    (N : Nat) (hAmod : affineOrbit N % 243 = 178) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_20122
    (N : Nat) (hAmod : affineOrbit N % 243 = 227) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_11002
    (N : Nat) (hAmod : affineOrbit N % 243 = 166) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_00122
    (N : Nat) (hAmod : affineOrbit N % 243 = 225) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_10102
    (N : Nat) (hAmod : affineOrbit N % 243 = 172) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_12022
    (N : Nat) (hAmod : affineOrbit N % 243 = 223) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_20002
    (N : Nat) (hAmod : affineOrbit N % 243 = 164) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_00102
    (N : Nat) (hAmod : affineOrbit N % 243 = 171) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_12122
    (N : Nat) (hAmod : affineOrbit N % 243 = 232) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_10122
    (N : Nat) (hAmod : affineOrbit N % 243 = 226) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_21102
    (N : Nat) (hAmod : affineOrbit N % 243 = 176) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_00002
    (N : Nat) (hAmod : affineOrbit N % 243 = 162) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_10002
    (N : Nat) (hAmod : affineOrbit N % 243 = 163) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_21002
    (N : Nat) (hAmod : affineOrbit N % 243 = 167) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 2 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_two_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_01002
    (N : Nat) (hAmod : affineOrbit N % 243 = 165) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_11102
    (N : Nat) (hAmod : affineOrbit N % 243 = 175) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_20102
    (N : Nat) (hAmod : affineOrbit N % 243 = 173) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

private theorem commonTwo_of_mod243_pattern_11122
    (N : Nat) (hAmod : affineOrbit N % 243 = 229) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit (A) = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 (A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 (A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 (A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 (A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 (A)) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 (A))) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 (A)))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (A))))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

/-- Exponent-side constructors for all 22 genuinely-new fifth-read classes. -/
theorem commonTwo_of_mod243_r21
    (N : Nat) (hN : N % 243 = 21) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 228 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 21) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_01122 N hA

theorem commonTwo_of_mod243_r38
    (N : Nat) (hN : N % 243 = 38) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 230 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 38) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_21122 N hA

theorem commonTwo_of_mod243_r48
    (N : Nat) (hN : N % 243 = 48) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 174 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 48) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_01102 N hA

theorem commonTwo_of_mod243_r61
    (N : Nat) (hN : N % 243 = 61) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 169 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 61) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_12002 N hA

theorem commonTwo_of_mod243_r70
    (N : Nat) (hN : N % 243 = 70) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 178 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 70) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_12102 N hA

theorem commonTwo_of_mod243_r71
    (N : Nat) (hN : N % 243 = 71) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 227 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 71) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_20122 N hA

theorem commonTwo_of_mod243_r85
    (N : Nat) (hN : N % 243 = 85) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 166 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 85) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_11002 N hA

theorem commonTwo_of_mod243_r90
    (N : Nat) (hN : N % 243 = 90) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 225 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 90) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_00122 N hA

theorem commonTwo_of_mod243_r91
    (N : Nat) (hN : N % 243 = 91) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 172 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 91) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_10102 N hA

theorem commonTwo_of_mod243_r115
    (N : Nat) (hN : N % 243 = 115) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 223 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 115) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_12022 N hA

theorem commonTwo_of_mod243_r116
    (N : Nat) (hN : N % 243 = 116) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 164 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 116) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_20002 N hA

theorem commonTwo_of_mod243_r117
    (N : Nat) (hN : N % 243 = 117) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 171 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 117) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_00102 N hA

theorem commonTwo_of_mod243_r124
    (N : Nat) (hN : N % 243 = 124) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 232 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 124) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_12122 N hA

theorem commonTwo_of_mod243_r145
    (N : Nat) (hN : N % 243 = 145) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 226 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 145) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_10122 N hA

theorem commonTwo_of_mod243_r146
    (N : Nat) (hN : N % 243 = 146) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 176 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 146) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_21102 N hA

theorem commonTwo_of_mod243_r162
    (N : Nat) (hN : N % 243 = 162) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 162 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 162) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_00002 N hA

theorem commonTwo_of_mod243_r163
    (N : Nat) (hN : N % 243 = 163) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 163 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 163) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_10002 N hA

theorem commonTwo_of_mod243_r164
    (N : Nat) (hN : N % 243 = 164) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 167 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 164) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_21002 N hA

theorem commonTwo_of_mod243_r174
    (N : Nat) (hN : N % 243 = 174) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 165 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 174) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_01002 N hA

theorem commonTwo_of_mod243_r175
    (N : Nat) (hN : N % 243 = 175) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 175 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 175) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_11102 N hA

theorem commonTwo_of_mod243_r179
    (N : Nat) (hN : N % 243 = 179) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 173 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 179) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_20102 N hA

theorem commonTwo_of_mod243_r229
    (N : Nat) (hN : N % 243 = 229) : CommonTwo N := by
  have hA : affineOrbit N % 243 = 229 := by
    have h := affineOrbit_mod243_eq_of_exponent (N := N) (r := 229) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod243_pattern_11122 N hA

/-- Backward-compatible named constructor retained for the first class that
was introduced on this route. -/
theorem commonTwo_of_mod243_fortyeight
    (N : Nat) (hN : N % 243 = 48) : CommonTwo N := by
  exact commonTwo_of_mod243_r48 N hN

/-- Complete fifth-trit kill sector, on the exponent side. -/
theorem commonTwo_of_mod243_affine_fifth_kills
    (N : Nat)
    (hKill :
      N % 243 = 21 ∨ N % 243 = 38 ∨ N % 243 = 48 ∨ N % 243 = 61 ∨
      N % 243 = 70 ∨ N % 243 = 71 ∨ N % 243 = 85 ∨ N % 243 = 90 ∨
      N % 243 = 91 ∨ N % 243 = 115 ∨ N % 243 = 116 ∨ N % 243 = 117 ∨
      N % 243 = 124 ∨ N % 243 = 145 ∨ N % 243 = 146 ∨ N % 243 = 162 ∨
      N % 243 = 163 ∨ N % 243 = 164 ∨ N % 243 = 174 ∨ N % 243 = 175 ∨
      N % 243 = 179 ∨ N % 243 = 229) :
    CommonTwo N := by
  rcases hKill with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact commonTwo_of_mod243_r21 N h
  · exact commonTwo_of_mod243_r38 N h
  · exact commonTwo_of_mod243_r48 N h
  · exact commonTwo_of_mod243_r61 N h
  · exact commonTwo_of_mod243_r70 N h
  · exact commonTwo_of_mod243_r71 N h
  · exact commonTwo_of_mod243_r85 N h
  · exact commonTwo_of_mod243_r90 N h
  · exact commonTwo_of_mod243_r91 N h
  · exact commonTwo_of_mod243_r115 N h
  · exact commonTwo_of_mod243_r116 N h
  · exact commonTwo_of_mod243_r117 N h
  · exact commonTwo_of_mod243_r124 N h
  · exact commonTwo_of_mod243_r145 N h
  · exact commonTwo_of_mod243_r146 N h
  · exact commonTwo_of_mod243_r162 N h
  · exact commonTwo_of_mod243_r163 N h
  · exact commonTwo_of_mod243_r164 N h
  · exact commonTwo_of_mod243_r174 N h
  · exact commonTwo_of_mod243_r175 N h
  · exact commonTwo_of_mod243_r179 N h
  · exact commonTwo_of_mod243_r229 N h

/-- Convert the complete fifth-trit affine kill sector into an actual physical
Happy row. -/
theorem physical_happy_of_mod243_affine_fifth_kills
    (N : Nat)
    (hKill :
      N % 243 = 21 ∨ N % 243 = 38 ∨ N % 243 = 48 ∨ N % 243 = 61 ∨
      N % 243 = 70 ∨ N % 243 = 71 ∨ N % 243 = 85 ∨ N % 243 = 90 ∨
      N % 243 = 91 ∨ N % 243 = 115 ∨ N % 243 = 116 ∨ N % 243 = 117 ∨
      N % 243 = 124 ∨ N % 243 = 145 ∨ N % 243 = 146 ∨ N % 243 = 162 ∨
      N % 243 = 163 ∨ N % 243 = 164 ∨ N % 243 = 174 ∨ N % 243 = 175 ∨
      N % 243 = 179 ∨ N % 243 = 229) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod243_affine_fifth_kills N hKill)

/-- Retain the single-class physical constructor as a specialization. -/
theorem physical_happy_of_mod243_fortyeight
    (N : Nat) (hN : N % 243 = 48) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod243_fortyeight N hN)

/-- Task-3.3-shaped direct relocation constructor for the complete fifth-trit
sector. The incoming Happy row is not transported; a fresh physical row on
`4^(K+1)` is constructed from the affine kill certificate. -/
theorem four_power_happy_propagates_of_next_mod243_affine_fifth_kills
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext :
      (K+1) % 243 = 21 ∨ (K+1) % 243 = 38 ∨ (K+1) % 243 = 48 ∨
      (K+1) % 243 = 61 ∨ (K+1) % 243 = 70 ∨ (K+1) % 243 = 71 ∨
      (K+1) % 243 = 85 ∨ (K+1) % 243 = 90 ∨ (K+1) % 243 = 91 ∨
      (K+1) % 243 = 115 ∨ (K+1) % 243 = 116 ∨ (K+1) % 243 = 117 ∨
      (K+1) % 243 = 124 ∨ (K+1) % 243 = 145 ∨ (K+1) % 243 = 146 ∨
      (K+1) % 243 = 162 ∨ (K+1) % 243 = 163 ∨ (K+1) % 243 = 164 ∨
      (K+1) % 243 = 174 ∨ (K+1) % 243 = 175 ∨ (K+1) % 243 = 179 ∨
      (K+1) % 243 = 229) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod243_affine_fifth_kills (K+1) hNext

/-- Backward-compatible relocation specialization for residue 48. -/
theorem four_power_happy_propagates_of_next_mod243_fortyeight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 243 = 48) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod243_fortyeight (K+1) hNext

#check commonTwo_of_mod243_fortyeight
#check commonTwo_of_mod243_affine_fifth_kills
#check physical_happy_of_mod243_affine_fifth_kills
#check four_power_happy_propagates_of_next_mod243_affine_fifth_kills
#print axioms commonTwo_of_mod243_affine_fifth_kills
#print axioms physical_happy_of_mod243_affine_fifth_kills
#print axioms four_power_happy_propagates_of_next_mod243_affine_fifth_kills

end GSTFourPowerAffineFifthTrit
