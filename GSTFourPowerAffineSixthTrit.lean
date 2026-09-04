import GSTFourPowerAffineFifthTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

/-- Exact sixth-prefix transfer from the exponent to the affine orbit. -/
private theorem affineOrbit_mod729_eq_of_exponent
    {N r : Nat} (hr : r < 729) (hN : N % 729 = r) :
    affineOrbit N % 729 = affineOrbit r % 729 := by
  exact (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N r).2 (by
    simpa [Nat.mod_eq_of_lt hr] using hN)

/-- First fresh sixth-trit death pattern.  For affine prefix
`(1,1,2,0,2,2)` (least significant trit first), a hypothetical bad channel
follows `1 -> 1 -> 1 -> 3 -> 1 -> 3`, and the terminal trit `2` is impossible
in state `3`. -/
private theorem commonTwo_of_mod729_pattern_112022
    (N : Nat) (hAmod : affineOrbit N % 729 = 670) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 1 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_one_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_three_iff, hd5] at hbad5
  simpa using hbad5

/-- A second genuinely sixth-trit death pattern.  For affine prefix
`(0,1,2,1,2,2)`, a hypothetical bad channel follows
`1 -> 0 -> 1 -> 3 -> 2 -> 3`, and the terminal trit `2` is impossible in
state `3`. -/
private theorem commonTwo_of_mod729_pattern_012122
    (N : Nat) (hAmod : affineOrbit N % 729 = 696) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 3 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 2 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_three_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_two_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_three_iff, hd5] at hbad5
  simpa using hbad5

/-- Exponent residue `22 mod 729` is killed exactly by the first fresh
sixth-trit bad-channel obstruction. -/
theorem commonTwo_of_mod729_twentytwo
    (N : Nat) (hN : N % 729 = 22) : CommonTwo N := by
  have hA : affineOrbit N % 729 = 670 := by
    have h := affineOrbit_mod729_eq_of_exponent (N := N) (r := 22) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod729_pattern_112022 N hA

/-- Exponent residue `30 mod 729` is killed at the sixth affine trit. -/
theorem commonTwo_of_mod729_thirty
    (N : Nat) (hN : N % 729 = 30) : CommonTwo N := by
  have hA : affineOrbit N % 729 = 696 := by
    have h := affineOrbit_mod729_eq_of_exponent (N := N) (r := 30) (by norm_num) hN
    norm_num [affineOrbit] at h
    exact h
  exact commonTwo_of_mod729_pattern_012122 N hA

/-- Convert residue `22` into an actual physical Happy row. -/
theorem physical_happy_of_mod729_twentytwo
    (N : Nat) (hN : N % 729 = 22) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_twentytwo N hN)

/-- Convert residue `30` into an actual physical Happy row. -/
theorem physical_happy_of_mod729_thirty
    (N : Nat) (hN : N % 729 = 30) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_thirty N hN)

/-- Task-3.3-shaped direct relocation constructor for residue `22`.  The source
Happy row is not transported: the next sheet gets a newly constructed physical
Happy row. -/
theorem four_power_happy_propagates_of_next_mod729_twentytwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 22) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_twentytwo (K+1) hNext

/-- Task-3.3-shaped direct relocation constructor for residue `30`. -/
theorem four_power_happy_propagates_of_next_mod729_thirty
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 30) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_thirty (K+1) hNext

#check commonTwo_of_mod729_twentytwo
#check commonTwo_of_mod729_thirty
#check physical_happy_of_mod729_twentytwo
#check physical_happy_of_mod729_thirty
#check four_power_happy_propagates_of_next_mod729_twentytwo
#check four_power_happy_propagates_of_next_mod729_thirty
#print axioms commonTwo_of_mod729_twentytwo
#print axioms commonTwo_of_mod729_thirty
#print axioms physical_happy_of_mod729_twentytwo
#print axioms physical_happy_of_mod729_thirty
#print axioms four_power_happy_propagates_of_next_mod729_twentytwo
#print axioms four_power_happy_propagates_of_next_mod729_thirty

end GSTFourPowerAffineSixthTrit
