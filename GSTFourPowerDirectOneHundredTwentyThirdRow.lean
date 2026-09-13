import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredTwentyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row123_reference :
    digit3 (4 ^ 124) 123 = 2 ∧ digit3 (4 ^ 125) 123 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod48519278097689642681155855396759336072749841943521979872827_124
    (N : Nat) (hN : N % 48519278097689642681155855396759336072749841943521979872827 = 124) : CommonTwo N := by
  have hPow : 3 ^ 123 = 48519278097689642681155855396759336072749841943521979872827 := by norm_num
  have hExp : N % 3 ^ 123 = 124 % 3 ^ 123 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (123 + 1) = 4 ^ 124 % 3 ^ (123 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 123 N 124).2 hExp
  have hd0 : digit3 (4 ^ N) 123 = 2 := by
    calc
      digit3 (4 ^ N) 123 = digit3 (4 ^ 124) 123 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row123_reference.1
  have hExp1 : (N + 1) % 3 ^ 123 = 125 % 3 ^ 123 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (123 + 1) = 4 ^ 125 % 3 ^ (123 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 123 (N + 1) 125).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 123 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 123 = digit3 (4 ^ 125) 123 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row123_reference.2
  exact ⟨123, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod48519278097689642681155855396759336072749841943521979872827_124
    (N : Nat) (hN : N % 48519278097689642681155855396759336072749841943521979872827 = 124) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod48519278097689642681155855396759336072749841943521979872827_124 N hN)

theorem four_power_happy_propagates_of_next_mod48519278097689642681155855396759336072749841943521979872827_124
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 48519278097689642681155855396759336072749841943521979872827 = 124) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod48519278097689642681155855396759336072749841943521979872827_124 (K + 1) hNext

#check commonTwo_of_mod48519278097689642681155855396759336072749841943521979872827_124
#check physical_happy_of_mod48519278097689642681155855396759336072749841943521979872827_124
#check four_power_happy_propagates_of_next_mod48519278097689642681155855396759336072749841943521979872827_124

end GSTFourPowerDirectOneHundredTwentyThirdRow
