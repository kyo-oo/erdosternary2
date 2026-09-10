import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtyFifthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row65_reference :
    digit3 (4 ^ 60) 65 = 2 ∧ digit3 (4 ^ 61) 65 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod10301051460877537453973547267843_60
    (N : Nat) (hN : N % 10301051460877537453973547267843 = 60) : CommonTwo N := by
  have hPow : 3 ^ 65 = 10301051460877537453973547267843 := by norm_num
  have hExp : N % 3 ^ 65 = 60 % 3 ^ 65 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (65 + 1) = 4 ^ 60 % 3 ^ (65 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 65 N 60).2 hExp
  have hd0 : digit3 (4 ^ N) 65 = 2 := by
    calc
      digit3 (4 ^ N) 65 = digit3 (4 ^ 60) 65 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row65_reference.1
  have hExp1 : (N + 1) % 3 ^ 65 = 61 % 3 ^ 65 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (65 + 1) = 4 ^ 61 % 3 ^ (65 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 65 (N + 1) 61).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 65 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 65 = digit3 (4 ^ 61) 65 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row65_reference.2
  exact ⟨65, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod10301051460877537453973547267843_60
    (N : Nat) (hN : N % 10301051460877537453973547267843 = 60) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod10301051460877537453973547267843_60 N hN)

theorem four_power_happy_propagates_of_next_mod10301051460877537453973547267843_60
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 10301051460877537453973547267843 = 60) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod10301051460877537453973547267843_60 (K + 1) hNext

#check commonTwo_of_mod10301051460877537453973547267843_60
#check physical_happy_of_mod10301051460877537453973547267843_60
#check four_power_happy_propagates_of_next_mod10301051460877537453973547267843_60

end GSTFourPowerDirectSixtyFifthRow
