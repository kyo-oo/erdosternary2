import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredNinetyFourthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row194_reference :
    digit3 (4 ^ 195) 194 = 2 ∧ digit3 (4 ^ 196) 194 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195
    (N : Nat) (hN : N % 364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369 = 195) : CommonTwo N := by
  have hPow : 3 ^ 194 = 364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369 := by norm_num
  have hExp : N % 3 ^ 194 = 195 % 3 ^ 194 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (194 + 1) = 4 ^ 195 % 3 ^ (194 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 194 N 195).2 hExp
  have hd0 : digit3 (4 ^ N) 194 = 2 := by
    calc
      digit3 (4 ^ N) 194 = digit3 (4 ^ 195) 194 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row194_reference.1
  have hExp1 : (N + 1) % 3 ^ 194 = 196 % 3 ^ 194 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (194 + 1) = 4 ^ 196 % 3 ^ (194 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 194 (N + 1) 196).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 194 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 194 = digit3 (4 ^ 196) 194 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row194_reference.2
  exact ⟨194, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195
    (N : Nat) (hN : N % 364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369 = 195) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195 N hN)

theorem four_power_happy_propagates_of_next_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369 = 195) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195 (K + 1) hNext

#check commonTwo_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195
#check physical_happy_of_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195
#check four_power_happy_propagates_of_next_mod364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369_195

end GSTFourPowerDirectOneHundredNinetyFourthRow
