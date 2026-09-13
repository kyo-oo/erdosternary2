import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredNinetyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row193_reference :
    digit3 (4 ^ 194) 193 = 2 ∧ digit3 (4 ^ 195) 193 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194
    (N : Nat) (hN : N % 121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123 = 194) : CommonTwo N := by
  have hPow : 3 ^ 193 = 121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123 := by norm_num
  have hExp : N % 3 ^ 193 = 194 % 3 ^ 193 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (193 + 1) = 4 ^ 194 % 3 ^ (193 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 193 N 194).2 hExp
  have hd0 : digit3 (4 ^ N) 193 = 2 := by
    calc
      digit3 (4 ^ N) 193 = digit3 (4 ^ 194) 193 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row193_reference.1
  have hExp1 : (N + 1) % 3 ^ 193 = 195 % 3 ^ 193 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (193 + 1) = 4 ^ 195 % 3 ^ (193 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 193 (N + 1) 195).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 193 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 193 = digit3 (4 ^ 195) 193 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row193_reference.2
  exact ⟨193, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194
    (N : Nat) (hN : N % 121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123 = 194) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194 N hN)

theorem four_power_happy_propagates_of_next_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123 = 194) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194 (K + 1) hNext

#check commonTwo_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194
#check physical_happy_of_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194
#check four_power_happy_propagates_of_next_mod121451298068529844233553416568714964256622520646270917226600348303197298080156462274524325123_194

end GSTFourPowerDirectOneHundredNinetyThirdRow
