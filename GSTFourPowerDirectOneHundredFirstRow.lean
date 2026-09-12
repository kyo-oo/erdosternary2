import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredFirstRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row101_reference :
    digit3 (4 ^ 102) 101 = 2 ∧ digit3 (4 ^ 103) 101 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod1546132562196033993109383389296863818106322566003_102
    (N : Nat) (hN : N % 1546132562196033993109383389296863818106322566003 = 102) : CommonTwo N := by
  have hPow : 3 ^ 101 = 1546132562196033993109383389296863818106322566003 := by norm_num
  have hExp : N % 3 ^ 101 = 102 % 3 ^ 101 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (101 + 1) = 4 ^ 102 % 3 ^ (101 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 101 N 102).2 hExp
  have hd0 : digit3 (4 ^ N) 101 = 2 := by
    calc
      digit3 (4 ^ N) 101 = digit3 (4 ^ 102) 101 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row101_reference.1
  have hExp1 : (N + 1) % 3 ^ 101 = 103 % 3 ^ 101 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (101 + 1) = 4 ^ 103 % 3 ^ (101 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 101 (N + 1) 103).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 101 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 101 = digit3 (4 ^ 103) 101 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row101_reference.2
  exact ⟨101, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod1546132562196033993109383389296863818106322566003_102
    (N : Nat) (hN : N % 1546132562196033993109383389296863818106322566003 = 102) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod1546132562196033993109383389296863818106322566003_102 N hN)

theorem four_power_happy_propagates_of_next_mod1546132562196033993109383389296863818106322566003_102
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 1546132562196033993109383389296863818106322566003 = 102) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod1546132562196033993109383389296863818106322566003_102 (K + 1) hNext

#check commonTwo_of_mod1546132562196033993109383389296863818106322566003_102
#check physical_happy_of_mod1546132562196033993109383389296863818106322566003_102
#check four_power_happy_propagates_of_next_mod1546132562196033993109383389296863818106322566003_102

end GSTFourPowerDirectOneHundredFirstRow
