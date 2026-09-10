import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectFiftyFifthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row55_reference :
    digit3 (4 ^ 85117) 55 = 2 ∧ digit3 (4 ^ 85118) 55 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod174449211009120179071170507_85117
    (N : Nat) (hN : N % 174449211009120179071170507 = 85117) : CommonTwo N := by
  have hPow : 3 ^ 55 = 174449211009120179071170507 := by norm_num
  have hExp : N % 3 ^ 55 = 85117 % 3 ^ 55 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (55 + 1) = 4 ^ 85117 % 3 ^ (55 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 55 N 85117).2 hExp
  have hd0 : digit3 (4 ^ N) 55 = 2 := by
    calc
      digit3 (4 ^ N) 55 = digit3 (4 ^ 85117) 55 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row55_reference.1
  have hExp1 : (N + 1) % 3 ^ 55 = 85118 % 3 ^ 55 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (55 + 1) = 4 ^ 85118 % 3 ^ (55 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 55 (N + 1) 85118).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 55 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 55 = digit3 (4 ^ 85118) 55 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row55_reference.2
  exact ⟨55, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod174449211009120179071170507_85117
    (N : Nat) (hN : N % 174449211009120179071170507 = 85117) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod174449211009120179071170507_85117 N hN)

theorem four_power_happy_propagates_of_next_mod174449211009120179071170507_85117
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 174449211009120179071170507 = 85117) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod174449211009120179071170507_85117 (K + 1) hNext

#check commonTwo_of_mod174449211009120179071170507_85117
#check physical_happy_of_mod174449211009120179071170507_85117
#check four_power_happy_propagates_of_next_mod174449211009120179071170507_85117

end GSTFourPowerDirectFiftyFifthRow
