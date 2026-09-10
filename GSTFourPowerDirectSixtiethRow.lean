import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtiethRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row60_reference :
    digit3 (4 ^ 50) 60 = 2 ∧ digit3 (4 ^ 51) 60 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod42391158275216203514294433201_50
    (N : Nat) (hN : N % 42391158275216203514294433201 = 50) : CommonTwo N := by
  have hPow : 3 ^ 60 = 42391158275216203514294433201 := by norm_num
  have hExp : N % 3 ^ 60 = 50 % 3 ^ 60 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (60 + 1) = 4 ^ 50 % 3 ^ (60 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 60 N 50).2 hExp
  have hd0 : digit3 (4 ^ N) 60 = 2 := by
    calc
      digit3 (4 ^ N) 60 = digit3 (4 ^ 50) 60 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row60_reference.1
  have hExp1 : (N + 1) % 3 ^ 60 = 51 % 3 ^ 60 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (60 + 1) = 4 ^ 51 % 3 ^ (60 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 60 (N + 1) 51).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 60 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 60 = digit3 (4 ^ 51) 60 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row60_reference.2
  exact ⟨60, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod42391158275216203514294433201_50
    (N : Nat) (hN : N % 42391158275216203514294433201 = 50) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod42391158275216203514294433201_50 N hN)

theorem four_power_happy_propagates_of_next_mod42391158275216203514294433201_50
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 42391158275216203514294433201 = 50) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod42391158275216203514294433201_50 (K + 1) hNext

#check commonTwo_of_mod42391158275216203514294433201_50
#check physical_happy_of_mod42391158275216203514294433201_50
#check four_power_happy_propagates_of_next_mod42391158275216203514294433201_50

end GSTFourPowerDirectSixtiethRow
