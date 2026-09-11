import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventyFifthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row75_reference :
    digit3 (4 ^ 60) 75 = 2 ∧ digit3 (4 ^ 61) 75 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod608266787713357709119683992618861307_60
    (N : Nat) (hN : N % 608266787713357709119683992618861307 = 60) : CommonTwo N := by
  have hPow : 3 ^ 75 = 608266787713357709119683992618861307 := by norm_num
  have hExp : N % 3 ^ 75 = 60 % 3 ^ 75 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (75 + 1) = 4 ^ 60 % 3 ^ (75 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 75 N 60).2 hExp
  have hd0 : digit3 (4 ^ N) 75 = 2 := by
    calc
      digit3 (4 ^ N) 75 = digit3 (4 ^ 60) 75 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row75_reference.1
  have hExp1 : (N + 1) % 3 ^ 75 = 61 % 3 ^ 75 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (75 + 1) = 4 ^ 61 % 3 ^ (75 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 75 (N + 1) 61).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 75 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 75 = digit3 (4 ^ 61) 75 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row75_reference.2
  exact ⟨75, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod608266787713357709119683992618861307_60
    (N : Nat) (hN : N % 608266787713357709119683992618861307 = 60) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod608266787713357709119683992618861307_60 N hN)

theorem four_power_happy_propagates_of_next_mod608266787713357709119683992618861307_60
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 608266787713357709119683992618861307 = 60) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod608266787713357709119683992618861307_60 (K + 1) hNext

#check commonTwo_of_mod608266787713357709119683992618861307_60
#check physical_happy_of_mod608266787713357709119683992618861307_60
#check four_power_happy_propagates_of_next_mod608266787713357709119683992618861307_60

end GSTFourPowerDirectSeventyFifthRow
