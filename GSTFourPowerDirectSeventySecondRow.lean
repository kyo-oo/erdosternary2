import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventySecondRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row72_reference :
    digit3 (4 ^ 59) 72 = 2 ∧ digit3 (4 ^ 60) 72 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod22528399544939174411840147874772641_59
    (N : Nat) (hN : N % 22528399544939174411840147874772641 = 59) : CommonTwo N := by
  have hPow : 3 ^ 72 = 22528399544939174411840147874772641 := by norm_num
  have hExp : N % 3 ^ 72 = 59 % 3 ^ 72 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (72 + 1) = 4 ^ 59 % 3 ^ (72 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 72 N 59).2 hExp
  have hd0 : digit3 (4 ^ N) 72 = 2 := by
    calc
      digit3 (4 ^ N) 72 = digit3 (4 ^ 59) 72 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row72_reference.1
  have hExp1 : (N + 1) % 3 ^ 72 = 60 % 3 ^ 72 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (72 + 1) = 4 ^ 60 % 3 ^ (72 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 72 (N + 1) 60).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 72 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 72 = digit3 (4 ^ 60) 72 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row72_reference.2
  exact ⟨72, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod22528399544939174411840147874772641_59
    (N : Nat) (hN : N % 22528399544939174411840147874772641 = 59) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod22528399544939174411840147874772641_59 N hN)

theorem four_power_happy_propagates_of_next_mod22528399544939174411840147874772641_59
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 22528399544939174411840147874772641 = 59) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod22528399544939174411840147874772641_59 (K + 1) hNext

#check commonTwo_of_mod22528399544939174411840147874772641_59
#check physical_happy_of_mod22528399544939174411840147874772641_59
#check four_power_happy_propagates_of_next_mod22528399544939174411840147874772641_59

end GSTFourPowerDirectSeventySecondRow
