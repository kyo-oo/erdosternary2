import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtySeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row67_reference :
    digit3 (4 ^ 55) 67 = 2 ∧ digit3 (4 ^ 56) 67 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod92709463147897837085761925410587_55
    (N : Nat) (hN : N % 92709463147897837085761925410587 = 55) : CommonTwo N := by
  have hPow : 3 ^ 67 = 92709463147897837085761925410587 := by norm_num
  have hExp : N % 3 ^ 67 = 55 % 3 ^ 67 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (67 + 1) = 4 ^ 55 % 3 ^ (67 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 67 N 55).2 hExp
  have hd0 : digit3 (4 ^ N) 67 = 2 := by
    calc
      digit3 (4 ^ N) 67 = digit3 (4 ^ 55) 67 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row67_reference.1
  have hExp1 : (N + 1) % 3 ^ 67 = 56 % 3 ^ 67 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (67 + 1) = 4 ^ 56 % 3 ^ (67 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 67 (N + 1) 56).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 67 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 67 = digit3 (4 ^ 56) 67 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row67_reference.2
  exact ⟨67, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod92709463147897837085761925410587_55
    (N : Nat) (hN : N % 92709463147897837085761925410587 = 55) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod92709463147897837085761925410587_55 N hN)

theorem four_power_happy_propagates_of_next_mod92709463147897837085761925410587_55
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 92709463147897837085761925410587 = 55) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod92709463147897837085761925410587_55 (K + 1) hNext

#check commonTwo_of_mod92709463147897837085761925410587_55
#check physical_happy_of_mod92709463147897837085761925410587_55
#check four_power_happy_propagates_of_next_mod92709463147897837085761925410587_55

end GSTFourPowerDirectSixtySeventhRow
