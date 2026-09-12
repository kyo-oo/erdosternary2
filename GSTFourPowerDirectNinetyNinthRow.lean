import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectNinetyNinthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row99_reference :
    digit3 (4 ^ 100) 99 = 2 ∧ digit3 (4 ^ 101) 99 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod171792506910670443678820376588540424234035840667_100
    (N : Nat) (hN : N % 171792506910670443678820376588540424234035840667 = 100) : CommonTwo N := by
  have hPow : 3 ^ 99 = 171792506910670443678820376588540424234035840667 := by norm_num
  have hExp : N % 3 ^ 99 = 100 % 3 ^ 99 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (99 + 1) = 4 ^ 100 % 3 ^ (99 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 99 N 100).2 hExp
  have hd0 : digit3 (4 ^ N) 99 = 2 := by
    calc
      digit3 (4 ^ N) 99 = digit3 (4 ^ 100) 99 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row99_reference.1
  have hExp1 : (N + 1) % 3 ^ 99 = 101 % 3 ^ 99 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (99 + 1) = 4 ^ 101 % 3 ^ (99 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 99 (N + 1) 101).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 99 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 99 = digit3 (4 ^ 101) 99 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row99_reference.2
  exact ⟨99, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod171792506910670443678820376588540424234035840667_100
    (N : Nat) (hN : N % 171792506910670443678820376588540424234035840667 = 100) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod171792506910670443678820376588540424234035840667_100 N hN)

theorem four_power_happy_propagates_of_next_mod171792506910670443678820376588540424234035840667_100
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 171792506910670443678820376588540424234035840667 = 100) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod171792506910670443678820376588540424234035840667_100 (K + 1) hNext

#check commonTwo_of_mod171792506910670443678820376588540424234035840667_100
#check physical_happy_of_mod171792506910670443678820376588540424234035840667_100
#check four_power_happy_propagates_of_next_mod171792506910670443678820376588540424234035840667_100

end GSTFourPowerDirectNinetyNinthRow
