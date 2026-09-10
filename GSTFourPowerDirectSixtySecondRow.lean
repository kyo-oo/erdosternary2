import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtySecondRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row62_reference :
    digit3 (4 ^ 52) 62 = 2 ∧ digit3 (4 ^ 53) 62 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod381520424476945831628649898809_52
    (N : Nat) (hN : N % 381520424476945831628649898809 = 52) : CommonTwo N := by
  have hPow : 3 ^ 62 = 381520424476945831628649898809 := by norm_num
  have hExp : N % 3 ^ 62 = 52 % 3 ^ 62 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (62 + 1) = 4 ^ 52 % 3 ^ (62 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 62 N 52).2 hExp
  have hd0 : digit3 (4 ^ N) 62 = 2 := by
    calc
      digit3 (4 ^ N) 62 = digit3 (4 ^ 52) 62 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row62_reference.1
  have hExp1 : (N + 1) % 3 ^ 62 = 53 % 3 ^ 62 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (62 + 1) = 4 ^ 53 % 3 ^ (62 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 62 (N + 1) 53).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 62 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 62 = digit3 (4 ^ 53) 62 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row62_reference.2
  exact ⟨62, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod381520424476945831628649898809_52
    (N : Nat) (hN : N % 381520424476945831628649898809 = 52) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod381520424476945831628649898809_52 N hN)

theorem four_power_happy_propagates_of_next_mod381520424476945831628649898809_52
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 381520424476945831628649898809 = 52) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod381520424476945831628649898809_52 (K + 1) hNext

#check commonTwo_of_mod381520424476945831628649898809_52
#check physical_happy_of_mod381520424476945831628649898809_52
#check four_power_happy_propagates_of_next_mod381520424476945831628649898809_52

end GSTFourPowerDirectSixtySecondRow
