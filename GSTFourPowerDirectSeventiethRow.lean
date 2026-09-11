import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventiethRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row70_reference :
    digit3 (4 ^ 56) 70 = 2 ∧ digit3 (4 ^ 57) 70 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod2503155504993241601315571986085849_56
    (N : Nat) (hN : N % 2503155504993241601315571986085849 = 56) : CommonTwo N := by
  have hPow : 3 ^ 70 = 2503155504993241601315571986085849 := by norm_num
  have hExp : N % 3 ^ 70 = 56 % 3 ^ 70 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (70 + 1) = 4 ^ 56 % 3 ^ (70 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 70 N 56).2 hExp
  have hd0 : digit3 (4 ^ N) 70 = 2 := by
    calc
      digit3 (4 ^ N) 70 = digit3 (4 ^ 56) 70 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row70_reference.1
  have hExp1 : (N + 1) % 3 ^ 70 = 57 % 3 ^ 70 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (70 + 1) = 4 ^ 57 % 3 ^ (70 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 70 (N + 1) 57).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 70 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 70 = digit3 (4 ^ 57) 70 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row70_reference.2
  exact ⟨70, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod2503155504993241601315571986085849_56
    (N : Nat) (hN : N % 2503155504993241601315571986085849 = 56) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod2503155504993241601315571986085849_56 N hN)

theorem four_power_happy_propagates_of_next_mod2503155504993241601315571986085849_56
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 2503155504993241601315571986085849 = 56) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod2503155504993241601315571986085849_56 (K + 1) hNext

#check commonTwo_of_mod2503155504993241601315571986085849_56
#check physical_happy_of_mod2503155504993241601315571986085849_56
#check four_power_happy_propagates_of_next_mod2503155504993241601315571986085849_56

end GSTFourPowerDirectSeventiethRow
