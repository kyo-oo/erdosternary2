import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row63_reference :
    digit3 (4 ^ 69) 63 = 2 ∧ digit3 (4 ^ 70) 63 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod1144561273430837494885949696427_69
    (N : Nat) (hN : N % 1144561273430837494885949696427 = 69) : CommonTwo N := by
  have hPow : 3 ^ 63 = 1144561273430837494885949696427 := by norm_num
  have hExp : N % 3 ^ 63 = 69 % 3 ^ 63 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (63 + 1) = 4 ^ 69 % 3 ^ (63 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 63 N 69).2 hExp
  have hd0 : digit3 (4 ^ N) 63 = 2 := by
    calc
      digit3 (4 ^ N) 63 = digit3 (4 ^ 69) 63 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row63_reference.1
  have hExp1 : (N + 1) % 3 ^ 63 = 70 % 3 ^ 63 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (63 + 1) = 4 ^ 70 % 3 ^ (63 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 63 (N + 1) 70).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 63 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 63 = digit3 (4 ^ 70) 63 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row63_reference.2
  exact ⟨63, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod1144561273430837494885949696427_69
    (N : Nat) (hN : N % 1144561273430837494885949696427 = 69) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod1144561273430837494885949696427_69 N hN)

theorem four_power_happy_propagates_of_next_mod1144561273430837494885949696427_69
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 1144561273430837494885949696427 = 69) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod1144561273430837494885949696427_69 (K + 1) hNext

#check commonTwo_of_mod1144561273430837494885949696427_69
#check physical_happy_of_mod1144561273430837494885949696427_69
#check four_power_happy_propagates_of_next_mod1144561273430837494885949696427_69

end GSTFourPowerDirectSixtyThirdRow
