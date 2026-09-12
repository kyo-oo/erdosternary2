import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredTwelfthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row112_reference :
    digit3 (4 ^ 113) 112 = 2 ∧ digit3 (4 ^ 114) 112 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod273892744995340833777347939263771534786080723599733441_113
    (N : Nat) (hN : N % 273892744995340833777347939263771534786080723599733441 = 113) : CommonTwo N := by
  have hPow : 3 ^ 112 = 273892744995340833777347939263771534786080723599733441 := by norm_num
  have hExp : N % 3 ^ 112 = 113 % 3 ^ 112 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (112 + 1) = 4 ^ 113 % 3 ^ (112 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 112 N 113).2 hExp
  have hd0 : digit3 (4 ^ N) 112 = 2 := by
    calc
      digit3 (4 ^ N) 112 = digit3 (4 ^ 113) 112 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row112_reference.1
  have hExp1 : (N + 1) % 3 ^ 112 = 114 % 3 ^ 112 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (112 + 1) = 4 ^ 114 % 3 ^ (112 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 112 (N + 1) 114).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 112 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 112 = digit3 (4 ^ 114) 112 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row112_reference.2
  exact ⟨112, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod273892744995340833777347939263771534786080723599733441_113
    (N : Nat) (hN : N % 273892744995340833777347939263771534786080723599733441 = 113) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod273892744995340833777347939263771534786080723599733441_113 N hN)

theorem four_power_happy_propagates_of_next_mod273892744995340833777347939263771534786080723599733441_113
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 273892744995340833777347939263771534786080723599733441 = 113) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod273892744995340833777347939263771534786080723599733441_113 (K + 1) hNext

#check commonTwo_of_mod273892744995340833777347939263771534786080723599733441_113
#check physical_happy_of_mod273892744995340833777347939263771534786080723599733441_113
#check four_power_happy_propagates_of_next_mod273892744995340833777347939263771534786080723599733441_113

end GSTFourPowerDirectOneHundredTwelfthRow
