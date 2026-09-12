import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSeventySixthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row76_reference :
    digit3 (4 ^ 77) 76 = 2 ∧ digit3 (4 ^ 78) 76 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod1824800363140073127359051977856583921_77
    (N : Nat) (hN : N % 1824800363140073127359051977856583921 = 77) : CommonTwo N := by
  have hPow : 3 ^ 76 = 1824800363140073127359051977856583921 := by norm_num
  have hExp : N % 3 ^ 76 = 77 % 3 ^ 76 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (76 + 1) = 4 ^ 77 % 3 ^ (76 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 76 N 77).2 hExp
  have hd0 : digit3 (4 ^ N) 76 = 2 := by
    calc
      digit3 (4 ^ N) 76 = digit3 (4 ^ 77) 76 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row76_reference.1
  have hExp1 : (N + 1) % 3 ^ 76 = 78 % 3 ^ 76 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (76 + 1) = 4 ^ 78 % 3 ^ (76 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 76 (N + 1) 78).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 76 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 76 = digit3 (4 ^ 78) 76 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row76_reference.2
  exact ⟨76, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod1824800363140073127359051977856583921_77
    (N : Nat) (hN : N % 1824800363140073127359051977856583921 = 77) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod1824800363140073127359051977856583921_77 N hN)

theorem four_power_happy_propagates_of_next_mod1824800363140073127359051977856583921_77
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 1824800363140073127359051977856583921 = 77) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod1824800363140073127359051977856583921_77 (K + 1) hNext

#check commonTwo_of_mod1824800363140073127359051977856583921_77
#check physical_happy_of_mod1824800363140073127359051977856583921_77
#check four_power_happy_propagates_of_next_mod1824800363140073127359051977856583921_77

end GSTFourPowerDirectSeventySixthRow
