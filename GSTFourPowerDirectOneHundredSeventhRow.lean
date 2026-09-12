import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredSeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row107_reference :
    digit3 (4 ^ 108) 107 = 2 ∧ digit3 (4 ^ 109) 107 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod1127130637840908780976740490797413723399509150616187_108
    (N : Nat) (hN : N % 1127130637840908780976740490797413723399509150616187 = 108) : CommonTwo N := by
  have hPow : 3 ^ 107 = 1127130637840908780976740490797413723399509150616187 := by norm_num
  have hExp : N % 3 ^ 107 = 108 % 3 ^ 107 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (107 + 1) = 4 ^ 108 % 3 ^ (107 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 107 N 108).2 hExp
  have hd0 : digit3 (4 ^ N) 107 = 2 := by
    calc
      digit3 (4 ^ N) 107 = digit3 (4 ^ 108) 107 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row107_reference.1
  have hExp1 : (N + 1) % 3 ^ 107 = 109 % 3 ^ 107 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (107 + 1) = 4 ^ 109 % 3 ^ (107 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 107 (N + 1) 109).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 107 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 107 = digit3 (4 ^ 109) 107 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row107_reference.2
  exact ⟨107, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod1127130637840908780976740490797413723399509150616187_108
    (N : Nat) (hN : N % 1127130637840908780976740490797413723399509150616187 = 108) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod1127130637840908780976740490797413723399509150616187_108 N hN)

theorem four_power_happy_propagates_of_next_mod1127130637840908780976740490797413723399509150616187_108
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 1127130637840908780976740490797413723399509150616187 = 108) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod1127130637840908780976740490797413723399509150616187_108 (K + 1) hNext

#check commonTwo_of_mod1127130637840908780976740490797413723399509150616187_108
#check physical_happy_of_mod1127130637840908780976740490797413723399509150616187_108
#check four_power_happy_propagates_of_next_mod1127130637840908780976740490797413723399509150616187_108

end GSTFourPowerDirectOneHundredSeventhRow
