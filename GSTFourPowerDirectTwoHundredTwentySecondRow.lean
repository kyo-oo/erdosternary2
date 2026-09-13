import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredTwentySecondRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row222_reference :
    digit3 (4 ^ 223) 222 = 2 ∧ digit3 (4 ^ 224) 222 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223
    (N : Nat) (hN : N % 8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609 = 223) : CommonTwo N := by
  have hPow : 3 ^ 222 = 8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609 := by norm_num
  have hExp : N % 3 ^ 222 = 223 % 3 ^ 222 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (222 + 1) = 4 ^ 223 % 3 ^ (222 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 222 N 223).2 hExp
  have hd0 : digit3 (4 ^ N) 222 = 2 := by
    calc
      digit3 (4 ^ N) 222 = digit3 (4 ^ 223) 222 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row222_reference.1
  have hExp1 : (N + 1) % 3 ^ 222 = 224 % 3 ^ 222 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (222 + 1) = 4 ^ 224 % 3 ^ (222 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 222 (N + 1) 224).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 222 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 222 = digit3 (4 ^ 224) 222 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row222_reference.2
  exact ⟨222, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223
    (N : Nat) (hN : N % 8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609 = 223) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223 N hN)

theorem four_power_happy_propagates_of_next_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609 = 223) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223 (K + 1) hNext

#check commonTwo_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223
#check physical_happy_of_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223
#check four_power_happy_propagates_of_next_mod8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609_223

end GSTFourPowerDirectTwoHundredTwentySecondRow
