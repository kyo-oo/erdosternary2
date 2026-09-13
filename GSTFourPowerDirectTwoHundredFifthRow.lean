import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredFifthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row205_reference :
    digit3 (4 ^ 206) 205 = 2 ∧ digit3 (4 ^ 207) 205 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206
    (N : Nat) (hN : N % 64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243 = 206) : CommonTwo N := by
  have hPow : 3 ^ 205 = 64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243 := by norm_num
  have hExp : N % 3 ^ 205 = 206 % 3 ^ 205 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (205 + 1) = 4 ^ 206 % 3 ^ (205 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 205 N 206).2 hExp
  have hd0 : digit3 (4 ^ N) 205 = 2 := by
    calc
      digit3 (4 ^ N) 205 = digit3 (4 ^ 206) 205 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row205_reference.1
  have hExp1 : (N + 1) % 3 ^ 205 = 207 % 3 ^ 205 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (205 + 1) = 4 ^ 207 % 3 ^ (205 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 205 (N + 1) 207).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 205 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 205 = digit3 (4 ^ 207) 205 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row205_reference.2
  exact ⟨205, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206
    (N : Nat) (hN : N % 64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243 = 206) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206 N hN)

theorem four_power_happy_propagates_of_next_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243 = 206) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206 (K + 1) hNext

#check commonTwo_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206
#check physical_happy_of_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206
#check four_power_happy_propagates_of_next_mod64544199296837568949323861254694449319503728994774862521821715702599475289016430467635481867692243_206

end GSTFourPowerDirectTwoHundredFifthRow
