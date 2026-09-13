import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredSeventyFifthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row175_reference :
    digit3 (4 ^ 176) 175 = 2 ∧ digit3 (4 ^ 177) 175 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176
    (N : Nat) (hN : N % 313487028995334947898311636710352105968826343219733319851858295246737190712070115307 = 176) : CommonTwo N := by
  have hPow : 3 ^ 175 = 313487028995334947898311636710352105968826343219733319851858295246737190712070115307 := by norm_num
  have hExp : N % 3 ^ 175 = 176 % 3 ^ 175 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (175 + 1) = 4 ^ 176 % 3 ^ (175 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 175 N 176).2 hExp
  have hd0 : digit3 (4 ^ N) 175 = 2 := by
    calc
      digit3 (4 ^ N) 175 = digit3 (4 ^ 176) 175 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row175_reference.1
  have hExp1 : (N + 1) % 3 ^ 175 = 177 % 3 ^ 175 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (175 + 1) = 4 ^ 177 % 3 ^ (175 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 175 (N + 1) 177).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 175 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 175 = digit3 (4 ^ 177) 175 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row175_reference.2
  exact ⟨175, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176
    (N : Nat) (hN : N % 313487028995334947898311636710352105968826343219733319851858295246737190712070115307 = 176) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176 N hN)

theorem four_power_happy_propagates_of_next_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 313487028995334947898311636710352105968826343219733319851858295246737190712070115307 = 176) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176 (K + 1) hNext

#check commonTwo_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176
#check physical_happy_of_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176
#check four_power_happy_propagates_of_next_mod313487028995334947898311636710352105968826343219733319851858295246737190712070115307_176

end GSTFourPowerDirectOneHundredSeventyFifthRow
