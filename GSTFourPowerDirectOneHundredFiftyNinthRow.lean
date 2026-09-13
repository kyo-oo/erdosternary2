import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredFiftyNinthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row159_reference :
    digit3 (4 ^ 160) 159 = 2 ∧ digit3 (4 ^ 161) 159 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160
    (N : Nat) (hN : N % 7282483350946404208076885500996745047522350034970917293604274649554310785067 = 160) : CommonTwo N := by
  have hPow : 3 ^ 159 = 7282483350946404208076885500996745047522350034970917293604274649554310785067 := by norm_num
  have hExp : N % 3 ^ 159 = 160 % 3 ^ 159 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (159 + 1) = 4 ^ 160 % 3 ^ (159 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 159 N 160).2 hExp
  have hd0 : digit3 (4 ^ N) 159 = 2 := by
    calc
      digit3 (4 ^ N) 159 = digit3 (4 ^ 160) 159 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row159_reference.1
  have hExp1 : (N + 1) % 3 ^ 159 = 161 % 3 ^ 159 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (159 + 1) = 4 ^ 161 % 3 ^ (159 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 159 (N + 1) 161).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 159 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 159 = digit3 (4 ^ 161) 159 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row159_reference.2
  exact ⟨159, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160
    (N : Nat) (hN : N % 7282483350946404208076885500996745047522350034970917293604274649554310785067 = 160) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160 N hN)

theorem four_power_happy_propagates_of_next_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 7282483350946404208076885500996745047522350034970917293604274649554310785067 = 160) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160 (K + 1) hNext

#check commonTwo_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160
#check physical_happy_of_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160
#check four_power_happy_propagates_of_next_mod7282483350946404208076885500996745047522350034970917293604274649554310785067_160

end GSTFourPowerDirectOneHundredFiftyNinthRow
