import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredTwentySeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row227_reference :
    digit3 (4 ^ 228) 227 = 2 ∧ digit3 (4 ^ 229) 227 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228
    (N : Nat) (hN : N % 2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987 = 228) : CommonTwo N := by
  have hPow : 3 ^ 227 = 2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987 := by norm_num
  have hExp : N % 3 ^ 227 = 228 % 3 ^ 227 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (227 + 1) = 4 ^ 228 % 3 ^ (227 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 227 N 228).2 hExp
  have hd0 : digit3 (4 ^ N) 227 = 2 := by
    calc
      digit3 (4 ^ N) 227 = digit3 (4 ^ 228) 227 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row227_reference.1
  have hExp1 : (N + 1) % 3 ^ 227 = 229 % 3 ^ 227 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (227 + 1) = 4 ^ 229 % 3 ^ (227 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 227 (N + 1) 229).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 227 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 227 = digit3 (4 ^ 229) 227 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row227_reference.2
  exact ⟨227, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228
    (N : Nat) (hN : N % 2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987 = 228) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228 N hN)

theorem four_power_happy_propagates_of_next_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987 = 228) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228 (K + 1) hNext

#check commonTwo_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228
#check physical_happy_of_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228
#check four_power_happy_propagates_of_next_mod2025465365549235636389379590279612045176776005882811610332067323733925450296747107485272801773488928849912987_228

end GSTFourPowerDirectTwoHundredTwentySeventhRow
