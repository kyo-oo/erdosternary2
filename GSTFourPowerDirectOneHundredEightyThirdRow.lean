import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredEightyThirdRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row183_reference :
    digit3 (4 ^ 184) 183 = 2 ∧ digit3 (4 ^ 185) 183 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184
    (N : Nat) (hN : N % 2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227 = 184) : CommonTwo N := by
  have hPow : 3 ^ 183 = 2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227 := by norm_num
  have hExp : N % 3 ^ 183 = 184 % 3 ^ 183 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (183 + 1) = 4 ^ 184 % 3 ^ (183 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 183 N 184).2 hExp
  have hd0 : digit3 (4 ^ N) 183 = 2 := by
    calc
      digit3 (4 ^ N) 183 = digit3 (4 ^ 184) 183 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row183_reference.1
  have hExp1 : (N + 1) % 3 ^ 183 = 185 % 3 ^ 183 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (183 + 1) = 4 ^ 185 % 3 ^ (183 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 183 (N + 1) 185).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 183 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 183 = digit3 (4 ^ 185) 183 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row183_reference.2
  exact ⟨183, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184
    (N : Nat) (hN : N % 2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227 = 184) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184 N hN)

theorem four_power_happy_propagates_of_next_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227 = 184) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184 (K + 1) hNext

#check commonTwo_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184
#check physical_happy_of_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184
#check four_power_happy_propagates_of_next_mod2056788397238392593160822648456620167261469637864670311548042275113842708261892026529227_184

end GSTFourPowerDirectOneHundredEightyThirdRow
