import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredSixthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row206_reference :
    digit3 (4 ^ 207) 206 = 2 ∧ digit3 (4 ^ 208) 206 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207
    (N : Nat) (hN : N % 193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729 = 207) : CommonTwo N := by
  have hPow : 3 ^ 206 = 193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729 := by norm_num
  have hExp : N % 3 ^ 206 = 207 % 3 ^ 206 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (206 + 1) = 4 ^ 207 % 3 ^ (206 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 206 N 207).2 hExp
  have hd0 : digit3 (4 ^ N) 206 = 2 := by
    calc
      digit3 (4 ^ N) 206 = digit3 (4 ^ 207) 206 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row206_reference.1
  have hExp1 : (N + 1) % 3 ^ 206 = 208 % 3 ^ 206 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (206 + 1) = 4 ^ 208 % 3 ^ (206 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 206 (N + 1) 208).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 206 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 206 = digit3 (4 ^ 208) 206 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row206_reference.2
  exact ⟨206, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207
    (N : Nat) (hN : N % 193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729 = 207) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207 N hN)

theorem four_power_happy_propagates_of_next_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729 = 207) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207 (K + 1) hNext

#check commonTwo_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207
#check physical_happy_of_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207
#check four_power_happy_propagates_of_next_mod193632597890512706847971583764083347958511186984324587565465147107798425867049291402906445603076729_207

end GSTFourPowerDirectTwoHundredSixthRow
