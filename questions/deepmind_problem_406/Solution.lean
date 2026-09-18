import GSTResidualOmegaRevival
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# DeepMind Formal Conjectures — Erdős Problem 406

Solution-side bridge from the binder-free residual Ω closure to DeepMind's
actual finiteness formulation.

No Mahler hypothesis, compression hypothesis, tail hypothesis, or custom
proposition is accepted by the exported theorem.
-/

namespace Erdos406

private theorem digit_two_forbids_zero_one_digits
    (n p : Nat) (hp : n / 3^p % 3 = 2) :
    ¬ Nat.digits 3 n ⊆ [0, 1] := by
  intro hsub
  have hget : (Nat.digits 3 n).getD p 0 = 2 := by
    rw [Nat.getD_digits n p (by decide : 2 ≤ 3)]
    exact hp
  by_cases hpl : p < (Nat.digits 3 n).length
  · have hmem : (Nat.digits 3 n)[p] ∈ Nat.digits 3 n :=
      List.getElem_mem hpl
    have h01 := hsub hmem
    have hget' : (Nat.digits 3 n)[p] = 2 := by
      rw [← List.getD_eq_getElem (l := Nat.digits 3 n) (d := 0) hpl]
      exact hget
    simp only [List.mem_cons, List.mem_singleton] at h01
    omega
  · have hge : (Nat.digits 3 n).length ≤ p := Nat.le_of_not_gt hpl
    have hz : (Nat.digits 3 n).getD p 0 = 0 :=
      List.getD_eq_default (l := Nat.digits 3 n) (d := 0) hge
    omega

theorem erdos_406 :
    {n : Nat | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  refine (Set.finite_Iic (2^8 : Nat)).subset ?_
  intro n hn
  rcases hn with ⟨hpow, hdigits⟩
  rcases hpow with ⟨k, rfl⟩
  have hklt : k < 9 := by
    by_contra hnot
    have hk9 : 9 ≤ k := by omega
    have hfalse : noTernaryTwo (2^k) = false :=
      GSTResidualOmegaRevival.full_erdos k hk9
    obtain ⟨p, hp⟩ := no_two_false_digit_witness (2^k) hfalse
    have hp' : 2^k / 3^p % 3 = 2 := by
      simpa [gstDigit] using hp
    exact digit_two_forbids_zero_one_digits (2^k) p hp' hdigits
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)

#print axioms erdos_406

end Erdos406
