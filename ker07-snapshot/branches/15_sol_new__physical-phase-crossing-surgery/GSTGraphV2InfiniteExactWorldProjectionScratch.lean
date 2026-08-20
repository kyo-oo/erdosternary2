import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Exact integer-cleared K-world projection

The handwritten master uses the evaluation x=3/K and the coefficient K-1.
Instead of working in a localization of rationals, this file clears every K
denominator recursively.  The resulting object is a plain natural number and
its reduction modulo K-1 is exactly the original ternary integer fingerprint.

No approximation and no analytic convergence enters this statement.
-/

/-- Ordinary ternary prefix value, written recursively so it is an exact
finite observation of the Nat-indexed digit stream. -/
def gstTernaryPrefixValueS (R : Nat) : Nat → Nat
  | 0 => 0
  | L+1 => gstTernaryPrefixValueS R L + 3^L * gstDigitS R L

/-- Every recursive prefix is literally R modulo the corresponding ternary
scale. -/
theorem gst_ternary_prefix_value_exactS
    (R L : Nat) :
    gstTernaryPrefixValueS R L = R % 3^L := by
  induction L with
  | zero => simp [gstTernaryPrefixValueS]
  | succ L ih =>
      rw [gstTernaryPrefixValueS, ih]
      exact (gst_prefix_residue_succ_exactS R L).symm

/-- Integer-cleared evaluation of the finite digit polynomial at x=3/K.
At each new digit the old cleared value receives one factor K. -/
def gstClearedWorldEvalS (R K : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
      K * gstClearedWorldEvalS R K L +
        K * 3^L * gstDigitS R L

/-- The world cardinality itself is one modulo its coefficient K-1. -/
theorem gst_cardinality_mod_world_coefficientS
    (K : Nat) (hK : 3 ≤ K) :
    K % (K-1) = 1 := by
  have hshape : K = (K-1) + 1 := by omega
  rw [hshape, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- Integer-cleared x=3/K evaluation has exactly the same K-1 shadow as the
ordinary ternary prefix. -/
theorem gst_cleared_world_eval_prefix_shadowS
    (R K L : Nat) (hK : 3 ≤ K) :
    gstClearedWorldEvalS R K L % (K-1) =
      gstTernaryPrefixValueS R L % (K-1) := by
  have hkmod : K % (K-1) = 1 :=
    gst_cardinality_mod_world_coefficientS K hK
  induction L with
  | zero => simp [gstClearedWorldEvalS, gstTernaryPrefixValueS]
  | succ L ih =>
      rw [gstClearedWorldEvalS, gstTernaryPrefixValueS,
        Nat.add_mod, Nat.add_mod,
        Nat.mul_mod, Nat.mul_mod, Nat.mul_mod,
        Nat.mul_mod, Nat.mul_mod]
      rw [hkmod, ih]
      simp

/-- Same theorem directly in terms of the actual integer residue R mod 3^L. -/
theorem gst_cleared_world_eval_prefix_fingerprintS
    (R K L : Nat) (hK : 3 ≤ K) :
    gstClearedWorldEvalS R K L % (K-1) =
      (R % 3^L) % (K-1) := by
  rw [gst_cleared_world_eval_prefix_shadowS R K L hK,
    gst_ternary_prefix_value_exactS]

/-- At the explicit natural support ceiling the cleared world projection sees
R itself modulo K-1.  The ceiling is only used to finish the finite-support
reconstruction; K remains arbitrary. -/
theorem gst_cleared_world_eval_full_fingerprintS
    (R K : Nat) (hK : 3 ≤ K) :
    gstClearedWorldEvalS R K (R+1) % (K-1) = R % (K-1) := by
  rw [gst_cleared_world_eval_prefix_fingerprintS R K (R+1) hK]
  have hlt : R < 3^(R+1) := gst_self_lt_three_pow_succS R
  rw [Nat.mod_eq_of_lt hlt]

/-- Exact divisibility form: the integer-cleared evaluation and R differ by a
multiple of K-1, with no rational localization. -/
theorem gst_world_projection_exact_modEqS
    (R K : Nat) (hK : 3 ≤ K) :
    Nat.ModEq (K-1)
      (gstClearedWorldEvalS R K (R+1)) R := by
  exact gst_cleared_world_eval_full_fingerprintS R K hK

/-- The same result is available at any observation depth that already lies
beyond the natural ternary support of R. -/
theorem gst_cleared_world_eval_stable_fingerprintS
    (R K L : Nat) (hK : 3 ≤ K)
    (hL : R + 1 ≤ L) :
    gstClearedWorldEvalS R K L % (K-1) = R % (K-1) := by
  rw [gst_cleared_world_eval_prefix_fingerprintS R K L hK]
  have hbase : R < 3^(R+1) := gst_self_lt_three_pow_succS R
  have hpow : 3^(R+1) ≤ 3^L :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hL
  have hlt : R < 3^L := lt_of_lt_of_le hbase hpow
  rw [Nat.mod_eq_of_lt hlt]

/-- The world coefficient grows with K, but the exact shadow law does not
change.  This packages the full all-cardinality family used later by K=6^k. -/
def GSTExactWorldProjectionFamilyS (R : Nat) : Prop :=
  ∀ K, 3 ≤ K →
    Nat.ModEq (K-1)
      (gstClearedWorldEvalS R K (R+1)) R

theorem gst_exact_world_projection_familyS
    (R : Nat) : GSTExactWorldProjectionFamilyS R := by
  intro K hK
  exact gst_world_projection_exact_modEqS R K hK

end GSTInfiniteV2
