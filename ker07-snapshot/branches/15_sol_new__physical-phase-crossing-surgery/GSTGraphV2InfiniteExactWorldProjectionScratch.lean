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

def gstTernaryPrefixValueS (R : Nat) : Nat → Nat
  | 0 => 0
  | L+1 => gstTernaryPrefixValueS R L + 3^L * gstDigitS R L

theorem gst_ternary_prefix_value_exactS
    (R L : Nat) :
    gstTernaryPrefixValueS R L = R % 3^L := by
  induction L with
  | zero =>
      exact (Nat.mod_one R).symm
  | succ L ih =>
      rw [gstTernaryPrefixValueS, ih]
      exact (gst_prefix_residue_succ_exactS R L).symm

def gstClearedWorldEvalS (R K : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
      K * gstClearedWorldEvalS R K L +
        K * 3^L * gstDigitS R L

theorem gst_cardinality_mod_world_coefficientS
    (K : Nat) (hK : 3 ≤ K) :
    K % (K-1) = 1 := by
  have hshape : K = (K-1) + 1 := by omega
  have hone_lt : 1 < K - 1 := by omega
  calc
    K % (K-1) = ((K-1) + 1) % (K-1) :=
      congrArg (fun x : Nat => x % (K-1)) hshape
    _ = 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt hone_lt]

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
        Nat.add_mod, Nat.add_mod]
      have hold :
          (K * gstClearedWorldEvalS R K L) % (K-1) =
            gstClearedWorldEvalS R K L % (K-1) := by
        rw [Nat.mul_mod, hkmod]
        simp
      have hterm :
          (K * 3^L * gstDigitS R L) % (K-1) =
            (3^L * gstDigitS R L) % (K-1) := by
        rw [show K * 3^L * gstDigitS R L =
              K * (3^L * gstDigitS R L) by ring,
            Nat.mul_mod, hkmod]
        simp
      rw [hold, hterm, ih]
      simp only [Nat.mod_mod]
      rw [← Nat.add_mod]

theorem gst_cleared_world_eval_prefix_fingerprintS
    (R K L : Nat) (hK : 3 ≤ K) :
    gstClearedWorldEvalS R K L % (K-1) =
      (R % 3^L) % (K-1) := by
  rw [gst_cleared_world_eval_prefix_shadowS R K L hK,
    gst_ternary_prefix_value_exactS]

theorem gst_cleared_world_eval_full_fingerprintS
    (R K : Nat) (hK : 3 ≤ K) :
    gstClearedWorldEvalS R K (R+1) % (K-1) = R % (K-1) := by
  rw [gst_cleared_world_eval_prefix_fingerprintS R K (R+1) hK]
  have hlt : R < 3^(R+1) := gst_self_lt_three_pow_succS R
  rw [Nat.mod_eq_of_lt hlt]

theorem gst_world_projection_exact_modEqS
    (R K : Nat) (hK : 3 ≤ K) :
    Nat.ModEq (K-1)
      (gstClearedWorldEvalS R K (R+1)) R := by
  exact gst_cleared_world_eval_full_fingerprintS R K hK

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

def GSTExactWorldProjectionFamilyS (R : Nat) : Prop :=
  ∀ K, 3 ≤ K →
    Nat.ModEq (K-1)
      (gstClearedWorldEvalS R K (R+1)) R

theorem gst_exact_world_projection_familyS
    (R : Nat) : GSTExactWorldProjectionFamilyS R := by
  intro K hK
  exact gst_world_projection_exact_modEqS R K hK

end GSTInfiniteV2
