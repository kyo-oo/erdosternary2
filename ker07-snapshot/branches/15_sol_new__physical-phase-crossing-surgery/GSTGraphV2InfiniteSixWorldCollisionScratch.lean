import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite six-world collision blade

The 2-world/3-world bridge mass is a base-six state.  This module proves the
exact contradiction obtained when a global no-BIG1 infinite path is identified
with the base-six digit stream of one fixed ordinary natural.
-/

def gstBaseSixDigitS (X p : Nat) : Nat := X / 6^p % 6

/-- Natural base-six streams are eventually zero. -/
theorem gst_self_lt_six_pow_succS : ∀ X : Nat, X < 6^(X+1)
  | 0 => by decide
  | X+1 => by
      have ih : X < 6^(X+1) := gst_self_lt_six_pow_succS X
      have hp : 0 < 6^(X+1) := Nat.pow_pos (by decide)
      calc
        X + 1 < 6^(X+1) + 1 := by omega
        _ ≤ 6^(X+1) * 6 := by omega
        _ = 6^((X+1)+1) := (Nat.pow_succ 6 (X+1)).symm

theorem gst_base_six_digit_zero_above_supportS
    (X p : Nat) (hp : X + 1 ≤ p) :
    gstBaseSixDigitS X p = 0 := by
  have hbase : X < 6^(X+1) := gst_self_lt_six_pow_succS X
  have hpow : 6^(X+1) ≤ 6^p :=
    Nat.pow_le_pow_of_le (by decide : 1 < 6) hp
  have hlt : X < 6^p := lt_of_lt_of_le hbase hpow
  unfold gstBaseSixDigitS
  rw [Nat.div_eq_of_lt hlt]

/-- No ordinary natural has the all-five base-six stream at every depth. -/
theorem gst_no_natural_all_five_base_sixS
    (X : Nat) : ¬ (∀ p, gstBaseSixDigitS X p = 5) := by
  intro hall
  have h5 := hall (X+1)
  have h0 := gst_base_six_digit_zero_above_supportS X (X+1) (by omega)
  omega

/-- A global no-BIG1 path has microscopic mass five at every depth. -/
theorem gst_big1_clear_infinite_mass_five_allS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ p, gstBinaryBridgeMassS (a p) (d p) = 5 := by
  intro p
  exact (gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 p).2.2.2.1

/-- Direct six-world collision.  If the microscopic masses of the global
no-BIG1 path are the base-six digits of one fixed natural X, contradiction. -/
theorem gst_big1_clear_cannot_realize_fixed_six_worldS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (X : Nat)
    (hreal : ∀ p,
      gstBinaryBridgeMassS (a p) (d p) = gstBaseSixDigitS X p) : False := by
  have hallMass := gst_big1_clear_infinite_mass_five_allS a d hpath h0
  apply gst_no_natural_all_five_base_sixS X
  intro p
  rw [← hreal p]
  exact hallMass p

/-- Specialization to the fixed binary pure-power diagonal integer 2^(S+1).
This is the exact target consumed by the diagonal 2/3/6-world adapter. -/
theorem gst_big1_clear_cannot_realize_power_diagonalS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (S : Nat)
    (hdiag : ∀ p,
      gstBinaryBridgeMassS (a p) (d p) =
        gstBaseSixDigitS (2^(S+1)) p) : False := by
  exact gst_big1_clear_cannot_realize_fixed_six_worldS
    a d hpath h0 (2^(S+1)) hdiag

/-- Recursive base-six prefix value of a fixed natural. -/
def gstBaseSixPrefixValueS (X : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => gstBaseSixPrefixValueS X K + 6^K * gstBaseSixDigitS X K

/-- Exact prefix reconstruction. -/
theorem gst_base_six_prefix_value_exactS
    (X K : Nat) : gstBaseSixPrefixValueS X K = X % 6^K := by
  induction K with
  | zero => simp [gstBaseSixPrefixValueS]
  | succ K ih =>
      rw [gstBaseSixPrefixValueS, ih]
      unfold gstBaseSixDigitS
      rw [Nat.pow_succ, Nat.mod_mul]

/-- If the first K six-world digits are all five, the finite observation is the
maximal base-six word 55...55 = 6^K-1. -/
theorem gst_base_six_all_five_prefix_maximalS
    (X K : Nat)
    (hall : ∀ p, p < K → gstBaseSixDigitS X p = 5) :
    X % 6^K = 6^K - 1 := by
  rw [← gst_base_six_prefix_value_exactS X K]
  induction K with
  | zero => simp [gstBaseSixPrefixValueS]
  | succ K ih =>
      rw [gstBaseSixPrefixValueS, hall K (by omega),
        ih (fun p hp => hall p (by omega)), Nat.pow_succ]
      have hp : 0 < 6^K := Nat.pow_pos (by decide)
      omega

/-- All-scale prefix form of the same collision. -/
theorem gst_big1_clear_fixed_six_world_all_prefixesS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (X : Nat)
    (hreal : ∀ p,
      gstBinaryBridgeMassS (a p) (d p) = gstBaseSixDigitS X p) :
    ∀ K, X % 6^K = 6^K - 1 := by
  intro K
  apply gst_base_six_all_five_prefix_maximalS
  intro p hp
  rw [← hreal p]
  exact gst_big1_clear_infinite_mass_five_allS a d hpath h0 p

end GSTInfiniteV2
