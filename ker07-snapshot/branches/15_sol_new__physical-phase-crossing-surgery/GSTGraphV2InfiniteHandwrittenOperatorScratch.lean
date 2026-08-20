import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite handwritten 6^k / 7/(x-6) / U / Omega operator

On the physical six-state spectrum m<6, the magnitude of Boss's scalar kernel
is represented exactly as 7/(6-m).  The global no-BIG1 branch has m=5 at every
microscopic depth, so the kernel is exactly seven at every depth.

Consequently the 6^k-weighted U contribution cannot remain below any fixed
finite Omega/Navigation budget at all depths.
-/

def gstInfiniteKernelDenomS (m : Nat) : Nat := 6 - m

def gstInfiniteKernelMagnitudeS (m : Nat) : Nat :=
  7 / gstInfiniteKernelDenomS m

theorem gst_infinite_kernel_mass_fiveS :
    gstInfiniteKernelDenomS 5 = 1 ∧
      gstInfiniteKernelMagnitudeS 5 = 7 := by
  decide

theorem gst_handwritten_u_charge_at_least_fiveS
    (C : Nat) : 5 ≤ gstHandwrittenUChargeS C := by
  unfold gstHandwrittenUChargeS
  by_cases h0 : C = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    by_cases h3 : C = 3
    · rw [if_pos h3]
      decide
    · rw [if_neg h3]
      decide

def gstHandwrittenInfiniteTermS
    (a d C : Nat → Nat) (k : Nat) : Nat :=
  6^k *
    gstInfiniteKernelMagnitudeS (gstBinaryBridgeMassS (a k) (d k)) *
    gstHandwrittenUChargeS (C k)

def gstHandwrittenInfinitePrefixS
    (a d C : Nat → Nat) (K : Nat) : Nat :=
  Finset.sum (Finset.range K) (gstHandwrittenInfiniteTermS a d C)

theorem gst_noBig1_infinite_term_exactS
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (k : Nat) :
    gstHandwrittenInfiniteTermS a d C k =
      6^k * 7 * gstHandwrittenUChargeS (C k) := by
  unfold gstHandwrittenInfiniteTermS
  have hm := (gst_big1_clear_infinite_edges_are_surviveS
    a d hpath h0 k).2.2.2.1
  rw [hm, gst_infinite_kernel_mass_fiveS.2]

theorem gst_noBig1_infinite_term_ge_world_weightS
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (k : Nat) :
    6^k ≤ gstHandwrittenInfiniteTermS a d C k := by
  rw [gst_noBig1_infinite_term_exactS a d C hpath h0 k]
  have hU : 5 ≤ gstHandwrittenUChargeS (C k) :=
    gst_handwritten_u_charge_at_least_fiveS (C k)
  have hfactor : 1 ≤ 7 * gstHandwrittenUChargeS (C k) := by omega
  have hmul := Nat.mul_le_mul_left (6^k) hfactor
  simpa [Nat.mul_assoc] using hmul

theorem gst_handwritten_prefix_ge_termS
    (a d C : Nat → Nat) (k : Nat) :
    gstHandwrittenInfiniteTermS a d C k ≤
      gstHandwrittenInfinitePrefixS a d C (k+1) := by
  unfold gstHandwrittenInfinitePrefixS
  rw [Finset.sum_range_succ]
  omega

theorem gst_budget_lt_six_pow_succS :
    ∀ B : Nat, B < 6^(B+1)
  | 0 => by decide
  | B+1 => by
      have ih : B < 6^(B+1) := gst_budget_lt_six_pow_succS B
      have hp : 0 < 6^(B+1) := Nat.pow_pos (by decide)
      calc
        B + 1 < 6^(B+1) + 1 := by omega
        _ ≤ 6^(B+1) * 6 := by omega
        _ = 6^((B+1)+1) := (Nat.pow_succ 6 (B+1)).symm

theorem gst_noBig1_handwritten_operator_exceeds_every_budgetS
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (B : Nat) :
    ∃ K, B < gstHandwrittenInfinitePrefixS a d C K := by
  let k := B+1
  refine ⟨k+1, ?_⟩
  have hB : B < 6^k := by
    simpa [k] using gst_budget_lt_six_pow_succS B
  have hweight : 6^k ≤ gstHandwrittenInfiniteTermS a d C k :=
    gst_noBig1_infinite_term_ge_world_weightS a d C hpath h0 k
  have hprefix : gstHandwrittenInfiniteTermS a d C k ≤
      gstHandwrittenInfinitePrefixS a d C (k+1) :=
    gst_handwritten_prefix_ge_termS a d C k
  exact lt_of_lt_of_le hB (le_trans hweight hprefix)

def GSTFiniteOmegaBudgetControlsS
    (a d C : Nat → Nat) (B : Nat) : Prop :=
  ∀ K, gstHandwrittenInfinitePrefixS a d C K ≤ B

theorem gst_noBig1_not_finite_omega_budgetS
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (B : Nat) :
    ¬ GSTFiniteOmegaBudgetControlsS a d C B := by
  intro hbound
  obtain ⟨K, hK⟩ :=
    gst_noBig1_handwritten_operator_exceeds_every_budgetS
      a d C hpath h0 B
  exact (not_lt_of_ge (hbound K)) hK

theorem gst_noBig1_not_navigation_omega_budgetS
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (t N : Nat) :
    ¬ GSTFiniteOmegaBudgetControlsS
      a d C (gstOmegaPressureEnergyS t N) := by
  exact gst_noBig1_not_finite_omega_budgetS
    a d C hpath h0 (gstOmegaPressureEnergyS t N)

theorem gst_handwritten_master_budget_eliminates_noBig1S
    (a d C : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (t N : Nat)
    (hmaster : GSTFiniteOmegaBudgetControlsS
      a d C (gstOmegaPressureEnergyS t N)) : False := by
  exact (gst_noBig1_not_navigation_omega_budgetS
    a d C hpath h0 t N) hmaster

end GSTInfiniteV2
