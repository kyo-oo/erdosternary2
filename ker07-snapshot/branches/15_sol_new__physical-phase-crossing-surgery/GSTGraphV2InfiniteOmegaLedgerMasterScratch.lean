import GSTGraphV2InfiniteElevenEquationMasterScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Exact infinite Omega Past/Future ledger fused with the eleven-equation master

The visible Omega transfer is not required to remain nonzero forever.  Instead
we keep the consumed Past and the unconsumed Future simultaneously.  Their sum
is the same finite information packet at every natural observation depth.
This is the exact additive counterpart of the multiplicative Pi/U invariant.
-/

/-- Information already transferred into Omega-Past below depth `K`. -/
def gstOmegaPastS (t N K : Nat) : Nat :=
  Finset.sum (Finset.range K) (fun i => gstOmegaNaturalTransferS t N i)

/-- Information still carried by Omega-Future above depth `K`, expressed in
exactly the same original scale as `gstOmegaPastS`. -/
def gstOmegaFutureS (t N K : Nat) : Nat :=
  3^(t+1+K) * (N / 3^K)

/-- Closed form for Past. -/
theorem gst_omega_past_closedS (t N K : Nat) :
    gstOmegaPastS t N K = 3^(t+1) * (N % 3^K) := by
  exact gst_omega_natural_transfer_prefixS t N K

/-- Exact all-depth Past/Future conservation.  No information is annihilated
when the visible Future eventually becomes zero. -/
theorem gst_omega_past_future_conservationS (t N K : Nat) :
    gstOmegaPastS t N K + gstOmegaFutureS t N K =
      3^(t+1) * N := by
  rw [gst_omega_past_closedS]
  unfold gstOmegaFutureS
  have hpow : 3^(t+1+K) = 3^(t+1) * 3^K := by
    rw [Nat.pow_add]
  rw [hpow]
  have hsplit : N = N % 3^K + 3^K * (N / 3^K) := by
    have h := Nat.mod_add_div N (3^K)
    omega
  calc
    3^(t+1) * (N % 3^K) +
        (3^(t+1) * 3^K) * (N / 3^K) =
      3^(t+1) * (N % 3^K + 3^K * (N / 3^K)) := by ring
    _ = 3^(t+1) * N := by rw [← hsplit]

/-- One Omega packet moves from Future to Past at each depth. -/
theorem gst_omega_past_stepS (t N K : Nat) :
    gstOmegaPastS t N (K+1) =
      gstOmegaPastS t N K + gstOmegaNaturalTransferS t N K := by
  unfold gstOmegaPastS
  rw [Finset.sum_range_succ]

/-- Future obeys the opposite transfer equation. -/
theorem gst_omega_future_stepS (t N K : Nat) :
    gstOmegaFutureS t N K =
      gstOmegaNaturalTransferS t N K + gstOmegaFutureS t N (K+1) := by
  have hK : 0 < 3^K := Nat.pow_pos (by decide)
  have hK1 : 0 < 3^(K+1) := Nat.pow_pos (by decide)
  have hdecompK :
      N / 3^K = gstDigitS N K + 3 * (N / 3^(K+1)) := by
    unfold gstDigitS
    have hdiv : (N / 3^K) / 3 = N / (3^K * 3) := by
      rw [Nat.div_div_eq_div_mul]
    have hmoddiv := Nat.mod_add_div (N / 3^K) 3
    rw [Nat.pow_succ]
    rw [← hdiv]
    omega
  unfold gstOmegaFutureS gstOmegaNaturalTransferS
  rw [hdecompK, Nat.mul_add]
  have hp1 : 3^(t+1+K) * gstDigitS N K =
      3^(t+1+K) * gstDigitS N K := rfl
  have hp2 : 3^(t+1+K) * (3 * (N / 3^(K+1))) =
      3^(t+1+(K+1)) * (N / 3^(K+1)) := by
    rw [show t + 1 + (K + 1) = (t + 1 + K) + 1 by omega, Nat.pow_succ]
    ring
  rw [hp2]

/-- At the exact natural BIG-N horizon the Future is zero and all information
is in Past. -/
theorem gst_omega_bigN_horizon_future_zeroS (t N : Nat) :
    gstOmegaFutureS t N (N+1) = 0 := by
  unfold gstOmegaFutureS
  have hlt : N < 3^(N+1) := gst_self_lt_three_pow_succS N
  rw [Nat.div_eq_of_lt hlt, Nat.mul_zero]

/-- The corresponding Past is the full original packet. -/
theorem gst_omega_bigN_horizon_past_completeS (t N : Nat) :
    gstOmegaPastS t N (N+1) = 3^(t+1) * N := by
  have hcons := gst_omega_past_future_conservationS t N (N+1)
  rw [gst_omega_bigN_horizon_future_zeroS] at hcons
  omega

/-- Positive original information remains positive in the augmented
Past/Future ledger at every depth, even after visible transfer ends. -/
theorem gst_omega_augmented_information_positive_all_scalesS
    (t N : Nat) (hN : 0 < N) :
    ∀ K, 0 < gstOmegaPastS t N K + gstOmegaFutureS t N K := by
  intro K
  rw [gst_omega_past_future_conservationS]
  have hp : 0 < 3^(t+1) := Nat.pow_pos (by decide)
  exact Nat.mul_pos hp hN

/-- The exact two-cell infinite projector coefficient is the canonical
six-world chord 35, and the event factor `2*6+1=13` raises it to 455. -/
theorem gst_infinite_two_cell_event_kernel_455S
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    (2*6+1) * gstBig1ProjectedPathCodeS a d 2 = 455 := by
  have hcode := gst_big1_clear_infinite_all_six_prefixes_maximalS
    a d hpath h0 2
  rw [hcode]
  decide

/-- One structure carries the three exact conservation layers simultaneously:
Omega additive information, Pi/U multiplicative origin energy, and the fused
kernel/cardinal world equation on the infinite BIG1-clear branch. -/
structure GSTInfiniteOmegaLedgerMasterS
    (t N R : Nat) (a d : Nat → Nat) : Prop where
  omegaAdditive : ∀ K,
    gstOmegaPastS t N K + gstOmegaFutureS t N K = 3^(t+1) * N
  originMultiplicative : ∀ K,
    gstOriginConsumedPrefixUS t N K *
      gstOriginRemainingUS (t+K) (N / 3^K) =
        gstOriginRemainingUS t N
  eleven : GSTInfiniteElevenEquationMasterS R a d
  twoCell455 : (2*6+1) * gstBig1ProjectedPathCodeS a d 2 = 455

/-- Full exact handwritten/infinite synthesis. -/
theorem gst_infinite_omega_ledger_masterS
    (t N R : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    GSTInfiniteOmegaLedgerMasterS t N R a d := by
  refine {
    omegaAdditive := gst_omega_past_future_conservationS t N
    originMultiplicative := gst_origin_prefix_remaining_U_conservationS t N
    eleven := gst_infinite_eleven_equation_masterS R a d hpath h0
    twoCell455 := gst_infinite_two_cell_event_kernel_455S a d hpath h0 }

end GSTInfiniteV2
