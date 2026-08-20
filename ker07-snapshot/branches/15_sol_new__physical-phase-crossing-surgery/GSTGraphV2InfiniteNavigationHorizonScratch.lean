import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Exact handwritten BIG-N as an infinite Navigation-horizon object

In the Aug-17 handwritten algebra, BIG-N is the ordinary natural Navigation
horizon.  The Omega information stream is still a function on every natural
index; BIG-N says the fixed natural packet has exhausted its future transfer
by its own Navigation coordinate N.
-/

/-- Positive N lies strictly below 3^N. -/
theorem gst_bigN_self_lt_three_powS :
    ∀ N : Nat, 1 ≤ N → N < 3^N
  | 0, hN => by omega
  | N+1, hN => by
      by_cases h0 : N = 0
      · subst N
        decide
      · have ih : N < 3^N := gst_bigN_self_lt_three_powS N (by omega)
        have hp : 0 < 3^N := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega

/-- At BIG-N itself, the remaining natural descent is zero. -/
theorem gst_bigN_navigation_descent_zeroS
    (N : Nat) (hN : 1 ≤ N) :
    N / 3^N = 0 := by
  exact Nat.div_eq_of_lt (gst_bigN_self_lt_three_powS N hN)

/-- Therefore the information digit at BIG-N is zero. -/
theorem gst_bigN_navigation_digit_zeroS
    (N : Nat) (hN : 1 ≤ N) :
    gstDigitS N N = 0 := by
  unfold gstDigitS
  rw [gst_bigN_navigation_descent_zeroS N hN]

/-- The Omega transfer packet at the Navigation horizon is exactly zero. -/
theorem gst_bigN_omega_transfer_zeroS
    (t N : Nat) (hN : 1 ≤ N) :
    gstOmegaNaturalTransferS t N N = 0 := by
  unfold gstOmegaNaturalTransferS
  rw [gst_bigN_navigation_digit_zeroS N hN]

/-- BIG-N kills every later information transfer as well.  The Omega object is
still Nat-indexed; its support is proved to lie strictly below N. -/
theorem gst_bigN_omega_transfer_zero_from_horizonS
    (t N i : Nat) (hN : 1 ≤ N) (hi : N ≤ i) :
    gstOmegaNaturalTransferS t N i = 0 := by
  unfold gstOmegaNaturalTransferS
  have hbase : N < 3^N := gst_bigN_self_lt_three_powS N hN
  have hpow : 3^N ≤ 3^i :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hi
  have hlt : N < 3^i := lt_of_lt_of_le hbase hpow
  have hdiv : N / 3^i = 0 := Nat.div_eq_of_lt hlt
  simp [gstDigitS, hdiv]

/-- The entire BIG-N Omega energy has already moved into the finite prefix
strictly before N. -/
theorem gst_bigN_omega_prefix_is_totalS
    (t N : Nat) (hN : 1 ≤ N) :
    Finset.sum (Finset.range N) (fun i => gstOmegaNaturalTransferS t N i) =
      3^(t+1) * N := by
  rw [gst_omega_natural_transfer_prefixS]
  have hlt : N < 3^N := gst_bigN_self_lt_three_powS N hN
  rw [Nat.mod_eq_of_lt hlt]

/-- Any observation depth at or beyond BIG-N sees the same exact total energy. -/
theorem gst_bigN_omega_prefix_stable_from_horizonS
    (t N K : Nat) (hN : 1 ≤ N) (hK : N ≤ K) :
    Finset.sum (Finset.range K) (fun i => gstOmegaNaturalTransferS t N i) =
      3^(t+1) * N := by
  rw [gst_omega_natural_transfer_prefixS]
  have hbase : N < 3^N := gst_bigN_self_lt_three_powS N hN
  have hpow : 3^N ≤ 3^K :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hK
  have hlt : N < 3^K := lt_of_lt_of_le hbase hpow
  rw [Nat.mod_eq_of_lt hlt]

/-- Exact BIG-N infinite controller: one Nat-indexed stream, finite support
proved at N, exact total Omega energy, plus Pi conservation at every origin
scale. -/
def GSTBigNInfiniteControlS (t N : Nat) : Prop :=
  1 ≤ N ∧
  (∀ i, N ≤ i → gstOmegaNaturalTransferS t N i = 0) ∧
  (∀ K, N ≤ K →
    Finset.sum (Finset.range K) (fun i => gstOmegaNaturalTransferS t N i) =
      3^(t+1) * N) ∧
  GSTOriginInfiniteMulDivControlS t N

theorem gst_bigN_infinite_controlS
    (t N : Nat) (hN : 1 ≤ N) :
    GSTBigNInfiniteControlS t N := by
  refine ⟨hN, ?_, ?_, gst_origin_infinite_mul_div_controlS t N⟩
  · intro i hi
    exact gst_bigN_omega_transfer_zero_from_horizonS t N i hN hi
  · intro K hK
    exact gst_bigN_omega_prefix_stable_from_horizonS t N K hN hK

/-- Source-faithful two-regime interface.  This is a tagged interface, not an
assertion that one branch logically implies the other: callers supply the
handwritten BIG-N case or the pathwise no-BIG1 case explicitly. -/
inductive GSTHandwrittenInformationCaseS
  | bigN (t N : Nat) (positive : 1 ≤ N)
  | notBig1 (a d : Nat → Nat)
      (path : GSTBig1ClearInfinitePathS a d)
      (nonzero : d 0 ≠ 0)

def GSTHandwrittenInformationCaseControlledS :
    GSTHandwrittenInformationCaseS → Prop
  | .bigN t N _ => GSTBigNInfiniteControlS t N
  | .notBig1 a d _ _ =>
      (∀ j, gstBinaryBridgeMassS (a j) (d j) = 5) ∧
      (∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1)

theorem gst_handwritten_information_case_controlS
    (r : GSTHandwrittenInformationCaseS) :
    GSTHandwrittenInformationCaseControlledS r := by
  cases r with
  | bigN t N positive =>
      exact gst_bigN_infinite_controlS t N positive
  | notBig1 a d path nonzero =>
      constructor
      · intro j
        exact (gst_big1_clear_infinite_edges_are_surviveS
          a d path nonzero j).2.2.2.1
      · exact gst_big1_clear_infinite_all_six_prefixes_maximalS
          a d path nonzero

end GSTInfiniteV2
