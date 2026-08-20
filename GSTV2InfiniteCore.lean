import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# GST V2 production infinite-control core

This module is intentionally independent of `ErdosTernary2.lean`.
It contains only all-Nat information/control primitives that can be imported
by the monolith without creating a circular proof dependency.

Local CREATE/DESTROY/SURVIVE labels describe a change of representation.
The exact ledgers below prove that the represented information itself is not
annihilated when a visible future channel becomes zero.
-/

/-- The three physical GST spaces.  The legacy two-space/duality language is
not used as a foundational type in V2. -/
inductive Space
  | null
  | altMinus
  | gstPlus
  deriving DecidableEq, Repr

/-- `k`-th least-significant ternary information digit. -/
def digit (N k : Nat) : Nat := N / 3^k % 3

/-- One local multiply-by-four information mass. -/
def cellMass (carry d : Nat) : Nat := carry + 4*d

/-- Visible output digit of one local cell. -/
def cellOutput (carry d : Nat) : Nat := cellMass carry d % 3

/-- Transported carry after one local cell. -/
def cellNextCarry (carry d : Nat) : Nat := cellMass carry d / 3

/-- Exact local conservation: a cell only repartitions its information mass
between the visible output coordinate and the transported carry coordinate. -/
theorem cell_mass_conservation (carry d : Nat) :
    cellMass carry d = cellOutput carry d + 3 * cellNextCarry carry d := by
  unfold cellMass cellOutput cellNextCarry
  have h := Nat.mod_add_div (carry + 4*d) 3
  omega

/-- Information transferred from the origin packet at coordinate `k`, kept in
the original absolute scale. -/
def omegaTransfer (t N k : Nat) : Nat := 3^(t+1+k) * digit N k

/-- Information already emitted below observation depth `K`. -/
def omegaPast (t N K : Nat) : Nat :=
  Finset.sum (Finset.range K) (fun k => omegaTransfer t N k)

/-- Information not yet emitted at observation depth `K`, expressed in the
same absolute scale as `omegaPast`. -/
def omegaFuture (t N K : Nat) : Nat := 3^(t+1+K) * (N / 3^K)

/-- Exact ternary prefix reconstruction. -/
theorem digit_prefix_value (N K : Nat) :
    (∑ k in Finset.range K, 3^k * digit N k) = N % 3^K := by
  induction K with
  | zero => simp [digit]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold digit
      rw [Nat.pow_succ, Nat.mod_mul]

/-- Closed form for information already transferred into Ω-Past. -/
theorem omega_past_closed (t N K : Nat) :
    omegaPast t N K = 3^(t+1) * (N % 3^K) := by
  unfold omegaPast omegaTransfer
  calc
    (∑ k in Finset.range K, 3^(t+1+k) * digit N k) =
        ∑ k in Finset.range K, 3^(t+1) * (3^k * digit N k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.pow_add]
          ring
    _ = 3^(t+1) * (∑ k in Finset.range K, 3^k * digit N k) := by
          rw [Finset.mul_sum]
    _ = 3^(t+1) * (N % 3^K) := by
          rw [digit_prefix_value]

/-- Exact all-depth information conservation.

At every natural observation depth, emitted Past plus un-emitted Future is the
same original packet.  In particular `Future = 0` is a support-horizon fact,
not destruction of information. -/
theorem omega_past_future_conservation (t N K : Nat) :
    omegaPast t N K + omegaFuture t N K = 3^(t+1) * N := by
  rw [omega_past_closed]
  unfold omegaFuture
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

/-- Past gains exactly the packet that Future loses at the next depth. -/
theorem omega_past_step (t N K : Nat) :
    omegaPast t N (K+1) = omegaPast t N K + omegaTransfer t N K := by
  unfold omegaPast
  rw [Finset.sum_range_succ]

/-- Elementary explicit support ceiling, avoiding logarithms. -/
theorem self_lt_three_pow_succ : ∀ N : Nat, N < 3^(N+1)
  | 0 => by decide
  | N+1 => by
      have ih : N < 3^(N+1) := self_lt_three_pow_succ N
      have hp : 0 < 3^(N+1) := Nat.pow_pos (by decide)
      have hle : N+1 ≤ 3^(N+1) := by omega
      rw [show (N+1)+1 = (N+1)+1 by rfl, Nat.pow_succ]
      omega

/-- Every natural origin has an explicit all-Nat zero-support horizon. -/
theorem digit_eventually_zero (N k : Nat) (hk : N + 1 ≤ k) : digit N k = 0 := by
  have hpow : 3^(N+1) ≤ 3^k :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hk
  have hlt : N < 3^k := lt_of_lt_of_le (self_lt_three_pow_succ N) hpow
  have hdiv : N / 3^k = 0 := Nat.div_eq_of_lt hlt
  simp [digit, hdiv]

/-- All-depth support is a controller property, not a large finite cutoff. -/
def InfiniteOriginSupport (N : Nat) : Prop :=
  ∀ K, ∃ k, K ≤ k ∧ digit N k ≠ 0

/-- No ordinary finite natural can realize an all-depth nonzero origin stream. -/
theorem finite_origin_collision (N : Nat) : ¬ InfiniteOriginSupport N := by
  intro hinf
  obtain ⟨k, hk, hnz⟩ := hinf (N+1)
  exact hnz (digit_eventually_zero N k hk)

/-- Support-horizon controller: the stream remains Nat-indexed at every depth,
while all information past the explicit natural horizon is proved zero and the
Past/Future ledger remains conserved everywhere. -/
structure SupportHorizonControl (t N : Nat) : Prop where
  futureZero : ∀ k, N + 1 ≤ k → N / 3^k = 0
  informationConserved : ∀ K,
    omegaPast t N K + omegaFuture t N K = 3^(t+1) * N

/-- Every natural packet has a canonical support-horizon controller. -/
theorem support_horizon_control (t N : Nat) : SupportHorizonControl t N := by
  constructor
  · intro k hk
    have hpow : 3^(N+1) ≤ 3^k :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hk
    exact Nat.div_eq_of_lt
      (lt_of_lt_of_le (self_lt_three_pow_succ N) hpow)
  · exact omega_past_future_conservation t N

end GSTV2
