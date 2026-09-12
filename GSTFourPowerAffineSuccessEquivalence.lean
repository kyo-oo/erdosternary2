import GSTFourPowerAffineIteratedRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSuccessEquivalence

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffineIteratedRelocation

/-- The reverse exact-row lift.  If the original affine pair has digit `2`
at row `n` on both sides, then after exactly `n` channel reads the low pair is
literally a `lowSuccess`.  No navigation or witness transport is involved. -/
theorem exact_row_pair_forces_iterated_lowSuccess
    (c x n : Nat)
    (hx : digit3 x n = 2)
    (hy : digit3 (4*x+c) n = 2) :
    lowSuccess (iterChannel n c x) (iterSource n x) := by
  induction n generalizing c x with
  | zero =>
      have hx0 : lowDigit x = 2 := by
        rw [← digit3_zero_source x]
        exact hx
      have hy0 : channelOut c (lowDigit x) = 2 := by
        rw [← digit3_zero_channel c x]
        exact hy
      simpa [iterChannel, iterSource, lowSuccess] using And.intro hx0 hy0
  | succ n ih =>
      have hx' : digit3 (tail3 x) n = 2 := by
        rw [← digit3_succ_tail x n]
        simpa [Nat.succ_eq_add_one] using hx
      have hy' :
          digit3 (4 * tail3 x + channelNext c (lowDigit x)) n = 2 := by
        rw [← digit3_succ_channel c x n]
        simpa [Nat.succ_eq_add_one] using hy
      have hnext := ih
        (c := channelNext c (lowDigit x))
        (x := tail3 x) hx' hy'
      simpa [iterChannel, iterSource] using hnext

/-- Exact finite-depth characterization of an affine common-two pair.
The successful channel depth is exactly the original common-two row. -/
theorem pairCommonTwo_iff_exists_iterated_lowSuccess
    (c x : Nat) :
    PairCommonTwo x (4*x+c) ↔
      ∃ n : Nat,
        lowSuccess (iterChannel n c x) (iterSource n x) := by
  constructor
  · rintro ⟨n, hx, hy⟩
    exact ⟨n, exact_row_pair_forces_iterated_lowSuccess c x n hx hy⟩
  · rintro ⟨n, hn⟩
    exact iterated_lowSuccess_constructs_pair_common_two c x n hn

/-- The four-power direct common-two predicate is *exactly* finite success of
the fresh channel-one affine orbit.  This upgrades the previous one-way
reduction to an equivalence. -/
theorem commonTwo_iff_exists_iterated_affine_low_success
    (N : Nat) :
    CommonTwo N ↔
      ∃ n : Nat,
        lowSuccess
          (iterChannel n 1 (affineOrbit N))
          (iterSource n (affineOrbit N)) := by
  rw [commonTwo_iff_channel_one N]
  exact pairCommonTwo_iff_exists_iterated_lowSuccess 1 (affineOrbit N)

/-- Exact formulation of the remaining universal arithmetic pressure point.
`FourPowerDirectExistence` is equivalent, not merely reducible, to finite
channel success for every admissible exponent. -/
theorem directExistence_iff_iterated_affine_low_success :
    FourPowerDirectExistence ↔
      ∀ N : Nat, 5 ≤ N → N ≠ 7 →
        ∃ n : Nat,
          lowSuccess
            (iterChannel n 1 (affineOrbit N))
            (iterSource n (affineOrbit N)) := by
  constructor
  · intro hDirect N hN h7
    exact (commonTwo_iff_exists_iterated_affine_low_success N).1
      (hDirect N hN h7)
  · intro hforce
    exact directExistence_of_iterated_affine_low_success hforce

/-- A direct common-two proof for the next exponent now canonically exposes a
finite channel depth and returns the concrete physical relocated row `q=n+1`.
This is an exact witness-producing adapter, not an existential reselection. -/
theorem commonTwo_constructs_channel_exact_relocated_row
    (K : Nat) (h : CommonTwo (K+1)) :
    ∃ n q : Nat, q = n+1 ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rcases (commonTwo_iff_exists_iterated_affine_low_success (K+1)).1 h with
    ⟨n, hn⟩
  rcases iterated_affine_low_success_constructs_exact_relocated_row K n hn with
    ⟨q, hqeq, hq, hHappy⟩
  exact ⟨n, q, hqeq, hq, hHappy⟩

#check exact_row_pair_forces_iterated_lowSuccess
#check pairCommonTwo_iff_exists_iterated_lowSuccess
#check commonTwo_iff_exists_iterated_affine_low_success
#check directExistence_iff_iterated_affine_low_success
#check commonTwo_constructs_channel_exact_relocated_row
#print axioms exact_row_pair_forces_iterated_lowSuccess
#print axioms pairCommonTwo_iff_exists_iterated_lowSuccess
#print axioms commonTwo_iff_exists_iterated_affine_low_success
#print axioms directExistence_iff_iterated_affine_low_success
#print axioms commonTwo_constructs_channel_exact_relocated_row

end GSTFourPowerAffineSuccessEquivalence
