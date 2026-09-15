import GSTGraphV2Ontological

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace GSTWorldtraceBoundary

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological

/-- The digit-potential contribution of a finite vertical trace. -/
def digitPotentialPrefix (d : Nat → Nat) : Nat → Int
  | 0 => 0
  | K+1 => digitPotentialPrefix d K +
      (3^K : Int) * ontDigitPotential (d K)

/-- Combine the proved horizontal current telescope with its vertical
telescope. Both carry boundaries remain in the equality. -/
theorem rectangle_boundary_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hout : ∀ t p, t < N → p < K →
      outDigit (C t p) (d t p) = d (t+1) p)
    (hnext : ∀ t p, t < N → p < K →
      nextCarry (C t p) (d t p) = C t (p+1)) :
    weightedOntPrefix C d N K =
      digitPotentialPrefix (d N) K -
      (7^N : Int) * digitPotentialPrefix (d 0) K +
      reverseOntCarryCode (fun t => C t 0) N -
      (3^K : Int) * reverseOntCarryCode (fun t => C t K) N := by
  revert hout hnext
  induction K with
  | zero =>
      intros
      simp [weightedOntPrefix, digitPotentialPrefix]
  | succ K ih =>
      intro hout hnext
      have ih' := ih
        (fun t p ht hp => hout t p ht (by omega))
        (fun t p ht hp => hnext t p ht (by omega))
      have hrow := reverseOntCode_exact
        (fun t => C t K) (fun t => C t (K+1))
        (fun t => d t K) N
        (fun t ht => hout t K ht (by omega))
        (fun t ht => hnext t K ht (by omega))
      rw [weightedOntPrefix, ih', hrow,
        digitPotentialPrefix, digitPotentialPrefix]
      push_cast
      rw [pow_succ]
      ring

def graphDigitPrefix (E t b K : Nat) : Int :=
  digitPotentialPrefix (fun j => (graph E t (b+j)).seven.digit) K

def graphCarryBoundary (E N p : Nat) : Int :=
  reverseOntCarryCode (fun t => (graph E t p).seven.carry) N

/-- Exact boundary evaluation on the existing physical worldtrace graph. -/
theorem graph_boundary_exact (E N b K : Nat) :
    graphOntWindow E N b K =
      graphDigitPrefix E N b K -
      (7^N : Int) * graphDigitPrefix E 0 b K +
      graphCarryBoundary E N b -
      (3^K : Int) * graphCarryBoundary E N (b+K) := by
  unfold graphOntWindow graphDigitPrefix graphCarryBoundary
  simpa only [Nat.add_zero] using
    rectangle_boundary_exact
      (fun t j => (graph E t (b+j)).seven.carry)
      (fun t j => (graph E t (b+j)).seven.digit) N K
      (fun t p _ _ => (graph_cell_exact E t (b+p)).1)
      (fun t p _ _ => by
        simpa only [Nat.add_assoc] using (graph_cell_exact E t (b+p)).2)

/-- A source Happy cell forces this precise boundary inequality.
In particular, the upper carry boundary cannot simply be discarded. -/
theorem happy_forces_boundary_excess
    (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    (7^N : Int) * graphDigitPrefix E 0 b (q+1) +
      (3^(q+1) : Int) * graphCarryBoundary E N (b+(q+1)) <
      graphDigitPrefix E N b (q+1) + graphCarryBoundary E N b := by
  have h := graphOntWindow_positive_of_happy E N b q hN hHappy
  rw [graph_boundary_exact] at h
  omega

/-- All-depth badness implies a nonpositive current on every vertical prefix
of the same column. This keeps the quantifier over all rows. -/
theorem bad_column_prefix_nonpositive
    (E b : Nat)
    (hBad : ∀ j, ¬ HappyCell
      (graph E 0 (b+j)).seven.carry
      (graph E 0 (b+j)).seven.digit) :
    ∀ K, graphOntWindow E 1 b K ≤ 0 := by
  intro K
  induction K with
  | zero => simp [graphOntWindow, weightedOntPrefix]
  | succ K ih =>
      have hcell := ontDensity_nonpositive_of_not_happy
        (graph E 0 (b+K)).seven.carry
        (graph E 0 (b+K)).seven.digit
        (graph_carry_lt_four E 0 (b+K))
        (graph_digit_lt_three E 0 (b+K)) (hBad K)
      have hterm : (3^K : Int) * ontDensity
          (graph E 0 (b+K)).seven.carry
          (graph E 0 (b+K)).seven.digit ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcell
      change weightedOntPrefix
        (fun t j => (graph E t (b+j)).seven.carry)
        (fun t j => (graph E t (b+j)).seven.digit) 1 K ≤ 0 at ih
      simpa only [graphOntWindow, weightedOntPrefix, reverseOntCode,
        mul_zero, zero_add, Nat.cast_pow, Nat.cast_ofNat] using add_nonpos ih hterm

/-- Worldtrace characterization of all-depth badness by exact boundary
inequalities. The reverse direction uses the proved highest-row domination,
not an assumed transfer of a Happy witness between columns. -/
theorem bad_column_iff_boundary_inequalities (E b : Nat) :
    (∀ j, ¬ HappyCell
      (graph E 0 (b+j)).seven.carry
      (graph E 0 (b+j)).seven.digit) ↔
    ∀ K,
      graphDigitPrefix E 1 b K -
        7 * graphDigitPrefix E 0 b K +
        graphCarryBoundary E 1 b ≤
      (3^K : Int) * graphCarryBoundary E 1 (b+K) := by
  constructor
  · intro hBad K
    have h := bad_column_prefix_nonpositive E b hBad K
    rw [graph_boundary_exact] at h
    norm_num only [pow_one] at h
    omega
  · intro h j hHappy
    have hpos := graphOntWindow_positive_of_happy E 1 b j (by decide) hHappy
    rw [graph_boundary_exact] at hpos
    norm_num only [pow_one] at hpos
    have hbound := h (j+1)
    omega

#print axioms rectangle_boundary_exact
#print axioms graph_boundary_exact
#print axioms happy_forces_boundary_excess
#print axioms bad_column_iff_boundary_inequalities

end GSTWorldtraceBoundary
