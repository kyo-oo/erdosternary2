import GSTGraphV2FourPowerRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FreshPowerPropagation

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2FourPowerRelocation

/-- Fresh Task 3.3 starting lemma.

This theorem uses only the current production relocation laws.  It does not
import any historical classifier, residual/Omega bridge, origin-descent file,
or previous candidate propagation theorem.

If a source Happy row exists on the `K` sheet but the `(K+1)` sheet has no
Happy row anywhere above row zero, then the source overlap forces an exact
latent seed on the next sheet: the same row still has information digit `2`,
the physical carry there is strictly middle (`1` or `2`), and therefore the
very next vertical carry is exactly `3`.
-/
theorem fresh_failed_edge_forces_latent_seed
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    (graph 1 (K+1) p).seven.digit = 2 ∧
      ((graph 1 (K+1) p).seven.carry = 1 ∨
       (graph 1 (K+1) p).seven.carry = 2) ∧
      (graph 1 (K+1) (p+1)).seven.carry = 3 := by
  have hOverlap :=
    (graph_happy_iff_consecutive_digit_two 1 K p).mp hSource
  have hdNext : (graph 1 (K+1) p).seven.digit = 2 := by
    simpa [Nat.add_assoc] using hOverlap.2

  have hNotHappy :
      ¬ HappyCell
        (graph 1 (K+1) p).seven.carry
        (graph 1 (K+1) p).seven.digit := by
    intro hHappy
    apply hNoRelocated
    exact ⟨p, hp, hHappy⟩

  have hCarryLt : (graph 1 (K+1) p).seven.carry < 4 :=
    graph_carry_lt_four 1 (K+1) p

  have hCarryNeZero : (graph 1 (K+1) p).seven.carry ≠ 0 := by
    intro h0
    apply hNotHappy
    exact ⟨hdNext, Or.inl h0⟩

  have hCarryNeThree : (graph 1 (K+1) p).seven.carry ≠ 3 := by
    intro h3
    apply hNotHappy
    exact ⟨hdNext, Or.inr h3⟩

  have hMiddle :
      (graph 1 (K+1) p).seven.carry = 1 ∨
      (graph 1 (K+1) p).seven.carry = 2 := by
    omega

  have hRec := (graph_cell_exact 1 (K+1) p).2
  have hNextCarry : (graph 1 (K+1) (p+1)).seven.carry = 3 := by
    rcases hMiddle with h1 | h2
    · simpa [h1, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm
    · simpa [h2, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm

  exact ⟨hdNext, hMiddle, hNextCarry⟩

/-- Exact failed-edge obstruction packet for the fresh Task 3.3 proof.

Nothing here weakens or localizes the target existential.  Under the literal
negation of the required relocated witness, every positive row of the
`4^(K+1)` sheet is bad.  The supplied source Happy row forces the exact latent
seed at `p`, its whole vertical future is bad, and the same physical sheet is
exactly neutral at the symbolic four-power support cutoff.

The remaining Task 3.3 mathematics is therefore a power-specific
incompatibility theorem for this finite-support packet. -/
theorem fresh_failed_edge_power_obstruction_packet
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    let B := fourPowerSupportCutoff K
    (graph 1 (K+1) p).seven.digit = 2 ∧
      ((graph 1 (K+1) p).seven.carry = 1 ∨
       (graph 1 (K+1) p).seven.carry = 2) ∧
      (graph 1 (K+1) (p+1)).seven.carry = 3 ∧
      (∀ q : Nat, 1 ≤ q →
        ¬ HappyCell
          (graph 1 (K+1) q).seven.carry
          (graph 1 (K+1) q).seven.digit) ∧
      (∀ r : Nat,
        ¬ HappyCell
          (graph 1 (K+1) (p+1+r)).seven.carry
          (graph 1 (K+1) (p+1+r)).seven.digit) ∧
      (graph 1 (K+1) B).seven.carry = 0 ∧
      (graph 1 (K+1) B).seven.digit = 0 := by
  dsimp
  have hSeed :=
    fresh_failed_edge_forces_latent_seed K p hp hSource hNoRelocated
  have hAllBad : ∀ q : Nat, 1 ≤ q →
      ¬ HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit := by
    intro q hq hHappy
    exact hNoRelocated ⟨q, hq, hHappy⟩
  have hFutureBad :=
    future_bad_of_no_relocated_happy K p hNoRelocated
  have hNeutral := four_power_graph_neutral_at_support_cutoff K
  exact ⟨hSeed.1, hSeed.2.1, hSeed.2.2,
    hAllBad, hFutureBad, hNeutral.1, hNeutral.2⟩

#check fresh_failed_edge_forces_latent_seed
#print axioms fresh_failed_edge_forces_latent_seed
#check fresh_failed_edge_power_obstruction_packet
#print axioms fresh_failed_edge_power_obstruction_packet

end Task33FreshPowerPropagation
