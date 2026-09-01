import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade

/-- Exact universal induction edge to be proved without weakening.

A physical Happy cell on the `4^K` unit sheet must force the existence of
some physical Happy cell on the `4^(K+1)` sheet.  The relocated row is not
assumed to be local to the input row. -/
def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit

/-- Exact vertical future packet beginning one row above a latent x4 cascade.
Nothing is projected away: carry and digit stay on the physical Graph-V2
sheet, carries remain physical, digits remain ternary, and the vertical
recurrence is the literal cell law at every future row. -/
theorem latent_vertical_future_packet
    (K p : Nat)
    (hNext : (graph 1 (K+1) (p+1)).seven.carry = 3) :
    let C : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.carry
    let d : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.digit
    C 0 = 3 ∧
      (∀ r, C r < 4) ∧
      (∀ r, d r < 3) ∧
      (∀ r,
        GST2DMixedEmergence.nextCarry (C r) (d r) = C (r+1)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hNext
  · intro r
    exact graph_carry_lt_four 1 (K+1) (p+1+r)
  · intro r
    exact graph_digit_lt_three 1 (K+1) (p+1+r)
  · intro r
    simpa [Nat.add_assoc] using
      (graph_cell_exact 1 (K+1) (p+1+r)).2

/-- If no relocated Happy witness exists anywhere above row zero, then every
row in the vertical future of a latent packet is physically bad.  This is an
internal contradiction-language adapter only; it does not assume the desired
propagation theorem as a parameter. -/
theorem future_bad_of_no_relocated_happy
    (K p : Nat)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    ∀ r : Nat,
      ¬ HappyCell
        (graph 1 (K+1) (p+1+r)).seven.carry
        (graph 1 (K+1) (p+1+r)).seven.digit := by
  intro r hHappy
  apply hNoRelocated
  exact ⟨p+1+r, by omega, hHappy⟩

#check FourPowerHappyPropagation
#check latent_vertical_future_packet
#check future_bad_of_no_relocated_happy
#print axioms latent_vertical_future_packet
#print axioms future_bad_of_no_relocated_happy

end GSTGraphV2FourPowerRelocation
