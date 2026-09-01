import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GST2DMixedEmergence
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

/-- A physical Graph-V2 cell is Happy exactly when information digit two is
present at the cell and survives the horizontal x4 step at the same row. -/
theorem graph_happy_iff_consecutive_digit_two
    (E t p : Nat) :
    HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit ↔
      (graph E t p).seven.digit = 2 ∧
        (graph E (t+1) p).seven.digit = 2 := by
  constructor
  · intro hHappy
    rcases hHappy with ⟨hd, hcarry⟩
    refine ⟨hd, ?_⟩
    have hHappy' : HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit := ⟨hd, hcarry⟩
    have hout :=
      (happyCell_positive_and_preserves_big2
        (graph E t p).seven.carry
        (graph E t p).seven.digit hHappy').2
    rw [← (graph_cell_exact E t p).1]
    exact hout
  · rintro ⟨hd, hnext⟩
    refine ⟨hd, ?_⟩
    have hout :
        outDigit
          (graph E t p).seven.carry
          (graph E t p).seven.digit = 2 := by
      rw [(graph_cell_exact E t p).1]
      exact hnext
    have hcarryLt := graph_carry_lt_four E t p
    have hcases :
        (graph E t p).seven.carry = 0 ∨
        (graph E t p).seven.carry = 1 ∨
        (graph E t p).seven.carry = 2 ∨
        (graph E t p).seven.carry = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · exact Or.inl h0
    · rw [h1, hd] at hout
      norm_num [outDigit] at hout
    · rw [h2, hd] at hout
      norm_num [outDigit] at hout
    · exact Or.inr h3

/-- Arithmetic form of the same physical law on a pure four-power sheet.
The carry condition has disappeared completely: a Happy witness is exactly a
shared ternary digit-two position of two consecutive powers of four. -/
theorem four_power_happy_iff_consecutive_digit_two
    (K p : Nat) :
    GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) ↔
      GSTCanonicalTailStateIso.digit3 (4^K) p = 2 ∧
        GSTCanonicalTailStateIso.digit3 (4^(K+1)) p = 2 := by
  simpa [GSTGraphV2InfiniteControl.graph,
    GSTGraphV2InfiniteControl.cell,
    GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.carry4,
    GSTCanonicalSevenAxisBridge.digit3,
    GSTU2DEventTransport.HappyCell,
    GSTCanonicalTailStateIso.HappyCell,
    GSTCanonicalTailStateIso.carry4,
    GSTCanonicalTailStateIso.digit3] using
      (graph_happy_iff_consecutive_digit_two 1 K p)

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
#check graph_happy_iff_consecutive_digit_two
#check four_power_happy_iff_consecutive_digit_two
#check latent_vertical_future_packet
#check future_bad_of_no_relocated_happy
#print axioms graph_happy_iff_consecutive_digit_two
#print axioms four_power_happy_iff_consecutive_digit_two
#print axioms latent_vertical_future_packet
#print axioms future_bad_of_no_relocated_happy

end GSTGraphV2FourPowerRelocation
