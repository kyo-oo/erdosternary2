import GSTFinalResidualEarliestGateBridge
import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

namespace GSTFinalResidualBinaryBoundaryBridge

/-- Two binary columns are exactly one x4 Graph-V2 horizontal step. -/
theorem binary_column_even_is_graph_digit
    (E t p : Nat) :
    GSTPhysicalKernel.binaryColumnDigit E p (2*t) =
      (graph E t p).seven.digit := by
  simp [GSTPhysicalKernel.binaryColumnDigit,
    graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.digit3,
    show 2^(2*t) = 4^t by
      calc
        2^(2*t) = (2^2)^t := by rw [Nat.pow_mul]
        _ = 4^t := by norm_num]

/-- A physical Graph-V2 Happy cell is exactly a binary BIG2 chord across its
corresponding pair of x2 columns.  This is the production replacement for the
old handwritten right-boundary conversion. -/
theorem graph_happy_iff_binary_big2_chord
    (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      GSTPhysicalKernel.binaryColumnDigit E p (2*t) = 2 ∧
      GSTPhysicalKernel.binaryColumnDigit E p (2*(t+1)) = 2 := by
  have hcell := graph_cell_exact E t p
  have hleft := binary_column_even_is_graph_digit E t p
  have hright := binary_column_even_is_graph_digit E (t+1) p
  constructor
  · intro hHappy
    have hout := (happyCell_positive_and_preserves_big2 _ _ hHappy).2
    constructor
    · rw [hleft]
      exact hHappy.1
    · rw [hright, ← hcell.1]
      exact hout
  · rintro ⟨hd0, hd1⟩
    have hDigit : (graph E t p).seven.digit = 2 := by
      rw [← hleft]
      exact hd0
    have hOut : outDigit (graph E t p).seven.carry
        (graph E t p).seven.digit = 2 := by
      rw [hcell.1, ← hright]
      exact hd1
    have hevent :
        GSTCanonicalSevenAxisBridge.event
          (graph E t p).seven.carry
          (graph E t p).seven.digit = 8 := by
      rw [GSTCanonicalSevenAxisBridge.event, hDigit, hOut]
    exact (GSTCanonicalSevenAxisBridge.happy_iff_event_eight _ _
      (graph_carry_lt_four E t p)
      (graph_digit_lt_three E t p)).2 hevent

/-- Level-one parent width is six binary columns; therefore right-boundary
badness is exactly exclusion of the `6 -> 8` BIG2 chord. -/
theorem level_one_right_bad_iff_no_binary_6_8
    (E p : Nat) :
    (¬ HappyCell (graph E 3 p).seven.carry (graph E 3 p).seven.digit) ↔
      ¬ (GSTPhysicalKernel.binaryColumnDigit E p 6 = 2 ∧
         GSTPhysicalKernel.binaryColumnDigit E p 8 = 2) := by
  simpa using not_congr (graph_happy_iff_binary_big2_chord E 3 p)

#check binary_column_even_is_graph_digit
#check graph_happy_iff_binary_big2_chord
#check level_one_right_bad_iff_no_binary_6_8
#print axioms graph_happy_iff_binary_big2_chord

end GSTFinalResidualBinaryBoundaryBridge
