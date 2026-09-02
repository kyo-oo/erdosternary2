import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectExistence

open GSTFourPowerDirectResidue

/-- Pure arithmetic common-digit predicate for two consecutive powers of four.
This is the primary object of the corrected proof architecture: it contains no
source Happy witness, relocation hypothesis, or propagation edge. -/
def CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧
    digit3 (4^(K+1)) p = 2

/-- The actual universal arithmetic target, isolated from all propagation
machinery. The only exceptional exponent in the statement is `7`. -/
def FourPowerDirectExistence : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K

/-- A common-two witness in particular proves that the source power itself has
a ternary digit two. -/
theorem commonTwo_has_source_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 := by
  rcases h with ⟨p, hp, h0, h1⟩
  exact ⟨p, hp, h0⟩

/-- Symmetrically, a common-two witness gives a ternary digit two in the next
power as well. -/
theorem commonTwo_has_target_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^(K+1)) p = 2 := by
  rcases h with ⟨p, hp, h0, h1⟩
  exact ⟨p, hp, h1⟩

/-- The exact row-two classifier gives a direct common witness in exponent
classes five and six modulo nine. -/
theorem commonTwo_of_mod9_five_or_six
    (K : Nat) (hres : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K := by
  refine ⟨2, by norm_num, ?_⟩
  exact row_two_overlap_of_mod9_five_or_six K hres

/-- Therefore a hypothetical counterexample to the direct theorem cannot lie
in either exact row-two overlap class. -/
theorem noCommonTwo_excludes_mod9_five_six
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 := by
  exact no_common_two_forbids_mod9_five_six K hNo

/-- The direct universal target implies the corresponding source-digit-two
existence statement immediately. This records the genuine arithmetic strength
of the remaining boundary. -/
theorem directExistence_implies_source_two
    (h : FourPowerDirectExistence)
    (K : Nat) (hK : 5 ≤ K) (h7 : K ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 := by
  exact commonTwo_has_source_two K (h K hK h7)

#check CommonTwo
#check FourPowerDirectExistence
#check commonTwo_has_source_two
#check commonTwo_has_target_two
#check commonTwo_of_mod9_five_or_six
#check noCommonTwo_excludes_mod9_five_six
#check directExistence_implies_source_two
#print axioms commonTwo_has_source_two
#print axioms commonTwo_has_target_two
#print axioms commonTwo_of_mod9_five_or_six
#print axioms noCommonTwo_excludes_mod9_five_six
#print axioms directExistence_implies_source_two

end GSTFourPowerDirectExistence
