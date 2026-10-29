import GSTFourPowerExponentTritObstruction
import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Unconditional binary extension of genuine no-common-two exponent prefixes

Unlike finite good-cylinder density, this direction produces TWO distinct
original perfect-power exponent lifts avoiding a common two at the next row
for EVERY surviving physical exponent prefix.

This prevents proving universal hGate by a finite-branch extinction argument.
It does not produce one fixed natural exponent that survives all rows:
the exponent may change at every extension. Eventual zero of the exponent
trits remains a separate global obstruction.
-/

namespace GSTProblem406BinarySurvivorExtensions

open GSTFourPowerDirectResidue

/-- Literal original physical no-common-two condition on rows 1,...,p. -/
def SurvivesRows (K p : Nat) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ p →
    ¬ (digit3 (4^K) j = 2 ∧ digit3 (4^(K+1)) j = 2)

/-- For each incoming source digit there are at least two distinct
exponent trits that avoid a source digit two after lifting. -/
theorem two_distinct_trits_avoid_two
    (d : Nat) (hd : d < 3) :
    ∃ a b : Nat, a < 3 ∧ b < 3 ∧ a ≠ b ∧
      (d+a)%3 ≠ 2 ∧ (d+b)%3 ≠ 2 := by
  interval_cases d
  · exact ⟨0,1,by decide,by decide,by decide,by decide,by decide⟩
  · exact ⟨0,2,by decide,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,2,by decide,by decide,by decide,by decide,by decide⟩

/-- A free high ternary exponent trit modifies the physical power digit
at row p+1 by its literal residue, not by an invented controller value. -/
theorem two_real_power_lifts_avoid_next_source_two
    (K p : Nat) :
    ∃ a b : Nat, a<3 ∧ b<3 ∧ a≠b ∧
      digit3 (4^(K+a*3^p)) (p+1) ≠ 2 ∧
      digit3 (4^(K+b*3^p)) (p+1) ≠ 2 := by
  let d := digit3 (4^K) (p+1)
  have hd : d < 3 := by
    dsimp [d, digit3]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨a,b,ha,hb,hab,hda,hdb⟩ :=
    two_distinct_trits_avoid_two d hd
  refine ⟨a,b,ha,hb,hab,?_,?_⟩
  · rw [pow4_exponent_trit_lift_digit p K a ha]
    exact hda
  · rw [pow4_exponent_trit_lift_digit p K b hb]
    exact hdb

/-- Shifting an exponent by any multiple of 3^p preserves BOTH original
physical digits at every lower position j≤p, without reinterpreting K. -/
theorem source_neighbor_digit_preserved_at_lower_row
    (K p a j : Nat) (hj : j ≤ p) :
    digit3 (4^(K+a*3^p)) j = digit3 (4^K) j ∧
    digit3 (4^((K+a*3^p)+1)) j =
      digit3 (4^(K+1)) j := by
  have hpow : 3^j * 3^(p-j) = 3^p := by
    calc
      3^j * 3^(p-j) = 3^(j+(p-j)) := (pow_add 3 j (p-j)).symm
      _ = 3^p := by congr 1; omega
  have hshape : K+a*3^p = K+3^j*(3^(p-j)*a) := by
    rw [← hpow]
    ring
  have hshapeNext :
      (K+a*3^p)+1 = (K+1)+3^j*(3^(p-j)*a) := by
    omega
  constructor
  · rw [hshape]
    exact pow4_digit_period j K (3^(p-j)*a)
  · rw [hshapeNext]
    exact pow4_digit_period j (K+1) (3^(p-j)*a)

/-- Every physically surviving prefix branches into at least TWO
different next exponent trits and both children survive the NEXT row.
No additional Happy premise or custom gate appears. -/
theorem every_survivor_has_two_next_lifts
    (K p : Nat) (h : SurvivesRows K p) :
    ∃ a b : Nat, a<3 ∧ b<3 ∧ a≠b ∧
      SurvivesRows (K+a*3^p) (p+1) ∧
      SurvivesRows (K+b*3^p) (p+1) := by
  obtain ⟨a,b,ha,hb,hab,havoidA,havoidB⟩ :=
    two_real_power_lifts_avoid_next_source_two K p
  refine ⟨a,b,ha,hb,hab,?_,?_⟩
  · intro j hj1 hjp hp
    by_cases hj0 : j ≤ p
    · obtain ⟨hs,hn⟩ :=
        source_neighbor_digit_preserved_at_lower_row K p a j hj0
      exact h j hj1 hj0 ⟨hs.symm.trans hp.1,hn.symm.trans hp.2⟩
    · have hjlast : j = p+1 := by omega
      subst j
      exact havoidA hp.1
  · intro j hj1 hjp hp
    by_cases hj0 : j ≤ p
    · obtain ⟨hs,hn⟩ :=
        source_neighbor_digit_preserved_at_lower_row K p b j hj0
      exact h j hj1 hj0 ⟨hs.symm.trans hp.1,hn.symm.trans hp.2⟩
    · have hjlast : j = p+1 := by omega
      subst j
      exact havoidB hp.1

/-- When the parent is its canonical residue representative, the two
surviving children are distinct integer representatives of the
two different exponent residue classes modulo 3^(p+1). -/
theorem canonical_survivor_has_distinct_bounded_children
    (K p : Nat) (hK : K < 3^p) (h : SurvivesRows K p) :
    ∃ A B : Nat, A < 3^(p+1) ∧ B < 3^(p+1) ∧ A ≠ B ∧
      SurvivesRows A (p+1) ∧ SurvivesRows B (p+1) := by
  obtain ⟨a,b,ha,hb,hab,hsa,hsb⟩ :=
    every_survivor_has_two_next_lifts K p h
  let A := K+a*3^p
  let B := K+b*3^p
  have hpow : 3^(p+1) = 3^p*3 := by rw [pow_succ]
  have hA : A < 3^(p+1) := by
    dsimp [A]
    rw [hpow]
    interval_cases a <;> omega
  have hB : B < 3^(p+1) := by
    dsimp [B]
    rw [hpow]
    interval_cases b <;> omega
  have hdiff : A ≠ B := by
    dsimp [A,B]
    intro heq
    have hnonzero : 0 < 3^p := by positivity
    have hmul : a*3^p=b*3^p := by omega
    have : a=b := (Nat.mul_right_cancel hnonzero hmul)
    exact hab this
  exact ⟨A,B,hA,hB,hdiff,hsa,hsb⟩

#print axioms two_distinct_trits_avoid_two
#print axioms two_real_power_lifts_avoid_next_source_two
#print axioms source_neighbor_digit_preserved_at_lower_row
#print axioms every_survivor_has_two_next_lifts
#print axioms canonical_survivor_has_distinct_bounded_children

end GSTProblem406BinarySurvivorExtensions
