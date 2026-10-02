import ErdosTernary2
import GSTFourPowerDirectExistence
import GSTFourPowerDirectResidue243

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# Four-power direct-existence closure

This file is the surgical replacement surface for the single historical
`gst_four_power_direct_existence_inline` boundary. Every lemma here is
assumption-free apart from explicit arithmetic hypotheses in the target; no
provider/gate/grant proposition is accepted as a substitute for mathematics.
-/

namespace GSTFourPowerDirectExistenceClosure

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue81
open GSTFourPowerDirectResidue243
open GSTFourPowerExponentTritObstruction

/-- A certified full-power GST+/NULL witness is already the exact same-row
`CommonTwo` event. -/
theorem commonTwo_of_div_three
    (K : Nat) (hK5 : 5 ≤ K) (hK3 : K % 3 = 0) :
    CommonTwo K := by
  obtain ⟨p, hp, _hpN, hd, hspace⟩ :=
    gst_graph_witness_four_pow_div_three K hK5 hK3
  have hCmod : gstCarry (4^K) p % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero (4^K) p hspace
  have hClt : gstCarry (4^K) p < 4 :=
    gstCarry_lt_four (4^K) p hp
  have hgood : gstCarry (4^K) p = 0 ∨ gstCarry (4^K) p = 3 := by
    omega
  have hlift :=
    gst_pure_lift_or_forced_cascade (4^K) p hp hd hgood
  have hdnext : gstDigit (4 * 4^K) p = 2 := by
    rcases hlift with h | h
    · exact h.1
    · exact h.1
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTFourPowerDirectResidue.digit3, gstDigit] using hd
  · have hpow : 4^(K+1) = 4 * 4^K := by
      rw [Nat.pow_succ]
      ring
    rw [hpow]
    simpa [GSTFourPowerDirectResidue.digit3, gstDigit] using hdnext

/-- The post-`de11` row-five classifier is pure direct arithmetic. -/
theorem commonTwo_of_mod243_row_five
    (K : Nat) (hres : RowFiveClass (K % 243)) :
    CommonTwo K := by
  refine ⟨5, by norm_num, ?_⟩
  exact row_five_overlap_of_mod243_classes K hres

/-- Structural row-six lift salvaged from the relocation branch, but stated
straight at the production object `CommonTwo`.  This avoids importing the old
Happy/provider transport stack.  The only normalization is on the small prefix
`m`, never on the full exponent `N`. -/
theorem commonTwo_of_mod729_lifted_prefix
    (N m a : Nat) (ha : a < 3)
    (hN : N % 729 = m + a * 3^5)
    (h0 : (digit3 (4^m) 6 + a) % 3 = 2)
    (h1 : (digit3 (4^(m+1)) 6 + a) % 3 = 2) :
    CommonTwo N := by
  have hm := Nat.mod_add_div N 729
  rw [hN] at hm
  have hdecomp : N = m + a * 3^5 + 3^6 * (N / 729) := by
    norm_num at hm ⊢
    omega
  have hpair := pow4_shared_trit_pair 5 m a (N / 729) ha
  have hrow : digit3 (4^N) 6 = 2 ∧ digit3 (4^(N+1)) 6 = 2 := by
    rw [hdecomp]
    simpa using And.intro (hpair.1.trans h0) (hpair.2.trans h1)
  exact ⟨6, by norm_num, hrow.1, hrow.2⟩

/-- The genuinely new row-six residues proved on the `7359d...` relocation
lineage.  These are kept as a compact structural class rather than copying the
historical relocation/provider modules. -/
def RelocatedRowSixClass (r : Nat) : Prop :=
  r = 288 ∨ r = 289 ∨ r = 292 ∨ r = 301 ∨ r = 302 ∨ r = 303

/-- Direct production `CommonTwo` theorem for every salvaged row-six residue. -/
theorem commonTwo_of_relocated_row_six
    (K : Nat) (hres : RelocatedRowSixClass (K % 729)) :
    CommonTwo K := by
  unfold RelocatedRowSixClass at hres
  rcases hres with h | h | h | h | h | h
  · exact commonTwo_of_mod729_lifted_prefix K 45 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])
  · exact commonTwo_of_mod729_lifted_prefix K 46 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])
  · exact commonTwo_of_mod729_lifted_prefix K 49 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])
  · exact commonTwo_of_mod729_lifted_prefix K 58 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])
  · exact commonTwo_of_mod729_lifted_prefix K 59 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])
  · exact commonTwo_of_mod729_lifted_prefix K 60 1 (by norm_num)
      (by norm_num at h ⊢; exact h) (by norm_num [digit3]) (by norm_num [digit3])

/-- Every counterexample surviving all currently integrated unconditional
layers lies outside row two through row six and outside the divisible-by-three
branch.  This is the exact survivor invariant consumed by deeper affine/Ω
descent. -/
theorem noCommonTwo_survivor_constraints
    (K : Nat) (hK5 : 5 ≤ K) (hNo : ¬ CommonTwo K) :
    K % 3 ≠ 0 ∧
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 ∧
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25 ∧
    ¬ RowFourClass (K % 81) ∧
    ¬ RowFiveClass (K % 243) ∧
    ¬ RelocatedRowSixClass (K % 729) := by
  have h3 : K % 3 ≠ 0 := by
    intro h
    exact hNo (commonTwo_of_div_three K hK5 h)
  have h9 := noCommonTwo_excludes_mod9_five_six K hNo
  have h27 := noCommonTwo_excludes_mod27_row_three K hNo
  have h81 := noCommonTwo_excludes_mod81_row_four K hNo
  have h243 : ¬ RowFiveClass (K % 243) := by
    intro h
    exact hNo (commonTwo_of_mod243_row_five K h)
  have h729 : ¬ RelocatedRowSixClass (K % 729) := by
    intro h
    exact hNo (commonTwo_of_relocated_row_six K h)
  exact ⟨h3, h9.1, h9.2, h27.1, h27.2.1, h27.2.2.1,
    h27.2.2.2, h81, h243, h729⟩

#check commonTwo_of_div_three
#check commonTwo_of_mod243_row_five
#check commonTwo_of_mod729_lifted_prefix
#check commonTwo_of_relocated_row_six
#check noCommonTwo_survivor_constraints
#print axioms commonTwo_of_div_three
#print axioms commonTwo_of_mod243_row_five
#print axioms commonTwo_of_mod729_lifted_prefix
#print axioms commonTwo_of_relocated_row_six
#print axioms noCommonTwo_survivor_constraints

end GSTFourPowerDirectExistenceClosure
