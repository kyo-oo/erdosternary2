import GSTFourPowerDirectResidue
import GSTFourPowerDirectResidue27
import GSTFourPowerDirectResidue81
import GSTFourPowerExponentTritObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectExistence

open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue27
open GSTFourPowerDirectResidue81
open GSTFourPowerExponentTritObstruction

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

/-- The exact row-three classifier supplies a direct common-two witness in four
additional exponent classes modulo 27. -/
theorem commonTwo_of_mod27_row_three
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    CommonTwo K := by
  refine ⟨3, by norm_num, ?_⟩
  exact row_three_overlap_of_mod27_classes K hres

/-- Consequently, a hypothetical direct counterexample avoids every exact
row-three overlap class modulo 27. -/
theorem noCommonTwo_excludes_mod27_row_three
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25 := by
  exact no_common_two_forbids_mod27_classes K hNo

/-- Row four contributes fourteen exact common-two classes modulo 81. -/
theorem commonTwo_of_mod81_row_four
    (K : Nat) (hres : RowFourClass (K % 81)) :
    CommonTwo K := by
  refine ⟨4, by norm_num, ?_⟩
  exact row_four_overlap_of_mod81_classes K hres

/-- Hence a hypothetical counterexample avoids every exact row-four class. -/
theorem noCommonTwo_excludes_mod81_row_four
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ¬ RowFourClass (K % 81) := by
  exact no_common_two_forbids_mod81_classes K hNo

/-- Parametric direct constructor from the exponent-prefix law.  At any scale
`p`, if the consecutive low-prefix powers agree at row `p+1` and the actual
`p`-th ternary exponent trit is the unique killing trit, then the current
exponent itself has a common-two row.  The witness is explicitly `p+1`; no
finite residue table or navigation route is used. -/
theorem commonTwo_of_prefix_killing_trit
    (K p : Nat)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1))
    (hkill :
      exponentTrit K p =
        2 - digit3 (4^(exponentPrefix K p)) (p+1)) :
    CommonTwo K := by
  refine ⟨p+1, by omega, ?_⟩
  exact (row_common_two_iff_prefix_killing_trit K p).2 ⟨heq, hkill⟩

/-- Any number strictly below the ternary scale `3^p` has zero digit at row
`p`.  This tiny arithmetic lemma lets the prefix-killing construction become
automatic once both low-prefix powers lie below the target row. -/
theorem digit3_eq_zero_of_lt_row
    (R p : Nat) (hR : R < 3^p) :
    digit3 R p = 0 := by
  unfold digit3
  simp [Nat.div_eq_of_lt hR]

/-- Parametric non-table success sector.  If the `p`-th exponent trit is `2`
and the next low-prefix power is still strictly below row `p+1`, then both
low-prefix row digits are zero.  Thus trit `2` is exactly the killing trit and
`p+1` is a direct common-two row for `4^K,4^(K+1)`.

This is a genuine scale-dependent constructor rather than another fixed
`mod 3^n` classification. -/
theorem commonTwo_of_leading_two_small_prefix
    (K p : Nat)
    (htrit : exponentTrit K p = 2)
    (hsmall : 4^((exponentPrefix K p)+1) < 3^(p+1)) :
    CommonTwo K := by
  have hpref_lt : 4^(exponentPrefix K p) < 3^(p+1) := by
    have hs := hsmall
    rw [Nat.pow_succ] at hs
    have hpos : 0 < 4^(exponentPrefix K p) := by positivity
    omega
  have hd0 :
      digit3 (4^(exponentPrefix K p)) (p+1) = 0 :=
    digit3_eq_zero_of_lt_row _ _ hpref_lt
  have hd1 :
      digit3 (4^((exponentPrefix K p)+1)) (p+1) = 0 :=
    digit3_eq_zero_of_lt_row _ _ hsmall
  apply commonTwo_of_prefix_killing_trit K p
  · exact hd0.trans hd1.symm
  · simpa [hd0] using htrit

/-- For every nonzero ternary scale, the fixed low-prefix successor `4^1 = 4`
lies strictly below row `p+1`.  This removes the remaining size hypothesis in
the zero-prefix branch of the parametric constructor. -/
theorem four_lt_three_pow_succ
    (p : Nat) (hp : 1 ≤ p) :
    4 < 3^(p+1) := by
  induction p with
  | zero => omega
  | succ p ih =>
      by_cases h0 : p = 0
      · subst p
        norm_num
      · have hp' : 1 ≤ p := by omega
        have hprev : 4 < 3^(p+1) := ih hp'
        have hstep : 3^(p+1) ≤ 3^(p+1) * 3 := by omega
        calc
          4 < 3^(p+1) := hprev
          _ ≤ 3^(p+1) * 3 := hstep
          _ = 3^((p+1)+1) := (Nat.pow_succ 3 (p+1)).symm
          _ = 3^(Nat.succ p + 1) := by congr 1 <;> omega

/-- Infinite parametric success family.  If the low `p` exponent trits are all
zero and the next exponent trit is `2`, then row `p+1` is automatically a
common-two row.  Unlike a fixed residue table, `p` is arbitrary: the condition
selects the entire family `K ≡ 2*3^p (mod 3^(p+1))` for every `p ≥ 1`. -/
theorem commonTwo_of_zero_prefix_two_trit
    (K p : Nat) (hp : 1 ≤ p)
    (hpref : exponentPrefix K p = 0)
    (htrit : exponentTrit K p = 2) :
    CommonTwo K := by
  apply commonTwo_of_leading_two_small_prefix K p htrit
  simpa [hpref] using four_lt_three_pow_succ p hp

/-- Starting at ternary scale two, the fixed low-prefix successor `4^(1+1)=16`
lies below row `p+1`.  This is the size input for the next parametric success
sector after the zero-prefix family. -/
theorem sixteen_lt_three_pow_succ
    (p : Nat) (hp : 2 ≤ p) :
    16 < 3^(p+1) := by
  induction p with
  | zero => omega
  | succ p ih =>
      by_cases h1 : p = 1
      · subst p
        norm_num
      · have hp' : 2 ≤ p := by omega
        have hprev : 16 < 3^(p+1) := ih hp'
        have hstep : 3^(p+1) ≤ 3^(p+1) * 3 := by omega
        calc
          16 < 3^(p+1) := hprev
          _ ≤ 3^(p+1) * 3 := hstep
          _ = 3^((p+1)+1) := (Nat.pow_succ 3 (p+1)).symm
          _ = 3^(Nat.succ p + 1) := by congr 1 <;> omega

/-- Second infinite parametric success family.  If the low `p` exponent prefix
is exactly one and the `p`-th exponent trit is `2`, then for every `p ≥ 2` the
next low-prefix power is only `16`, hence both prefix digits vanish at row
`p+1`.  The direct common-two witness is again the actual row `q = p+1`.
Equivalently this covers `K ≡ 1 + 2*3^p (mod 3^(p+1))` uniformly in `p`. -/
theorem commonTwo_of_one_prefix_two_trit
    (K p : Nat) (hp : 2 ≤ p)
    (hpref : exponentPrefix K p = 1)
    (htrit : exponentTrit K p = 2) :
    CommonTwo K := by
  apply commonTwo_of_leading_two_small_prefix K p htrit
  simpa [hpref] using sixteen_lt_three_pow_succ p hp

/-- Every hypothetical direct counterexample obeys the parametric exponent-trit
obstruction at every scale.  If the two low-prefix values agree at row `p+1`,
the actual `p`-th ternary trit of `K` cannot equal the canonical killing trit.

This is the recursive direct proof law: it constrains the ternary expansion of
`K` itself and contains no source-witness transport. -/
theorem noCommonTwo_exponent_trit_law
    (K p : Nat) (hNo : ¬ CommonTwo K)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - digit3 (4^(exponentPrefix K p)) (p+1) := by
  exact no_common_two_exponent_trit_obstruction K p hNo heq

/-- Bundled form: a hypothetical counterexample carries the trit obstruction
uniformly at every ternary scale. -/
theorem noCommonTwo_all_exponent_trit_laws
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1) := by
  intro p heq
  exact noCommonTwo_exponent_trit_law K p hNo heq

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
#check commonTwo_of_mod27_row_three
#check noCommonTwo_excludes_mod27_row_three
#check commonTwo_of_mod81_row_four
#check noCommonTwo_excludes_mod81_row_four
#check commonTwo_of_prefix_killing_trit
#check digit3_eq_zero_of_lt_row
#check commonTwo_of_leading_two_small_prefix
#check four_lt_three_pow_succ
#check commonTwo_of_zero_prefix_two_trit
#check sixteen_lt_three_pow_succ
#check commonTwo_of_one_prefix_two_trit
#check noCommonTwo_exponent_trit_law
#check noCommonTwo_all_exponent_trit_laws
#check directExistence_implies_source_two
#print axioms commonTwo_has_source_two
#print axioms commonTwo_has_target_two
#print axioms commonTwo_of_mod9_five_or_six
#print axioms noCommonTwo_excludes_mod9_five_six
#print axioms commonTwo_of_mod27_row_three
#print axioms noCommonTwo_excludes_mod27_row_three
#print axioms commonTwo_of_mod81_row_four
#print axioms noCommonTwo_excludes_mod81_row_four
#print axioms commonTwo_of_prefix_killing_trit
#print axioms digit3_eq_zero_of_lt_row
#print axioms commonTwo_of_leading_two_small_prefix
#print axioms four_lt_three_pow_succ
#print axioms commonTwo_of_zero_prefix_two_trit
#print axioms sixteen_lt_three_pow_succ
#print axioms commonTwo_of_one_prefix_two_trit
#print axioms noCommonTwo_exponent_trit_law
#print axioms noCommonTwo_all_exponent_trit_laws
#print axioms directExistence_implies_source_two

end GSTFourPowerDirectExistence