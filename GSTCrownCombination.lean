import GSTUnifiedCrown
import GSTUnconditionalCoverage
import GSTShadowPerfectTree
import GSTShadowSeparationAttack
import GSTShadowGapReceipt
import GSTHypothesisToTheorem
import GSTStep6Close
import GSTGraphV2SixAdicUnitIsometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# THE CROWN COMBINATION — the total supply chain and the one-battle theorem

The campaign's combination order: take every theorem the supply chain has
ever produced, read them together, and weld them into one new theorem.
This module is that weld.

* **THE INTERCHANGES** (`residual_firing_iff_no_eternal_shadow`,
  `deep_firing_iff_no_eternal_shadow`): the residual-firing families and
  the death of the eternal shadow are one object in both directions —
  the level-five residual, the level-six deep residual, and the
  separation are interchangeable named forms of the same remaining
  content.  The forward directions are the campaign's separation
  suppliers; the reverse directions are new here, from the observation
  that every combined-residual exponent is above five, so the bare
  separation already fires it.

* **THE NEW DOORS** (`crown_of_residual_firing`, `crown_of_deep_firing`,
  `crown_of_clean_word`): three doors the ten-route unified crown did
  not carry — the combined-residual firing, the deep-residual firing,
  and the clean-word equation (re-exported from the separation attack so
  the grand disjunction below is self-contained).

* **THE ONE BATTLE** (`the_one_battle`): the comparator statement, the
  death of the eternal shadow, the level-five residual firing, the
  level-six deep-residual firing, and the clean-word equation — five
  named forms, all machine-checked equivalent, in one statement.

* **THE TOTAL DISJUNCTION** (`crown_of_any_door`): any ONE of the
  thirteen named objects — the ten unified-crown routes plus the three
  new doors — delivers the full unconditional Erdős ternary-2 theorem.

* **THE SUPPLY-CHAIN COMPLETION**: this module is the first in the
  campaign's history whose import closure contains every lakefile root —
  including `GSTStep6Close` and `GSTGraphV2SixAdicUnitIsometry`, the two
  modules no CI step had ever built.  Building this file builds the
  entire war at once.
-/

namespace GSTCrownCombination

open GSTShadowGap
open GSTShadowGapReceipt
open GSTShadowSeparationAttack
open GSTFourPowerDirectResidue

/-! ## Section 1 — the interchanges -/

/-- An exponent that is not eternally shadowed owns a ternary digit two,
in the raw window form the residual statements use. -/
theorem exists_digit_two_of_not_eternally_shadowed (K : Nat)
    (h : ¬ EternallyShadowed K) :
    ∃ p : Nat, (4^K)/3^p % 3 = 2 := by
  rw [eternally_shadowed_iff_no_digit_two] at h
  by_contra hclean
  exact h (fun p heq => hclean ⟨p, heq⟩)

/-- **THE RESIDUAL INTERCHANGE.**  The level-five combined-residual
firing and the death of the eternal shadow are one object: each implies
the other.  The forward direction is the separation supplier; the
reverse is new — every combined-residual exponent is above five, so the
bare separation already fires it. -/
theorem residual_firing_iff_no_eternal_shadow :
    (∀ K : Nat, GSTUnconditionalCoverage.CombinedResidual K →
      ∃ p : Nat, (4^K)/3^p % 3 = 2) ↔
    (∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) :=
  ⟨GSTUnconditionalCoverage.separation_of_residual_firing,
   fun h K hK =>
     exists_digit_two_of_not_eternally_shadowed K
       (h K (by obtain ⟨h500, _, _⟩ := hK; omega))⟩

/-- **THE DEEP-RESIDUAL INTERCHANGE.**  The level-six deep-residual
firing and the death of the eternal shadow are one object, in both
directions. -/
theorem deep_firing_iff_no_eternal_shadow :
    (∀ K : Nat, GSTShadowPerfectTree.CombinedResidualDeep K →
      ∃ p : Nat, (4^K)/3^p % 3 = 2) ↔
    (∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) :=
  ⟨GSTShadowPerfectTree.separation_of_deep_firing,
   fun h K hK =>
     exists_digit_two_of_not_eternally_shadowed K
       (h K (by obtain ⟨h500, _, _⟩ := hK; omega))⟩

/-! ## Section 2 — the new doors -/

/-- **DOOR ELEVEN — the residual firing.**  If every level-five
combined-residual exponent owns a ternary digit two, the full
unconditional theorem follows. -/
theorem crown_of_residual_firing
    (h : ∀ K : Nat, GSTUnconditionalCoverage.CombinedResidual K →
      ∃ p : Nat, (4^K)/3^p % 3 = 2) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTUnconditionalCoverage.erdos_ternary_2_iff_combined_residual.mpr h

/-- **DOOR TWELVE — the deep-residual firing.**  If every level-six
deep-residual exponent owns a ternary digit two, the full unconditional
theorem follows. -/
theorem crown_of_deep_firing
    (h : ∀ K : Nat, GSTShadowPerfectTree.CombinedResidualDeep K →
      ∃ p : Nat, (4^K)/3^p % 3 = 2) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTShadowPerfectTree.erdos_ternary_2_iff_combined_residual_deep.mpr h

/-- **DOOR THIRTEEN — the clean-word equation.**  If every exponent
from five on owns a dirty row in its quotient word `z = (4^m − 1)/3`,
the full unconditional theorem follows.  The equation is the separation
attack's own route, re-exported so the total disjunction is
self-contained. -/
theorem crown_of_clean_word
    (h : ∀ m : Nat, 5 ≤ m → ∃ q : Nat, digit3 (cleanQuot m) q = 2) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTShadowSeparationAttack.crown_of_clean_word_equation h

/-! ## Section 3 — the one battle -/

/-- **THE ONE BATTLE.**  Five named forms of the entire remaining
content, machine-checked equivalent in one statement: the comparator
statement itself, the death of the eternal shadow, the level-five
residual firing, the level-six deep-residual firing, and the clean-word
equation.  They are not five battles; they are one battle with five
names. -/
theorem the_one_battle :
    ((∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ↔
      (∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m)) ∧
    ((∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) ↔
      (∀ K : Nat, GSTUnconditionalCoverage.CombinedResidual K →
        ∃ p : Nat, (4^K)/3^p % 3 = 2)) ∧
    ((∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) ↔
      (∀ K : Nat, GSTShadowPerfectTree.CombinedResidualDeep K →
        ∃ p : Nat, (4^K)/3^p % 3 = 2)) ∧
    ((∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) ↔
      (∀ m : Nat, 5 ≤ m → ∃ q : Nat, digit3 (cleanQuot m) q = 2)) :=
  ⟨THE_REMAINING_CONTENT, residual_firing_iff_no_eternal_shadow.symm,
    deep_firing_iff_no_eternal_shadow.symm,
    separation_iff_clean_word_equation⟩

/-! ## Section 4 — the total disjunction -/

/-- **THE TOTAL DISJUNCTION.**  Any ONE of the thirteen named objects —
the creation master, the climb tail, the third-wave descent, the mirror
bridge, the worldtrace-Mahler theory, the death of the Cantorian, the
empty dust, the shadow tailF, the feedback escape, the separation, the
residual firing, the deep-residual firing, or the clean-word equation —
delivers the full unconditional Erdős ternary-2 theorem.  One battle,
thirteen doors. -/
theorem crown_of_any_door
    (h : GSTFourPowerOntologicalAdapter.FourPowerCreationMaster
      ∨ GSTFourPowerHappyBaseCamp.four_power_happy_climb_tail
      ∨ GSTFourPowerThirdWaveMultiscaleBridge.ThirdWaveNoCommonDescent
      ∨ Nonempty GSTCardinalWorldsBridge.CardinalWorldsMirrorBridge
      ∨ GSTWorldtraceMahler.WorldtraceMahlerTheory
      ∨ (¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K)
      ∨ (∀ K : Nat, 8 ≤ K → ¬ GSTDiagonalRead.WindowCleanDust K)
      ∨ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
      ∨ (∀ K : Nat, 8 ≤ K → ∃ j : Nat,
          (GSTCanonicalSevenAxisBridge.digit3 (4^(K % 3^j)) (j + 1)
            + GSTCanonicalSevenAxisBridge.digit3 K j) % 3 = 2)
      ∨ (∀ m : Nat, 5 ≤ m → ¬ GSTShadowGapReceipt.EternallyShadowed m)
      ∨ (∀ K : Nat, GSTUnconditionalCoverage.CombinedResidual K →
          ∃ p : Nat, (4^K)/3^p % 3 = 2)
      ∨ (∀ K : Nat, GSTShadowPerfectTree.CombinedResidualDeep K →
          ∃ p : Nat, (4^K)/3^p % 3 = 2)
      ∨ (∀ m : Nat, 5 ≤ m → ∃ q : Nat, digit3 (cleanQuot m) q = 2)) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact GSTUnifiedCrown.crown_of_creation_master h
  · exact GSTUnifiedCrown.crown_of_climb_tail h
  · exact GSTUnifiedCrown.crown_of_third_wave_no_common_descent h
  · obtain ⟨hM⟩ := h
    exact GSTUnifiedCrown.crown_of_mirror_bridge hM
  · exact GSTUnifiedCrown.crown_of_worldtrace_mahler h
  · exact GSTUnifiedCrown.crown_of_no_cantorian h
  · exact GSTUnifiedCrown.crown_of_dust_empty h
  · exact GSTUnifiedCrown.crown_of_shadow_tailF h
  · exact GSTUnifiedCrown.crown_of_feedback h
  · exact GSTUnifiedCrown.crown_of_separation h
  · exact crown_of_residual_firing h
  · exact crown_of_deep_firing h
  · exact crown_of_clean_word h

/-! ## Section 5 — the supply-chain completion receipts

`GSTStep6Close` and `GSTGraphV2SixAdicUnitIsometry` are the two lakefile
roots no CI step had ever built.  Their first kernel verification
happens in this module's own build; the receipts below are its witness. -/

#check GSTStep6Close.gst_step6_collision_from_packets
#check GSTStep6Close.gst_step6_close_v2_selftest
#check GSTStep6Close.gst_step6_close_selftest
#print axioms GSTStep6Close.gst_step6_collision_from_packets
#print axioms GSTStep6Close.gst_step6_close_v2_selftest
#print axioms GSTStep6Close.gst_step6_close_selftest

#check GSTGraphV2SixAdicUnitIsometry.six_iso_translate_iff
#check GSTGraphV2SixAdicUnitIsometry.six_iso_mul_reflect_of_mod_inverse
#check GSTGraphV2SixAdicUnitIsometry.six_iso_mul_iff_of_mod_inverse
#check GSTGraphV2SixAdicUnitIsometry.six_scale_exact_iff
#print axioms GSTGraphV2SixAdicUnitIsometry.six_iso_translate_iff
#print axioms GSTGraphV2SixAdicUnitIsometry.six_iso_mul_reflect_of_mod_inverse
#print axioms GSTGraphV2SixAdicUnitIsometry.six_iso_mul_iff_of_mod_inverse
#print axioms GSTGraphV2SixAdicUnitIsometry.six_scale_exact_iff

/-! ## Section 6 — receipts for the new theorems -/

#print axioms exists_digit_two_of_not_eternally_shadowed
#print axioms residual_firing_iff_no_eternal_shadow
#print axioms deep_firing_iff_no_eternal_shadow
#print axioms crown_of_residual_firing
#print axioms crown_of_deep_firing
#print axioms crown_of_clean_word
#print axioms the_one_battle
#print axioms crown_of_any_door

end GSTCrownCombination
