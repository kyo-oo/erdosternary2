import ErdosPreOmega
import GSTGraphV2SleepEquationLabScratch
import GSTGraphV2SleepEquationCollisionScratch
import GSTGraphV2InfiniteBigNDichotomyScratch
import GSTGraphV2SleepBadLanguageDescentScratch
import CanonicalTrapScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Handwritten equation -> live prefix-one production probe

Literal page, as recovered by the Aug-20 transcription:

  Π_{t→∞}^{n≠0} { ∫_{∞}^{-∞} (lim_{j→∞} e^x) }
    2^j ∪ 3^j ∪ 6^j - f_m ∪ Σ_{S≠0}^{S≠3^x} S n^x

The source semantics used here are the repository's own handwritten ones:
Π = all-scale natural-origin constructor, Ω reverse transfer = exact Future/Past
transport, 2^j/3^j/6^j = binary/ternary/mixed worlds, and S*n^x = the signed
physical-space moment.  We do not assign a new meaning to the unresolved f_m
glyph.
-/

theorem gpt56_handwritten_operator_on_navigation_child
    (s n : Nat) (hs : 1 ≤ s) :
    GSTSleepFullOperatorS
      (s+1) n (gstNavigationConstant (s+1) n) := by
  apply gst_sleep_full_operatorS
  unfold GSTSleepNavigationEnergyCouplingS
  unfold gstOmegaPressureEnergyS gstOriginRemainingUS
  exact (gst_navigation_decomposition (s+1) n (by omega)).symm

/-- Exact post-last-gate classification supplied by the handwritten S/U
operator.  Nothing is declared terminal.  If BIG1 is absent from the retained
child suffix then the conserved high endpoint C+4Y is forced onto one of the
two exact ternary boundary families. -/
theorem gpt56_last_gate_handwritten_boundary_dichotomy
    (A z T : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hparent : GSTSeededBadTraceS 1 (z + A*T))
    (hchild : ∃ j, GSTSeededHappyS 0 T j) :
    ∃ q,
      let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
      let Z := gstAffineMulCarryS A z T (q+1)
      let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
      let C := gstAffineMulCarryS 4 0 T (q+1)
      let Y := T / 3^(q+1)
      GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      D + 4*Z = W + A*C ∧
      W < A ∧
      ((∃ j, GSTInfiniteV2.gstDigitS Y j = 1) ∨
       (∃ r, C + 4*Y = 3^(2*r) + 1) ∨
       (∃ r, C + 4*Y = 3^(2*r+1))) := by
  obtain ⟨q, htrap⟩ :=
    gst_canonical_two_boundary_trapS A z T hA hz1 hparent hchild
  refine ⟨q, ?_⟩
  dsimp only at htrap ⊢
  refine ⟨htrap.1, htrap.2.1, htrap.2.2.1,
    htrap.2.2.2.1, htrap.2.2.2.2, ?_⟩
  by_cases hbig1 : ∃ j, GSTInfiniteV2.gstDigitS (T / 3^(q+1)) j = 1
  · exact Or.inl hbig1
  · have hno : GSTSleepNoBig1S (T / 3^(q+1)) := by
      intro j hj
      exact hbig1 ⟨j, hj⟩
    have hbadSleep :
        GSTSleepSeededBadTraceS
          (gstAffineMulCarryS 4 0 T (q+1)) (T / 3^(q+1)) := by
      intro j
      have hj := htrap.2.1 j
      simpa only [_root_.GSTBadPairS, GSTInfiniteV2.GSTBadPairS,
        _root_.gstAffineMulCarryS, GSTInfiniteV2.gstAffineCarryS,
        _root_.gstDigitS, GSTInfiniteV2.gstDigitS] using hj
    have hb := gst_sleep_big1_free_last_gate_peel_is_ternary_boundaryS
      (gstAffineMulCarryS 4 0 T (q+1)) (T / 3^(q+1))
      htrap.2.2.1 hbadSleep hno
    rcases hb with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inr (Or.inl ⟨r, hr⟩)
    · exact Or.inr (Or.inr ⟨r, hr⟩)

#check gpt56_handwritten_operator_on_navigation_child
#check gpt56_last_gate_handwritten_boundary_dichotomy
#print axioms gpt56_handwritten_operator_on_navigation_child
#print axioms gpt56_last_gate_handwritten_boundary_dichotomy
