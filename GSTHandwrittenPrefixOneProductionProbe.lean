import ErdosPreOmega
import GSTGraphV2SleepEquationLabScratch
import GSTGraphV2SleepEquationCollisionScratch
import GSTGraphV2InfiniteBigNDichotomyScratch
import GSTGraphV2SleepBadLanguageDescentScratch
import GSTGraphV2PhysicalSignedKernelTelescopeScratch
import PhysicalSixBridgeGateScratch
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

/-- The handwritten infinite x2/base3 bridge is not abstract: every literal
physical binary row R,2R,4R,... at a fixed ternary position p realizes the
exact `GSTInfiniteBridgePathS` interface. -/
theorem gpt56_physical_binary_row_is_infinite_bridge
    (R p : Nat) :
    GSTInfiniteBridgePathS
      (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact GSTPhysicalKernel.binaryColumnCarry_lt_two R p r
  · intro r
    exact GSTPhysicalKernel.binaryColumnDigit_lt_three R p r
  · intro r
    simpa [GSTInfiniteV2.gstBinaryBridgeOutputS,
      GSTPhysicalKernel.microOutput] using
      GSTPhysicalKernel.microOutput_eq_next_binaryColumnDigit R p r

/-- Every actual child Happy gate is physically one of exactly the two
handwritten microscopic patterns: NULL DESTROY/CREATE=(4,2), or the right
chord GST+ SURVIVE/SURVIVE=(5,5). -/
theorem gpt56_child_happy_gate_micro_dichotomy
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    gstPhysicalMicroPairS T q = (4,2) ∨
      gstPhysicalMicroPairS T q = (5,5) := by
  apply (gst_physical_micro_pair_happy_iffS T q).1
  simpa [_root_.gstCarryS, _root_.gstAffineMulCarryS] using hgate

/-- A real child Happy gate places the literal binary-column realization of
that child into the exhaustive handwritten BIG-N / I!=BIG1 controller.  This
is the physical, not abstract, instantiation of the 2^j/3^j/6^j sector. -/
theorem gpt56_child_happy_gate_physical_two_case_quantitative
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
    let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
    (∃ N, GSTFirstBig1AtS d N ∧
        (1 ≤ N → gstBig1ProjectedPathCodeS a d N =
          5 * 6^(N-1) - 1)) ∨
      (GSTBig1ClearInfinitePathS a d ∧
        ∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1) := by
  dsimp only
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_physical_binary_row_is_infinite_bridge T q
  have hd0eq : d 0 = 2 := by
    dsimp [d, GSTPhysicalKernel.binaryColumnDigit]
    simpa [_root_.GSTSeededHappyS, _root_.gstDigitS] using hgate.1
  have hd0 : d 0 ≠ 0 := by omega
  exact gst_infinite_two_case_quantitativeS a d hpath hd0

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
#check gpt56_physical_binary_row_is_infinite_bridge
#check gpt56_child_happy_gate_micro_dichotomy
#check gpt56_child_happy_gate_physical_two_case_quantitative
#check gpt56_last_gate_handwritten_boundary_dichotomy
#print axioms gpt56_handwritten_operator_on_navigation_child
#print axioms gpt56_physical_binary_row_is_infinite_bridge
#print axioms gpt56_child_happy_gate_micro_dichotomy
#print axioms gpt56_child_happy_gate_physical_two_case_quantitative
#print axioms gpt56_last_gate_handwritten_boundary_dichotomy
