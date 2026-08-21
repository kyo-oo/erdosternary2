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

/-- Every literal physical binary row R,2R,4R,... at a fixed ternary cut p
realizes the exact all-Nat handwritten x2/base3 bridge. -/
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

/-- Every actual child Happy gate is physically exactly one of the two
handwritten microscopic patterns: DESTROY/CREATE=(4,2), or the right-chord
SURVIVE/SURVIVE=(5,5). -/
theorem gpt56_child_happy_gate_micro_dichotomy
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    gstPhysicalMicroPairS T q = (4,2) ∨
      gstPhysicalMicroPairS T q = (5,5) := by
  apply (gst_physical_micro_pair_happy_iffS T q).1
  simpa [_root_.gstCarryS, _root_.gstAffineMulCarryS] using hgate

/-- A real child Happy gate places the literal binary-column realization of
that child into the exhaustive handwritten BIG-N / I!=BIG1 controller. -/
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
operator.  No terminal-NULL assumption occurs. -/
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
  rcases htrap with ⟨hparentBad, hchildBad, hC, hshared, hW⟩
  refine ⟨hparentBad, hchildBad, hC, hshared, hW, ?_⟩
  let C := gstAffineMulCarryS 4 0 T (q+1)
  let Y := T / 3^(q+1)
  by_cases hbig1 : ∃ j, GSTInfiniteV2.gstDigitS Y j = 1
  · exact Or.inl hbig1
  · have hno : GSTSleepNoBig1S Y := by
      intro j hj
      exact hbig1 ⟨j, hj⟩
    have hbadSleep : GSTSleepSeededBadTraceS C Y := by
      intro j
      change ¬ (GSTInfiniteV2.gstDigitS Y j = 2 ∧
        (GSTInfiniteV2.gstAffineCarryS C Y j = 0 ∨
         GSTInfiniteV2.gstAffineCarryS C Y j = 3))
      intro hhappy
      have hj := hchildBad j
      apply hj
      constructor
      · simpa [_root_.gstDigitS, GSTInfiniteV2.gstDigitS, Y] using hhappy.1
      · rcases hhappy.2 with h0 | h3
        · left
          simpa [_root_.gstAffineMulCarryS, GSTInfiniteV2.gstAffineCarryS, C, Y] using h0
        · right
          simpa [_root_.gstAffineMulCarryS, GSTInfiniteV2.gstAffineCarryS, C, Y] using h3
    have hb := gst_sleep_big1_free_last_gate_peel_is_ternary_boundaryS
      C Y hC hbadSleep hno
    rcases hb with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inr (Or.inl ⟨r, by simpa [C, Y] using hr⟩)
    · exact Or.inr (Or.inr ⟨r, by simpa [C, Y] using hr⟩)

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
