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

/-- Elementary growth used to destroy an abstract all-SURVIVE path once it is
realized by one finite physical residue row. -/
theorem gpt56_self_lt_two_pow
    (M : Nat) (hM : 1 ≤ M) : M < 2^M := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h0 : M = 0
      · subst M
        decide
      · have hM1 : 1 ≤ M := by omega
        have hi : M < 2^M := ih hM1
        have hp : 0 < 2^M := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega

/-- The abstract I!=BIG1 all-SURVIVE branch cannot be realized by the literal
binary columns of one finite natural at one fixed ternary cut.  The low residue
deficit doubles at every SURVIVE step and therefore exceeds the finite modulus. -/
theorem gpt56_physical_binary_row_noBig1_impossible
    (R p : Nat)
    (hclear : GSTBig1ClearInfinitePathS
      (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r))
    (h0 : GSTPhysicalKernel.binaryColumnDigit R p 0 ≠ 0) : False := by
  let M := 3^p
  let x : Nat → Nat := fun r => (2^r * R) % M
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  have hM1 : 1 ≤ M := by omega
  have hxlt : ∀ r, x r < M := by
    intro r
    dsimp [x]
    exact Nat.mod_lt _ hMpos
  have hall := gst_big1_clear_infinite_edges_are_surviveS
    (fun r => GSTPhysicalKernel.binaryColumnCarry R p r)
    (fun r => GSTPhysicalKernel.binaryColumnDigit R p r)
    hclear h0
  have hcarry1 : ∀ r, (2 * x r) / M = 1 := by
    intro r
    have hr := (hall r).1
    simpa [GSTPhysicalKernel.binaryColumnCarry, x, M] using hr
  have hxstep : ∀ r, x (r+1) = (2 * x r) % M := by
    intro r
    dsimp [x]
    have hpow : 2^(r+1) * R = 2 * (2^r * R) := by
      rw [Nat.pow_succ]
      ring
    rw [hpow]
    simp [Nat.mul_mod]
  have hbalance : ∀ r, x (r+1) + M = 2 * x r := by
    intro r
    have hdiv := hcarry1 r
    have hmd := Nat.mod_add_div (2 * x r) M
    rw [hxstep r]
    rw [hdiv] at hmd
    omega
  have hdefstep : ∀ r, M - x (r+1) = 2 * (M - x r) := by
    intro r
    have hb := hbalance r
    have hr := hxlt r
    have hr1 := hxlt (r+1)
    omega
  have hdef : ∀ k, M - x k = 2^k * (M - x 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hdefstep k, ih, Nat.pow_succ]
        ring
  have hx0lt := hxlt 0
  have hdef0 : 1 ≤ M - x 0 := by omega
  have hpowle : 2^M ≤ M - x M := by
    rw [hdef M]
    have hmul := Nat.mul_le_mul_left (2^M) hdef0
    simpa using hmul
  have hdefle : M - x M ≤ M := Nat.sub_le _ _
  have hgrow : M < 2^M := gpt56_self_lt_two_pow M hM1
  omega

/-- Therefore every nonzero real physical binary row reaches BIG1 at a finite
binary column.  The no-BIG1 branch of the abstract controller is eliminated by
finite residue arithmetic, not by a cutoff assumption. -/
theorem gpt56_physical_binary_row_hits_big1
    (R p : Nat)
    (h0 : GSTPhysicalKernel.binaryColumnDigit R p 0 ≠ 0) :
    ∃ N, GSTPhysicalKernel.binaryColumnDigit R p N = 1 := by
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry R p r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit R p r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_physical_binary_row_is_infinite_bridge R p
  by_contra hnone
  have hno : ∀ j, d j ≠ 1 := by
    intro j hj
    apply hnone
    exact ⟨j, hj⟩
  have hclear : GSTBig1ClearInfinitePathS a d :=
    gst_infinite_bridge_to_big1_clearS a d hpath hno
  exact gpt56_physical_binary_row_noBig1_impossible R p
    (by simpa [a, d] using hclear)
    (by simpa [d] using h0)

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

/-- A child Happy gate therefore enters the finite BIG-N branch on its literal
physical binary row; the abstract I!=BIG1 branch has been surgically removed. -/
theorem gpt56_child_happy_gate_has_first_big1
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
    let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
    ∃ N, GSTFirstBig1AtS d N := by
  dsimp only
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hd0eq : d 0 = 2 := by
    dsimp [d, GSTPhysicalKernel.binaryColumnDigit]
    simpa [_root_.GSTSeededHappyS, _root_.gstDigitS] using hgate.1
  have hd0 : d 0 ≠ 0 := by omega
  have hex : ∃ N, d N = 1 := by
    simpa [d] using gpt56_physical_binary_row_hits_big1 T q
      (by simpa [d] using hd0)
  exact gst_exists_first_big1S d hex

/-- Quantitative first-BIG1 output of the handwritten physical row. -/
theorem gpt56_child_happy_gate_first_big1_quantitative
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
    let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
    ∃ N, GSTFirstBig1AtS d N ∧
      (1 ≤ N → gstBig1ProjectedPathCodeS a d N =
        5 * 6^(N-1) - 1) := by
  dsimp only
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_physical_binary_row_is_infinite_bridge T q
  obtain ⟨N, hfirst⟩ := gpt56_child_happy_gate_has_first_big1 T q hgate
  refine ⟨N, hfirst, ?_⟩
  intro hN
  have hd0eq : d 0 = 2 := by
    dsimp [d, GSTPhysicalKernel.binaryColumnDigit]
    simpa [_root_.GSTSeededHappyS, _root_.gstDigitS] using hgate.1
  have hd0 : d 0 ≠ 0 := by omega
  exact gst_first_big1_quantitative_prefixS a d hpath hd0 N hN hfirst

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
#check gpt56_physical_binary_row_noBig1_impossible
#check gpt56_physical_binary_row_hits_big1
#check gpt56_child_happy_gate_micro_dichotomy
#check gpt56_child_happy_gate_has_first_big1
#check gpt56_child_happy_gate_first_big1_quantitative
#check gpt56_last_gate_handwritten_boundary_dichotomy
#print axioms gpt56_handwritten_operator_on_navigation_child
#print axioms gpt56_physical_binary_row_is_infinite_bridge
#print axioms gpt56_physical_binary_row_noBig1_impossible
#print axioms gpt56_physical_binary_row_hits_big1
#print axioms gpt56_child_happy_gate_has_first_big1
#print axioms gpt56_child_happy_gate_first_big1_quantitative
#print axioms gpt56_last_gate_handwritten_boundary_dichotomy
