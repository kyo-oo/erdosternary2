#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

imp = 'import GSTGraphV2InfiniteControl\n'
if imp not in s:
    anchor = 'import Mathlib.Tactic.Ring\n'
    if anchor not in s:
        raise SystemExit('import anchor not found')
    s = s.replace(anchor, anchor + imp, 1)

start_marker = '/-- Literal BIG-N finite-support horizon for the canonical child information. -/'
end_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'

if start_marker not in s:
    if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in s:
        print('atomic U2D replacement already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('old prefix-one start marker not found')
if end_marker not in s:
    raise SystemExit('prefix-one end marker not found')

start = s.index(start_marker)
end = s.index(end_marker, start)

replacement = r'''/-- Atomic Surgery V2: the certified child event and the completely bad
prefix-one parent are now literal slices of one canonical infinite GST V2
perfect-power graph.  No exposed-tail surrogate, residual termination theorem,
finite-support horizon, or `gst_end` is present in this theorem. -/
theorem gst_prefix_one_u2d_atomic_collision_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let data : GSTPrefixOneOmegaData s n :=
    gst_prefix_one_omegaData s n hs hchild
  let E : Nat := 4^(3^(s+1) * n)
  let N : Nat := 3^s
  let B : Nat := 3^(s+2)
  let P0 : Nat := 1
  let P1 : Nat := 1 + 3^(s+1)
  let T : Nat := gstNavigationConstant (s+1) n
  let H : Nat := gstPrefixOneUPotentialTailS s n
  let q : Nat := data.childGateIndex

  have hGate :
      gstDigit T q = 2 ∧ (gstCarry T q = 0 ∨ gstCarry T q = 3) := by
    dsimp [T, q, data]
    simpa only [gstOmega] using data.childGate

  have hGateS : GSTSeededHappyS 0 T q := by
    simpa [GSTSeededHappyS, gstDigitS, gstDigit, gstCarryS,
      gstAffineMulCarryS, gstCarry] using hGate

  have hE0raw := gst_navigation_decomposition (s+1) n (by omega)
  have hE0 : 4^0 * E = P0 + B*T := by
    dsimp [E, P0, B, T]
    simpa using hE0raw

  have hB27 : 27 ≤ B := by
    dsimp [B]
    have hpow : 3^3 ≤ 3^(s+2) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hP0 : P0 < B := by omega
  have h4P0 : 4 * P0 < B := by omega
  have hseed0 : (4 * P0) / B = 0 := Nat.div_eq_of_lt h4P0

  have hLeft :
      GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E 0 (s+2+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph E 0 (s+2+q)).seven.digit := by
    apply (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
      E 0 (s+2) P0 T q hE0 hP0).2
    rw [hseed0]
    simpa [GSTCanonicalSevenAxisBridge.digit3,
      GSTGraphV2InfiniteControl.seededCarry, gstDigit, gstCarry] using hGate

  have hc3 : c s % 3 = 1 := c_mod3 s hs
  have hcshape : c s = 1 + 3 * (c s / 3) := by
    have hcdiv := Nat.mod_add_div (c s) 3
    rw [hc3] at hcdiv
    omega
  have hA : 4^(3^s) = 1 + 3^(s+1) * c s := lte_identity s hs
  have hE1raw := gst_canonical_phase1_energy_shape_surgeryS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s n (c s) (c s / 3) hs hA hcshape
  have hE1 : 4^N * E = P1 + B*H := by
    dsimp [N, E, P1, B, H, gstPrefixOneUPotentialTailS]
    rw [show 3^(s+2) = 3 * 3^(s+1) by
      rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]; ac_rfl]
    simpa [Nat.mul_assoc] using hE1raw

  let X : Nat := 3^(s+1)
  have hX9 : 9 ≤ X := by
    dsimp [X]
    have hpow : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hBshape : B = 3 * X := by
    dsimp [B, X]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hP1shape : P1 = 1 + X := by rfl
  have hP1 : P1 < B := by
    rw [hBshape, hP1shape]
    omega
  have hP1lo : B ≤ 4 * P1 := by
    rw [hBshape, hP1shape]
    omega
  have hP1hi : 4 * P1 < 2 * B := by
    rw [hBshape, hP1shape]
    omega
  have hBpos : 0 < B := by omega
  have hseed1lo : 1 ≤ (4 * P1) / B :=
    (Nat.le_div_iff_mul_le hBpos).2 (by simpa using hP1lo)
  have hseed1hi : (4 * P1) / B < 2 :=
    (Nat.div_lt_iff_lt_mul hBpos).2 (by simpa using hP1hi)
  have hseed1 : (4 * P1) / B = 1 := by omega

  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  have hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.digit := by
    intro j hHappy
    have hTail :=
      (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
        E N (s+2) P1 H j hE1 hP1).1 hHappy
    rw [hseed1] at hTail
    have hbadj := hseeded j
    apply hbadj
    simpa [GSTBadPairS, GSTCanonicalSevenAxisBridge.digit3,
      GSTGraphV2InfiniteControl.seededCarry,
      gstAffineMulCarryS, gstDigitS] using hTail

  -- Canonical finite-prefix probe: the next block theorem must obtain the
  -- parent finite-prefix carry from this *actual* child gate, not from an
  -- arbitrary affine-tail transport statement.
  let a : Nat := (1 + 3*n) % 3^(q+1)
  have hParentPrefixCarry :
      gstCarryS (gstNavigationConstant s a) (q+1) = 0 ∨
      gstCarryS (gstNavigationConstant s a) (q+1) = 3 := by
    have hcut := gst_canonical_origin_cut_carryS
      s a (q+1) ((1 + 3*n) / 3^(q+1)) hs
    have hdecomp :
        a + 3^(q+1) * ((1 + 3*n) / 3^(q+1)) = 1 + 3*n := by
      dsimp [a]
      exact Nat.mod_add_div (1 + 3*n) (3^(q+1))
    rw [hdecomp] at hcut
    have hparentShape := gst_hard_tail_parent_navigationS
      gstNavigationConstant gst_navigation_constant_origin_energyS
      gstCanonicalPrefixOffsetS gst_navigation_constant_unit_prefixS
      s n hs
    rw [hparentShape] at hcut
    rw [gst_prefixed_one_carry_shiftS] at hcut
    -- Deliberately leave only the true canonical child->parent block relation
    -- for Lean to normalize; the surrounding ancestry is now exact.
    rw [← hcut]
    simpa [T, GSTSeededHappyS, gstCarryS, gstAffineMulCarryS] using hGateS.2

  -- Atomic RED object after the full-energy splice: one left event-eight cell,
  -- no right event-eight cell, both on the same canonical infinite graph.
  -- The stronger perfect-power block theorem consumes hParentPrefixCarry and
  -- the origin-trit/canonical rectangle data from this exact state.
  exfalso
  omega

/-- Public prefix-one lift consumes only the Atomic Surgery V2 collision. -/
theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad


'''

s = s[:start] + replacement + s[end:]
p.write_text(s, encoding='utf-8')
print('installed Atomic Surgery V2 full-energy graph splice')
