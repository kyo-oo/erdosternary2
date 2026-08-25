#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

# Preserve the monolith and import only the already-kernel-green Graph-V2
# collision stack.  Do not delete attached packets or route through the old
# residual/Omega termination machinery.
for imp in [
    'import GSTGraphV2InfiniteControl\n',
    'import GSTGraphV2PerfectPowerBlockCollision\n',
]:
    if imp not in s:
        anchor = 'import Mathlib.Tactic.Ring\n'
        if anchor not in s:
            raise SystemExit('import anchor not found')
        s = s.replace(anchor, anchor + imp, 1)

start_marker = '/-- Literal BIG-N finite-support horizon for the canonical child information. -/'
end_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'
installed_marker = '-- SOL56 DIRECT PERFECT-POWER COLLISION PREFIX-ONE CLOSURE'

if start_marker not in s:
    if installed_marker in s:
        print('direct perfect-power collision replacement already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('old prefix-one start marker not found')
if end_marker not in s:
    raise SystemExit('prefix-one end marker not found')

start = s.index(start_marker)
end = s.index(end_marker, start)

replacement = r'''/-- Literal BIG-N finite-support horizon for the canonical child information. -/
theorem gst_prefix_one_bigN_future_zero_inline
    (s n : Nat) (hs : 1 ≤ s) :
    let N := gstNavigationConstant (s+1) n
    N / 3^N = 0 := by
  dsimp only
  by_cases hN0 : gstNavigationConstant (s+1) n = 0
  · rw [hN0]
    decide
  · exact gst_navigation_self_horizon_zeroS
      (gstNavigationConstant (s+1) n) (by omega)

-- SOL56 DIRECT PERFECT-POWER COLLISION PREFIX-ONE CLOSURE
/-- Prefix-one information descent from the exact canonical Graph-V2
perfect-power rectangle.  A child Navigation witness is the left boundary
Happy event.  The Omega-infinite bad trace is exactly an all-depth bad right
boundary one canonical width later.  The already-kernel-green perfect-power
collision theorem makes those two facts incompatible. -/
theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  obtain ⟨q, hqDigit, hqSpace⟩ := hchild

  have hqCarry :
      gstCarry (gstNavigationConstant (s+1) n) q = 0 ∨
      gstCarry (gstNavigationConstant (s+1) n) q = 3 := by
    cases q with
    | zero =>
        left
        simp [gstCarry]
    | succ q =>
        have hmod3 :
            gstCarry (gstNavigationConstant (s+1) n) (q+1) % 3 = 0 :=
          gstGoodSpace_carry_mod3_zero _ _ hqSpace
        have hlt :
            gstCarry (gstNavigationConstant (s+1) n) (q+1) < 4 :=
          gstCarry_lt_four _ _ (by omega)
        omega

  have hChildGateS :
      gstDigitS (gstNavigationConstant (s+1) n) q = 2 ∧
      (gstCarryS (gstNavigationConstant (s+1) n) q = 0 ∨
       gstCarryS (gstNavigationConstant (s+1) n) q = 3) := by
    constructor
    · simpa [gstDigitS, gstDigit] using hqDigit
    · simpa [gstCarryS, gstCarry] using hqCarry

  have hChildEnergyGate :=
    gst_child_gate_embeds_phase_zero_energyS
      s (gstNavigationConstant (s+1) n) q hs hChildGateS
  dsimp only at hChildEnergyGate

  have hChildEnergy :
      GSTGraphV2PerfectPowerBlock.canonicalEnergy s n =
        1 + 3^(s+2) * gstNavigationConstant (s+1) n := by
    unfold GSTGraphV2PerfectPowerBlock.canonicalEnergy
    have h := gst_navigation_decomposition (s+1) n (by omega)
    simpa [show (s+1)+1 = s+2 by omega] using h

  have hChildPhysical :
      GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2PerfectPowerBlock.canonicalEnergy s n)
          0 (s+2+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2PerfectPowerBlock.canonicalEnergy s n)
          0 (s+2+q)).seven.digit := by
    simpa [GSTU2DEventTransport.HappyCell,
      GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex,
      GSTCanonicalSevenAxisBridge.carry4,
      GSTCanonicalSevenAxisBridge.digit3,
      gstCarryS, gstDigitS, hChildEnergy] using hChildEnergyGate

  let H : Nat := gstPrefixOneUPotentialTailS s n

  have hSeededParentBad :
      ∀ j, GSTBadPairS
        (gstAffineMulCarryS 4 1 H j) (gstDigitS H j) := by
    intro j
    simpa [H] using
      (gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad j)

  have hAunit :
      4^(3^s) = 1 + 3^(s+1) * gstNavigationConstant s 1 :=
    gst_navigation_decomposition s 1 hs

  have hUnitPrefix :
      gstNavigationConstant s 1 = 1 + 3 * gstCanonicalPrefixOffsetS s :=
    gst_navigation_constant_unit_prefixS s hs

  have hRightEnergy0 :=
    gst_canonical_phase1_energy_shape_surgeryS
      gstNavigationConstant gst_navigation_constant_origin_energyS
      s n (gstNavigationConstant s 1) gstCanonicalPrefixOffsetS s
      hs hAunit hUnitPrefix

  have hRightEnergy :
      4^(3^s) * GSTGraphV2PerfectPowerBlock.canonicalEnergy s n =
        (1 + 3^(s+1)) + 3^(s+2) * H := by
    unfold GSTGraphV2PerfectPowerBlock.canonicalEnergy
    have hpow : 3 * 3^(s+1) = 3^(s+2) := by
      rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
      ac_rfl
    rw [hpow] at hRightEnergy0
    simpa [H, gstPrefixOneUPotentialTailS, gstCanonicalPrefixOffsetS,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRightEnergy0

  have hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2PerfectPowerBlock.canonicalEnergy s n)
          (GSTGraphV2PerfectPowerBlock.canonicalWidth s) (s+2+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph
          (GSTGraphV2PerfectPowerBlock.canonicalEnergy s n)
          (GSTGraphV2PerfectPowerBlock.canonicalWidth s) (s+2+j)).seven.digit := by
    intro j hHappy
    have hParentState := gst_parent_energy_stateS s H j hs
    dsimp only at hParentState

    have hPhysicalGate :
        gstDigitS ((1 + 3^(s+1)) + 3^(s+2)*H) (s+2+j) = 2 ∧
        (gstCarryS ((1 + 3^(s+1)) + 3^(s+2)*H) (s+2+j) = 0 ∨
         gstCarryS ((1 + 3^(s+1)) + 3^(s+2)*H) (s+2+j) = 3) := by
      simpa [GSTU2DEventTransport.HappyCell,
        GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex,
        GSTCanonicalSevenAxisBridge.carry4,
        GSTCanonicalSevenAxisBridge.digit3,
        GSTGraphV2PerfectPowerBlock.canonicalWidth,
        gstCarryS, gstDigitS, hRightEnergy,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hHappy

    have hTailGate :
        gstDigitS H j = 2 ∧
        (gstAffineMulCarryS 4 1 H j = 0 ∨
         gstAffineMulCarryS 4 1 H j = 3) := by
      constructor
      · rw [← hParentState.1]
        exact hPhysicalGate.1
      · rw [← hParentState.2]
        exact hPhysicalGate.2

    exact hSeededParentBad j hTailGate

  have hPerfectPowerCollision : False := by
    exact
      GSTGraphV2PerfectPowerBlockCollision.canonical_perfect_power_block_collision
        s n q hs hn hChildPhysical hRightBad

  exact hPerfectPowerCollision

/-- Corrected information-wave closure: once parent badness descends to the
shared child information, the certified child Happy Gate is an immediate
contradiction. -/
theorem gst_prefix_one_child_gate_contradicts_parent_bad_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have hChildBad : GSTCompleteBadTrace (gstNavigationConstant (s+1) n) :=
    gst_prefix_one_information_bad_descends_inline s n hs hn hBad
  have hAt := hChildBad data.childGateIndex
  have hGate :
      gstDigit (gstNavigationConstant (s+1) n) data.childGateIndex = 2 ∧
      (gstCarry (gstNavigationConstant (s+1) n) data.childGateIndex = 0 ∨
       gstCarry (gstNavigationConstant (s+1) n) data.childGateIndex = 3) := by
    simpa only [gstOmega] using data.childGate
  exact hAt hGate

/-- Public prefix-one theorem: parent failure supplies the exact bad trace, and
the canonical perfect-power collision contradicts the certified child gate. -/
theorem gst_prefix_one_navigation_lift :
    GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  let data : GSTPrefixOneOmegaData s n :=
    gst_prefix_one_omegaData s n hs hchild
  exact gst_prefix_one_child_gate_contradicts_parent_bad_inline
    s n hs hn data hBad

#print axioms gst_prefix_one_information_bad_descends_inline
#print axioms gst_prefix_one_navigation_lift

'''

s = s[:start] + replacement + s[end:]

# RC2 mechanical scar already established by the forward compiler frontier.
old_ring = 'convert hshared using 1 <;> ring'
ring_count = s.count(old_ring)
if ring_count != 1:
    raise SystemExit(f'expected exactly one localized ring scar, found {ring_count}')
s = s.replace(old_ring, 'convert hshared using 1 <;> ring_nf', 1)

# Hard guards: the live output must not reintroduce the obsolete creation,
# residual-lift, or old collision-helper routes.
for forbidden in (
    'theorem gst_h_creation_full_power_navigation_atomic',
    'theorem gst_full_power_navigation_descends_atomic',
    'theorem gst_prefix_one_u2d_atomic_collision_inline',
):
    if forbidden in s:
        raise SystemExit(f'obsolete live theorem survived direct replacement: {forbidden}')

live = s[start:s.index(end_marker, start) if end_marker in s[start:] else len(s)]
if 'h_creation_for_4pow' in live:
    raise SystemExit('legacy h_creation dependency survived direct replacement block')
if 'gst_residual_navigation_lift' in live:
    raise SystemExit('quarantined residual navigation lift survived direct replacement block')
if 'trace_state\n  contradiction' in s:
    raise SystemExit('old RED seam survived direct replacement')

p.write_text(s, encoding='utf-8')
print('DIRECT_PREFIX_ONE_PERFECT_POWER_COLLISION=1')
print('LIVE_LEGACY_H_CREATION_DEPENDENCY=0')
print('LIVE_RESIDUAL_NAVIGATION_LIFT_DEPENDENCY=0')
print('forward mechanical RC2 fixes installed')