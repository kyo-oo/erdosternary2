#!/usr/bin/env python3
from pathlib import Path
import re

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

raw_lines = len(s.splitlines())
raw_theorems = len(re.findall(r'(?m)^\s*(?:private\s+)?theorem\s+', s))
raw_defs = len(re.findall(r'(?m)^\s*(?:noncomputable\s+)?def\s+', s))
print(f'PRODUCTION_STATS raw_lines={raw_lines} raw_theorems={raw_theorems} raw_defs={raw_defs}')

# Keep the production theorem unchanged except for the one RED seam.  Import
# the already-kernel-green perfect-power collision theorem and its exact graph
# dependencies into the transformed monolith.
for imp in [
    'import GSTGraphV2InfiniteControl\n',
    'import GSTU2DPureDivergence83\n',
    'import GSTGraphV2UnifiedPowerRectangle\n',
    'import GSTGraphV2UnifiedVerticalTelescope\n',
    'import GSTGraphV2PerfectPowerAncestry\n',
    'import GSTGraphV2PerfectPowerBlockProbe\n',
    'import GSTGraphV2PerfectPowerBlockCollision\n',
]:
    if imp not in s:
        anchor = 'import Mathlib.Tactic.Ring\n'
        if anchor not in s:
            raise SystemExit('import anchor not found')
        s = s.replace(anchor, anchor + imp, 1)

needle = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

installed_marker = 'have hPerfectPowerCollision : False := by'
if needle not in s:
    if installed_marker in s and '\n  gst_end\n' not in s:
        print('perfect-power collision surgery already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('literal residual gst_end seam not found')

replacement = r'''  -- Final Graph-V2 collision bridge.  The dedicated collision theorem is
  -- already kernel-green.  Here we only identify the monolith child witness
  -- with the left physical perfect-power boundary and the Omega bad trace
  -- with the all-depth bad right boundary of the same rectangle.
  have hchildOriginal :
      GSTNavigationWitness (gstNavigationConstant (s+1) n) := by
    rw [hscale]
    exact hchild

  obtain ⟨q, hqDigit, hqSpace⟩ := hchildOriginal

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
'''

s = s.replace(needle, replacement, 1)
p.write_text(s, encoding='utf-8')
transformed_lines = len(s.splitlines())
transformed_theorems = len(re.findall(r'(?m)^\s*(?:private\s+)?theorem\s+', s))
transformed_defs = len(re.findall(r'(?m)^\s*(?:noncomputable\s+)?def\s+', s))
print(f'PRODUCTION_STATS transformed_lines={transformed_lines} transformed_theorems={transformed_theorems} transformed_defs={transformed_defs}')
print('installed perfect-power collision production surgery')
