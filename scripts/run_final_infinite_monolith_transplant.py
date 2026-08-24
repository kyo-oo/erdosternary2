#!/usr/bin/env python3
from pathlib import Path
import runpy

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

begin_marker = '-- BEGIN SOL56 FINAL INFINITE MONOLITH TRANSPLANT'
end_marker = '-- END SOL56 FINAL INFINITE MONOLITH TRANSPLANT'
original_seam = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

# If a previous CI iteration already persisted the transplanted theorem body,
# restore only that exact marked block to the original seam.  The canonical
# transplant script can then install the newest body.  This edits the live
# monolith on every iteration instead of freezing the first transplant.
if begin_marker in s:
    bpos = s.index(begin_marker)
    line_start = s.rfind('\n', 0, bpos) + 1
    epos = s.index(end_marker, bpos) + len(end_marker)
    line_end = s.find('\n', epos)
    if line_end == -1:
        line_end = len(s)
    else:
        line_end += 1
    s = s[:line_start] + original_seam + s[line_end:]
    p.write_text(s, encoding='utf-8')
    print('REFRESH: removed previous marked monolith transplant')

runpy.run_path('scripts/apply_final_infinite_monolith_transplant.py', run_name='__main__')

# Make the exact copied theorem modules part of the live monolith itself.
# Add missing imports individually so later transplant iterations can grow the
# block without being frozen by imports persisted by an earlier iteration.
s = p.read_text(encoding='utf-8')
anchor = 'import GSTFinalPurePowerResidueTransplant\n'
imports = [
    'PurePowerResidueGraphScratch',
    'InformationQuotientScratch',
    'InformationIterationScratch',
    'HorizontalTrapWidthDescentScratch',
    'PhaseCycleInformationScratch',
    'CanonicalCausalityScratch',
    'CanonicalOriginModulusScratch',
    'CanonicalOriginCutIntersectionScratch',
    'NavigationResidueCutScratch',
    'PrefixOneOriginPhaseRecursionScratch',
]
if anchor not in s:
    raise SystemExit('transplanted import anchor not found')
insert = anchor
for mod in imports:
    line = f'import {mod}\n'
    if line not in s:
        insert += line
if insert != anchor:
    s = s.replace(anchor, insert, 1)
    print('TRANSPLANT: wired missing copied modules into ErdosTernary2.lean')

# Replace the obsolete one-trit hard-family shortcut in the generated proof
# body.  The live hard branch must retain all k-1 preceding zero origin trits.
old_cut = '''      have hPrefixSquare := gst_canonical_prefix_one_energy_squareS
        gstNavigationConstant hQ 1 m (by decide)
      have hOriginRec := gst_hard_tail_origin_one_recursionS
        gstNavigationConstant hQ z hunit 1 (m/3) (by decide)
      have hOriginDigit := gst_hard_tail_origin_one_mod3S
        gstNavigationConstant hQ z hunit hz3 1 (m/3) (by decide)

      -- Full exact power-residue rectangle, not the reduced one-theorem probe.
'''
new_cut = '''      -- Exact arbitrary-k cut: do not collapse 1+3^k*m to the one-trit case.
      have hParentCutDecomposition :=
        gst_level_one_prefix_one_cut_decompositionS k m
      have hParentCutResidue : 2 ≤ k ->
          gstNavigationConstant 1 (1 + 3^k*m) % 3^k = 7 := by
        intro hk2
        exact gst_level_one_prefix_one_cut_residueS k m hk2
      have hParentCutTail : 2 ≤ k ->
          gstNavigationConstant 1 (1 + 3^k*m) / 3^k =
            64 * gstNavigationConstant (1+k) m := by
        intro hk2
        exact gst_level_one_prefix_one_cut_tailS k m hk2
      have hParentCutCarry : 2 ≤ k ->
          gstCarryS (gstNavigationConstant 1 (1 + 3^k*m)) k =
            28 / 3^k := by
        intro hk2
        exact gst_level_one_prefix_one_cut_carryS k m hk2
      have hParentCutDigit : 2 ≤ k ->
          gstDigitS (gstNavigationConstant 1 (1 + 3^k*m)) k = 1 := by
        intro hk2
        exact gst_level_one_prefix_one_cut_digit_oneS k m hk2 hm1

      -- Align the literal transplanted A=64,D=9 strip with the live row.
      -- qStrip retains the k-1 leading zero trits before the first nonzero m trit.
      let qStrip := (k-1) + q
      let Tstrip := 3^(k-1) * gstNavigationConstant (1+k) m
      let Hstrip := 2 + 64*Tstrip
      have hEstrip : E = 1 + 3*9*Tstrip := by
        have hnav := gst_navigation_decomposition (1+k) m (by omega)
        have hpow : 3^((1+k)+1) = 27 * 3^(k-1) := by
          rw [show (1+k)+1 = 3 + (k-1) by omega, Nat.pow_add]
          norm_num
        rw [hpow] at hnav
        simpa [E, Tstrip,
          GSTGraphV2HandwrittenOmegaUBlock.residualEnergy,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnav
      have hParentEnergyStrip : 64*E = 10 + 27*Hstrip := by
        rw [hEstrip]
        dsimp [Hstrip]
        ring

      -- Full exact power-residue rectangle, not the reduced one-theorem probe.
'''
if old_cut not in s:
    raise SystemExit('hard-family one-trit shortcut not found in generated monolith')
s = s.replace(old_cut, new_cut, 1)

p.write_text(s, encoding='utf-8')
print('TRANSPLANT: exact arbitrary-k hard-family cut installed in ErdosTernary2.lean')
