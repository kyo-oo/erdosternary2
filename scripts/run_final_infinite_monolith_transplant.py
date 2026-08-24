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
    p.write_text(s, encoding='utf-8')
    print('TRANSPLANT: wired missing copied modules into ErdosTernary2.lean')
