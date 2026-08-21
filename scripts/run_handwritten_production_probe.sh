#!/usr/bin/env bash
set -euxo pipefail

SNAP="$PWD/ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery"

curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.33.0-rc2
lake update
lake exe cache get
lake build GSTTactic

LEGACY_LINE=$(grep -n 'Legacy residual overproof' ErdosTernary2.lean | head -1 | cut -d: -f1)
CUT=$((LEGACY_LINE - 2))
test "$CUT" -eq 7326
head -n "$CUT" ErdosTernary2.lean > ErdosPreOmega.lean
lake env lean -o ErdosPreOmega.olean ErdosPreOmega.lean

export LEAN_PATH="$SNAP:$PWD:${LEAN_PATH:-}"
python3 - <<'PY'
from pathlib import Path
import re
root=Path('ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery')
files={p.stem:p for p in root.glob('*.lean')}
seeds=['GSTGraphV2SleepEquationLabScratch','GSTGraphV2SleepEquationCollisionScratch',
       'GSTGraphV2InfiniteBigNDichotomyScratch','GSTGraphV2SleepBadLanguageDescentScratch',
       'GSTGraphV2PhysicalSignedKernelTelescopeScratch','PhysicalSixBridgeGateScratch',
       'CanonicalTrapScratch']
rx=re.compile(r'^\s*import\s+(.+?)\s*$',re.M)
imports={}
for m,p in files.items():
    xs=[]
    for line in rx.findall(p.read_text()):
        line=line.split('--',1)[0].strip(); xs.extend(line.split())
    imports[m]={x for x in xs if x in files}
need=set()
def add(m):
    if m in need:return
    if m not in files:raise SystemExit('MISSING '+m)
    need.add(m)
    for d in imports[m]:add(d)
for s in seeds:add(s)
indeg={m:0 for m in need}; out={m:set() for m in need}
for m in need:
    for d in imports[m]&need: indeg[m]+=1; out[d].add(m)
q=sorted(m for m,v in indeg.items() if v==0); order=[]
while q:
    m=q.pop(0); order.append(m)
    for n in sorted(out[m]):
        indeg[n]-=1
        if indeg[n]==0:q.append(n);q.sort()
if len(order)!=len(need):raise SystemExit('IMPORT_CYCLE')
Path('.handwritten-order').write_text('\n'.join(order)+'\n')
print('HANDWRITTEN_CLOSURE_COUNT',len(order))
PY
while IFS= read -r mod; do
  lake env lean -o "$SNAP/$mod.olean" "$SNAP/$mod.lean"
done < .handwritten-order

lake env lean GSTHandwrittenPhysicalNoBig1.lean 2>&1 | tee handwritten-physical-nobig1.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' handwritten-physical-nobig1.log
grep -Fq "'gpt56_binary_residue_gap_doubles' depends on axioms:" handwritten-physical-nobig1.log
grep -Fq "'gpt56_physical_noBig1_impossible' depends on axioms:" handwritten-physical-nobig1.log
grep -Fq "'gpt56_physical_path_forces_first_big1' depends on axioms:" handwritten-physical-nobig1.log

lake env lean GSTHandwrittenPrefixOneProductionProbe.lean 2>&1 | tee handwritten-production-probe.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' handwritten-production-probe.log
grep -Fq "'gpt56_handwritten_operator_on_navigation_child' depends on axioms:" handwritten-production-probe.log
grep -Fq "'gpt56_physical_binary_row_is_infinite_bridge' depends on axioms:" handwritten-production-probe.log
grep -Fq "'gpt56_child_happy_gate_micro_dichotomy' depends on axioms:" handwritten-production-probe.log
grep -Fq "'gpt56_child_happy_gate_physical_two_case_quantitative' depends on axioms:" handwritten-production-probe.log
grep -Fq "'gpt56_last_gate_handwritten_boundary_dichotomy' depends on axioms:" handwritten-production-probe.log
