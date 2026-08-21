#!/usr/bin/env bash
set -euxo pipefail

SNAP="$PWD/ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery"

curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.33.0-rc2
lake update
lake exe cache get
lake build GSTTactic

test "$(wc -l < ErdosTernary2.lean)" -eq 8750
LEGACY_LINE=$(grep -n 'Legacy residual overproof' ErdosTernary2.lean | head -1 | cut -d: -f1)
CUT=$((LEGACY_LINE - 2))
echo "ROOT_LINES=$(wc -l < ErdosTernary2.lean) LEGACY_LINE=$LEGACY_LINE CUT=$CUT"
test "$CUT" -eq 7326
head -n "$CUT" ErdosTernary2.lean > ErdosPreOmega.lean
lake env lean -o ErdosPreOmega.olean ErdosPreOmega.lean

export LEAN_PATH="$SNAP:$PWD:${LEAN_PATH:-}"

# Compile the exact local dependency closure of the RED collision first.  This
# makes proof iterations reach the production theorem without paying for the
# unrelated heavyweight probes.  The full closure is still compiled below
# before monolith surgery/comparator certification.
python3 - <<'PY'
from pathlib import Path
import re
root = Path('ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery')
files = {p.stem:p for p in root.glob('*.lean')}
seeds = [
    'GSTGraphV2InfiniteBigNDichotomyScratch',
    'GSTGraphV2PhysicalSignedKernelTelescopeScratch',
]
rx = re.compile(r'^\s*import\s+(.+?)\s*$', re.M)
imports = {}
for m,p in files.items():
    names=[]
    for line in rx.findall(p.read_text()):
        line=line.split('--',1)[0].strip(); names.extend(line.split())
    imports[m] = {x for x in names if x in files}
need=set()
def add(m):
    if m in need: return
    if m not in files: raise SystemExit('MISSING_LOCAL_MODULE '+m)
    need.add(m)
    for d in imports[m]: add(d)
for s in seeds: add(s)
indeg={m:0 for m in need}; out={m:set() for m in need}
for m in need:
    for d in imports[m] & need:
        indeg[m]+=1; out[d].add(m)
q=sorted(m for m,v in indeg.items() if v==0); order=[]
while q:
    m=q.pop(0); order.append(m)
    for n in sorted(out[m]):
        indeg[n]-=1
        if indeg[n]==0: q.append(n); q.sort()
if len(order)!=len(need): raise SystemExit('IMPORT_CYCLE')
Path('.collision-order').write_text('\n'.join(order)+'\n')
print('COLLISION_DEPENDENCY_ORDER', order)
PY
while IFS= read -r mod; do
  lake env lean -o "$SNAP/$mod.olean" "$SNAP/$mod.lean"
done < .collision-order

for mod in \
  GSTHandwrittenPhysicalNoBig1 \
  GSTHandwrittenChildFirstBig1 \
  GSTHandwrittenHorizontalParentBridge \
  GSTHandwrittenPrefixOneLivePackage \
  GSTHandwrittenBigNThreeWorldFactors \
  GSTHandwrittenBigNSignedKernel; do
  lake env lean -o "$mod.olean" "$mod.lean"
done
lake env lean -o GSTHandwrittenPrefixOneCollisionRepair.olean GSTHandwrittenPrefixOneCollisionRepair.lean 2>&1 | tee handwritten-prefix-one-collision.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' handwritten-prefix-one-collision.log

# Full authoritative V2/snapshot closure.  Already compiled collision deps are
# reused from this same job; every remaining module is still kernel-checked.
python3 - <<'PY'
from pathlib import Path
import re
root = Path('ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery')
files = {p.stem:p for p in root.glob('*.lean')}
seeds = [
    'InformationRegenerationScratch',
    'StripConservationScratch',
    'GSTGraphV2SleepEquationLabScratch',
    'GSTGraphV2SleepEquationCollisionScratch',
    'GSTGraphV2InfiniteBigNDichotomyScratch',
    'GSTGraphV2SleepBadLanguageDescentScratch',
    'GSTGraphV2PhysicalSignedKernelTelescopeScratch',
    'PhysicalSixBridgeGateScratch',
    'CanonicalTrapScratch',
]
rx = re.compile(r'^\s*import\s+(.+?)\s*$', re.M)
imports = {}
for m,p in files.items():
    names=[]
    for line in rx.findall(p.read_text()):
        line=line.split('--',1)[0].strip(); names.extend(line.split())
    imports[m] = {x for x in names if x in files}
need=set()
def add(m):
    if m in need: return
    if m not in files: raise SystemExit('MISSING_LOCAL_MODULE '+m)
    need.add(m)
    for d in imports[m]: add(d)
for s in seeds: add(s)
indeg={m:0 for m in need}; out={m:set() for m in need}
for m in need:
    for d in imports[m] & need:
        indeg[m]+=1; out[d].add(m)
q=sorted(m for m,v in indeg.items() if v==0); order=[]
while q:
    m=q.pop(0); order.append(m)
    for n in sorted(out[m]):
        indeg[n]-=1
        if indeg[n]==0: q.append(n); q.sort()
if len(order)!=len(need): raise SystemExit('IMPORT_CYCLE')
Path('.probe-order').write_text('\n'.join(order)+'\n')
print('PROBE_DEPENDENCY_ORDER', order)
PY
while IFS= read -r mod; do
  if [[ ! -f "$SNAP/$mod.olean" ]]; then
    lake env lean -o "$SNAP/$mod.olean" "$SNAP/$mod.lean"
  fi
done < .probe-order

lake env lean -o GSTHandwrittenPrefixOneProductionProbe.olean GSTHandwrittenPrefixOneProductionProbe.lean 2>&1 | tee handwritten-production-probe.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' handwritten-production-probe.log

bash scripts/probe_physical_trap_counterexample.sh

python3 - <<'PY'
from pathlib import Path
p=Path('ErdosTernary2.lean')
src=p.read_text()
legacy_start = src.index('theorem gst_omega_termination_s1')
legacy_marker = '\n/-\n/-- Numerical ceiling used to bound every power-of-four graph witness. -/'
legacy_end = src.index(legacy_marker, legacy_start)
src = src[:legacy_start] + legacy_marker + src[legacy_end + len(legacy_marker):]
inline_start = src.index('theorem gst_prefix_one_information_bad_descends_inline')
two_wave_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'
inline_end = src.index(two_wave_marker, inline_start)
replacement = r'''theorem gst_v2_infinite_prefix_one_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  exact gpt56_prefix_one_collision_bigN s n hs hn hchild hBad

-- Public prefix-one theorem now consumes only the V2 collision interface.
theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_v2_infinite_prefix_one_collision s n hs hn hchild hBad

'''
src = src[:inline_start] + replacement + src[inline_end:]
p.write_text(src)
print('SURGERY_LINES',src.count('\n')+1)
PY

lake env lean -o ErdosTernary2.olean ErdosTernary2.lean 2>&1 | tee surgery-first.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' surgery-first.log
bash scripts/sorry_check.sh
bash scripts/comparator.sh
