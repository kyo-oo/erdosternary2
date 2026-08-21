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

# Compile the sound handwritten/V2 dependency closure needed by the production
# equation probe and the concrete physical-trap counterexample probe.
export LEAN_PATH="$SNAP:$PWD:${LEAN_PATH:-}"
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
    'CanonicalTrapScratch',
]
rx = re.compile(r'^\s*import\s+(.+?)\s*$', re.M)
imports = {}
for m,p in files.items():
    names=[]
    for line in rx.findall(p.read_text()):
        line=line.split('--',1)[0].strip()
        names.extend(line.split())
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
  lake env lean -o "$SNAP/$mod.olean" "$SNAP/$mod.lean"
done < .probe-order

lake env lean GSTHandwrittenPrefixOneProductionProbe.lean | tee handwritten-production-probe.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' handwritten-production-probe.log

bash scripts/probe_physical_trap_counterexample.sh

# Comment-safe physical surgery. Replace whole semantic corridors between
# stable markers instead of guessing declaration spans; this preserves the
# existing legacy quarantine comment and all later public declarations.
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
  let T := gstNavigationConstant (s+1) n
  let X := c s / 3 + 4^(3^s) * T
  have hseeded : GSTSeededAffineBadTrace 1 X := by
    have h := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
    have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
      rw [Nat.pow_one, c_mod3 s hs]
    rw [hseed] at h
    simpa [T, X] using h
  obtain ⟨j, hd, hspace⟩ := hchild
  have hCmod : gstCarry T j % 3 = 0 := by
    dsimp [T]
    exact gstGoodSpace_carry_mod3_zero _ j hspace
  have hClt : gstCarry T j < 4 := by
    cases j with
    | zero => simp [gstCarry, Nat.mod_one]
    | succ q =>
        dsimp [T]
        exact gstCarry_lt_four _ (q+1) (by omega)
  have hC : gstCarry T j = 0 ∨ gstCarry T j = 3 := by omega
  omega

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
for bad in ['theorem gst_omega_termination_s1','theorem gst_residual_navigation_lift :']:
    if bad in src[:src.index('/-\n/-- Numerical ceiling')]:
        raise SystemExit('LIVE_LEGACY_DECLARATION '+bad)
PY

lake env lean -o ErdosTernary2.olean ErdosTernary2.lean 2>&1 | tee surgery-first.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' surgery-first.log
