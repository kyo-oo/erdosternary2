#!/usr/bin/env bash
set -euxo pipefail

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

python3 - <<'PY'
from pathlib import Path
import re
p=Path('ErdosTernary2.lean')
src=p.read_text()
DECL=re.compile(r'(?m)^(?:theorem|lemma|def|abbrev|structure|inductive|instance|private\s+theorem)\s+[A-Za-z0-9_]')
def span(text,name):
    m=re.search(rf'(?m)^theorem\s+{re.escape(name)}\b',text)
    if not m: raise SystemExit('MISSING_DECL '+name)
    n=DECL.search(text,m.end())
    return m.start(), len(text) if n is None else n.start()
def remove(text,name):
    a,b=span(text,name)
    return text[:a]+text[b:]
for name in [
    'gst_omega_termination_s1',
    'gst_omega_termination_s3',
    'gst_omega_termination_stable',
    'gst_residual_omega_termination',
    'gst_residual_navigation_lift',
    'gst_prefix_one_information_bad_descends_inline',
    'gst_prefix_one_child_gate_contradicts_parent_bad_inline',
]:
    src=remove(src,name)
replacement=r'''
/-- V2 replacement seam for the deleted legacy Omega corridor. -/
theorem gst_v2_infinite_prefix_one_collision
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
    | zero => simp [gstCarry]
    | succ q =>
        dsimp [T]
        exact gstCarry_lt_four _ (q+1) (by omega)
  have hC : gstCarry T j = 0 ∨ gstCarry T j = 3 := by omega
  omega

theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad := gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_v2_infinite_prefix_one_collision s n hs hn hchild hBad

'''
a,b=span(src,'gst_prefix_one_navigation_lift')
src=src[:a]+replacement+src[b:]
p.write_text(src)
print('SURGERY_LINES',src.count('\n')+1)
PY

lake env lean -o ErdosTernary2.olean ErdosTernary2.lean 2>&1 | tee surgery-first.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' surgery-first.log
