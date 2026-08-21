#!/usr/bin/env bash
set -euxo pipefail

curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.33.0-rc2
lake update
lake exe cache get
lake build GSTTactic

cp ErdosTernary2.lean ErdosTernary2.before-final-direct.lean
python3 - <<'PY'
from pathlib import Path
import re
p = Path('ErdosTernary2.lean')
text = p.read_text()
omega_marker = 'theorem gst_omega_termination_s1'
if omega_marker not in text:
    raise SystemExit('missing Omega surgery marker')
pre = text[:text.index(omega_marker)]
creation_name = 'theorem h_creation_for_4pow'
start = text.index(creation_name)
tail = text[start:]
nxt = re.search(r'\n(?=(?:theorem|lemma|def|structure|inductive|abbrev)\s+[A-Za-z0-9_])', tail[len(creation_name):])
if not nxt:
    raise SystemExit('cannot find end of h_creation_for_4pow')
end = start + len(creation_name) + nxt.start() + 1
creation = text[start:end].rstrip() + '\n'
for tok in ('sorry', 'admit', 'sorryAx'):
    if re.search(rf'(?<![A-Za-z0-9_]){re.escape(tok)}(?![A-Za-z0-9_])', creation):
        raise SystemExit(f'h_creation_for_4pow contains forbidden token: {tok}')
direct = r'''

/- FINAL DIRECT-INDUCTION SURGERY. -/
theorem erdos_ternary_2_even_universal
    (a : Nat) (ha : 5 ≤ a) : hasTernaryTwo (4^a) = true := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
      by_cases hbase : a ≤ 500
      · exact modular_check_base a ha hbase
      · have ha1 : 5 ≤ a - 1 := by omega
        have hlt : a - 1 < a := by omega
        have hprev : hasTernaryTwo (4^(a-1)) = true := ih (a-1) hlt ha1
        have hRmod : (4^(a-1)) % 3 = 1 := by
          rw [Nat.pow_mod, show (4:Nat) % 3 = 1 from by decide, Nat.one_pow]
        have hcreation := h_creation_for_4pow (a-1) ha1 (by omega : a - 1 ≠ 7)
        have hstep : hasTernaryTwo (4 * 4^(a-1)) = true :=
          gst_duality (4^(a-1)) hRmod hprev hcreation
        have hpow : 4 * 4^(a-1) = 4^a := by
          have hae : a = (a-1)+1 := by omega
          calc
            4 * 4^(a-1) = 4^(a-1) * 4 := by ac_rfl
            _ = 4^((a-1)+1) := (Nat.pow_succ 4 (a-1)).symm
            _ = 4^a := by rw [← hae]
        simpa [hpow] using hstep

theorem erdos_ternary_2_universal (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false := by
  by_cases hodd : n % 2 = 1
  · exact erdos_ternary_2_odd_universal n hn hodd
  · have heven : n % 2 = 0 := by omega
    have h4eq : 2^n = 4^(n/2) := by
      have hn_eq : n = 2 * (n/2) := by omega
      rw [show (4 : Nat) = 2^2 from by decide, ← Nat.pow_mul, ← hn_eq]
    rw [h4eq]
    have ha : 5 ≤ n/2 := by omega
    exact has_two_imp_not_no_two (4^(n/2))
      (erdos_ternary_2_even_universal (n/2) ha)

#print axioms h_creation_for_4pow
#print axioms erdos_ternary_2_even_universal
#print axioms erdos_ternary_2_universal
'''
candidate = pre.rstrip() + '\n\n' + creation + direct
for dead in ('theorem gst_omega_termination_s1','theorem gst_omega_termination_s3','theorem gst_omega_termination_stable','theorem gst_residual_omega_termination'):
    if dead in candidate:
        raise SystemExit(f'dead Omega declaration survived: {dead}')
p.write_text(candidate)
print('DIRECT_CANDIDATE_BUILT', candidate.count('\n') + 1)
PY

set -o pipefail
lake env lean ErdosTernary2.lean 2>&1 | tee final-direct-lean.log
! grep -E 'error:|declaration uses .*[Ss]orry|sorryAx' final-direct-lean.log
bash scripts/sorry_check.sh 2>&1 | tee final-direct-sorry.log
bash scripts/comparator.sh 2>&1 | tee final-direct-comparator.log
grep -q 'Your solution is okay!' final-direct-comparator.log
grep -q 'COMPARATOR RESULT: PASS' final-direct-comparator.log
echo 'FINAL_DIRECT_COMPARATOR_GREEN'
