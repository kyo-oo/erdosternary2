#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

creation_marker = 'theorem h_creation_for_4pow'
next_marker = '\ntheorem mul4_lift_gst_duality'
helper_marker = 'theorem gst_h_creation_full_power_navigation_atomic'
helper_next = 'theorem gst_full_power_navigation_descends_atomic'

helper_start = s.index(helper_marker)
helper_end = s.index(helper_next, helper_start)
helper = s[helper_start:helper_end]

# Keep the universal adapter contract exactly as restored by the current U2D
# generator. The bounded hCreationCheck shortcut is forbidden because the
# collision exponent K is unbounded.
required_call = 'h_creation_for_4pow k hk5 hk7'
if required_call not in helper:
    raise SystemExit('universal h_creation_for_4pow adapter call is not intact')
if 'hCreationCheck_univ k hk7' in helper:
    raise SystemExit('bounded hCreationCheck shortcut survived in U2D helper')

# Production retains the general theorem inside the quarantined legacy block.
# Lift that exact declaration, then apply only the two RC2 elaboration repairs
# exposed by the current-head certification run:
#   1. make the documented strong induction explicit;
#   2. expose gstDigit before rewriting the exact forward carry edge.
qstart = s.index(creation_marker)
qend = s.index(next_marker, qstart)
if qstart >= helper_start:
    raise SystemExit('expected quarantined h_creation theorem before U2D helper')
creation_decl = s[qstart:qend].rstrip() + '\n\n'
if not creation_decl.startswith(creation_marker):
    raise SystemExit('h_creation extraction boundary changed')
if creation_decl.count(creation_marker) != 1:
    raise SystemExit('h_creation extraction multiplicity changed')

proof_anchor = ':= by\n'
if creation_decl.count(proof_anchor) < 1:
    raise SystemExit('h_creation proof anchor changed')
head, body = creation_decl.split(proof_anchor, 1)
recursive_old = '    have hih := h_creation_for_4pow (k - 1) hk1 hk1_7\n'
recursive_new = '      have hih := ih (k - 1) (by omega) hk1 hk1_7\n'
if recursive_old not in body:
    raise SystemExit('h_creation recursive call shape changed')
# Nest the existing proof body under the strong-recursion induction branch.
body = ''.join(('  ' + line) if line.strip() else line for line in body.splitlines(keepends=True))
if recursive_new.strip() not in body:
    # The old recursive line acquired two spaces from the branch indentation.
    body = body.replace('      have hih := h_creation_for_4pow (k - 1) hk1 hk1_7\n', recursive_new, 1)
creation_decl = (
    head + proof_anchor +
    '  induction k using Nat.strongRecOn with\n'
    '  | ind k ih =>\n' +
    body
)
if 'have hih := h_creation_for_4pow (k - 1)' in creation_decl:
    raise SystemExit('direct self-call survived strong-induction repair')
if 'have hih := ih (k - 1) (by omega) hk1 hk1_7' not in creation_decl:
    raise SystemExit('strong-induction recursive call was not installed')

# Guard against accidental double activation if this patcher is invoked twice.
live_stamp = '-- SOL56 LIVE GENERAL H_CREATION REACTIVATED\n'
if live_stamp in s:
    print('FULL_H_CREATION_ALREADY_REACTIVATED=1')
    p.write_text(s, encoding='utf-8')
    raise SystemExit(0)

s = s[:helper_start] + live_stamp + creation_decl + s[helper_start:]

# Mechanical gstDigit exposure in the current U2D adapter. The compiler error
# showed `hd` in raw quotient form while the carry edge contains `gstDigit`.
helper_old = '''    have hnext := gstCarry_forward_exact (4^k) p hp1
    rw [hC, hd] at hnext
    norm_num [gstStepCarry] at hnext
'''
helper_new = '''    have hnext := gstCarry_forward_exact (4^k) p hp1
    have hdDigit : gstDigit (4^k) p = 2 := by
      simpa [gstDigit] using hd
    rw [hC, hdDigit] at hnext
    norm_num [gstStepCarry] at hnext
'''
if helper_old not in s:
    raise SystemExit('U2D carry-one helper rewrite shape changed')
s = s.replace(helper_old, helper_new, 1)

# Exactly one live copy sits after the explicit stamp; the original textual copy
# remains quarantined for archaeology.
live_start = s.index(live_stamp) + len(live_stamp)
live_helper = s.index(helper_marker, live_start)
live_slice = s[live_start:live_helper]
if live_slice.count(creation_marker) != 1:
    raise SystemExit('expected exactly one reactivated live h_creation theorem')
if required_call not in s[live_helper:s.index(helper_next, live_helper)]:
    raise SystemExit('U2D helper no longer consumes general h_creation theorem')
if 'rw [hC, hdDigit] at hnext' not in s[live_helper:s.index(helper_next, live_helper)]:
    raise SystemExit('gstDigit RC2 repair missing from U2D helper')

p.write_text(s, encoding='utf-8')
print('FULL_H_CREATION_REACTIVATED=1')
print('STRONG_INDUCTION_RC2_REPAIR=1')
print('GSTDIGIT_RC2_REPAIR=1')
print('UNBOUNDED_U2D_CREATION_ADAPTER_PRESERVED=1')
