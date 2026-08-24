#!/usr/bin/env python3
from pathlib import Path
import re

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

obsolete = 'theorem gst_prefix_one_information_bad_descends_inline\n'
child_contra = 'theorem gst_prefix_one_child_gate_contradicts_parent_bad_inline\n'
public_re = re.compile(r'(?m)^theorem gst_prefix_one_navigation_lift\s*:\s*$')
next_marker = '\n/-- The two consecutive power waves overlap'

obsolete_start = s.find(obsolete)
if obsolete_start < 0:
    raise SystemExit('obsolete information-descent theorem not found')
child_start = s.find(child_contra, obsolete_start)
if child_start < 0:
    raise SystemExit('obsolete child-gate contradiction theorem not found')

public_matches = list(public_re.finditer(s, child_start))
if len(public_matches) != 1:
    raise SystemExit(
        f'expected exactly one public prefix-one navigation lift after obsolete chain, found {len(public_matches)}')
public_start = public_matches[0].start()
public_end = s.find(next_marker, public_start)
if public_end < 0:
    raise SystemExit('public prefix-one navigation lift end marker not found')

replacement = r'''/-- Production prefix-one Navigation lift.

The obsolete information-descent / child-complete-badness detour is removed.
The stronger Ω∞ production theorem supplies a finite collision-polynomial zero
directly from the canonical child witness; that zero is exactly the parent
Navigation witness by `gst_omega_gate_zero_closes_parent`. -/
theorem gst_prefix_one_navigation_lift :
    GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  have hzero :
      ∃ j, GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 :=
    gst_omega_prefix_one_gate_exists s n hs hn hchild
  simpa using (gst_omega_gate_zero_closes_parent s 1 n hs hzero)
'''

s2 = s[:obsolete_start] + replacement + s[public_end:]

# Structural contract: surgery must remove the circular/obsolete chain and
# leave exactly the stronger Ω∞ gate-existence -> gate-zero-closes-parent path.
for forbidden in [
    'theorem gst_prefix_one_information_bad_descends_inline',
    'theorem gst_prefix_one_child_gate_contradicts_parent_bad_inline',
    'GSTCanonicalRightChordTrapS A z T',
    'gst_shared_x4_binary_factor_last_gate_high_bitS',
    'RED frontier:',
]:
    if forbidden in s2:
        raise SystemExit(f'obsolete surgery artifact survived: {forbidden}')

if re.search(r'(?m)^\s*gst_end\s*$', s2):
    raise SystemExit('literal gst_end survived production surgery')

if len(re.findall(r'(?m)^theorem gst_prefix_one_navigation_lift\s*:', s2)) != 1:
    raise SystemExit('production surgery must leave exactly one public prefix-one navigation lift')

required = [
    'gst_omega_prefix_one_gate_exists s n hs hn hchild',
    'gst_omega_gate_zero_closes_parent s 1 n hs hzero',
]
for needle in required:
    if needle not in s2:
        raise SystemExit(f'direct Ω∞ production splice missing: {needle}')

p.write_text(s2, encoding='utf-8')

print('DIRECT_OMEGA_SURGERY installed')
print('DIRECT_OMEGA_SURGERY removed=information_bad_descends,child_gate_contradicts_parent_bad')
print('DIRECT_OMEGA_SURGERY public_lifts=1')
print('DIRECT_OMEGA_SURGERY path=gate_exists->gate_zero_closes_parent')
