#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

repls = [
    (
        "theorem gst_h_creation_full_power_navigation_atomic\n    (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :\n    GSTNavigationWitness (4^k) := by\n  obtain ⟨p, hp1, hd, hcase⟩ := h_creation_for_4pow k hk5 hk7",
        "theorem gst_h_creation_full_power_navigation_atomic\n    (k : Nat) (hk7 : 7 ≤ k) :\n    GSTNavigationWitness (4^k) := by\n  obtain ⟨p, hp1, hd, hcase⟩ := hCreationCheck_univ k hk7",
    ),
    (
        "gst_h_creation_full_power_navigation_atomic K (by omega) (by omega)",
        "gst_h_creation_full_power_navigation_atomic K (by omega)",
    ),
    (
        "#print axioms h_creation_for_4pow\n",
        "",
    ),
]

for old, new in repls:
    count = s.count(old)
    if count != 1:
        raise SystemExit(f'expected exactly one live-certificate patch site, found {count}: {old[:80]!r}')
    s = s.replace(old, new, 1)

# The dead historical name may remain in comments/source archaeology, but must
# not occur in the installed helper body or in a live #print.
helper_start = s.index('theorem gst_h_creation_full_power_navigation_atomic')
helper_end = s.index('theorem gst_full_power_navigation_descends_atomic', helper_start)
if 'h_creation_for_4pow' in s[helper_start:helper_end]:
    raise SystemExit('dead creation certificate survived installed helper body')
if '#print axioms h_creation_for_4pow' in s:
    raise SystemExit('dead creation certificate survived live axiom print')
if 'hCreationCheck_univ k hk7' not in s[helper_start:helper_end]:
    raise SystemExit('live hCreationCheck_univ certificate not installed')

p.write_text(s, encoding='utf-8')
print('LIVE_HCREATIONCHECK_REUSED=1')
print('DEAD_H_CREATION_LIVE_REFERENCES=0')
