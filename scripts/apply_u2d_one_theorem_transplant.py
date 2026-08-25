#!/usr/bin/env python3
from pathlib import Path
import ast
import re

MONOLITH = Path('ErdosTernary2.lean')
U2D_SOURCE = Path('scripts/apply_u2d_atomic_replacement.py')
MIN_MONOLITH_BYTES = 300_000
TARGET = 'theorem gst_prefix_one_information_bad_descends_inline\n'
TARGET_END = '\n/-- Corrected information-wave closure:'
PUBLIC_MARKER = '/-- Public prefix-one lift consumes only the exact Graph-V2 event collision. -/'
IMPORT = 'import GSTGraphV2InfiniteControl\n'
STALE_UNUSED_IMPORTS = (
    'import GSTPrefixOnePhaseIncidenceControl\n',
    'import GSTPrefixOneSpacetimeIncidenceControl\n',
)


def extract_green_helpers() -> str:
    tree = ast.parse(U2D_SOURCE.read_text(encoding='utf-8'))
    replacement = None
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if any(isinstance(t, ast.Name) and t.id == 'replacement' for t in node.targets):
            replacement = ast.literal_eval(node.value)
            break
    if not isinstance(replacement, str):
        raise SystemExit('could not extract green U2D replacement payload')
    if PUBLIC_MARKER not in replacement:
        raise SystemExit('green U2D public marker not found')
    helpers = replacement[:replacement.index(PUBLIC_MARKER)].rstrip() + '\n\n'
    required = (
        'theorem gst_h_creation_full_power_navigation_atomic',
        'theorem gst_full_power_navigation_descends_atomic',
        'theorem gst_prefix_one_u2d_atomic_collision_inline',
    )
    for name in required:
        if name not in helpers:
            raise SystemExit(f'missing required green helper: {name}')
    if 'theorem gst_prefix_one_navigation_lift' in helpers:
        raise SystemExit('helper extraction crossed the public-lift boundary')
    return helpers


s = MONOLITH.read_text(encoding='utf-8')
original_bytes = len(s.encode('utf-8'))
if original_bytes < MIN_MONOLITH_BYTES:
    raise SystemExit(
        f'refusing seam surgery into truncated ErdosTernary2.lean: {original_bytes} bytes'
    )

if IMPORT not in s:
    anchor = 'import Mathlib.Tactic.Ring\n'
    if anchor not in s:
        raise SystemExit('import anchor not found')
    s = s.replace(anchor, anchor + IMPORT, 1)

# These two incidence modules were experimental side branches.  The production
# monolith does not reference their API, while PhaseIncidence reaches the old
# GSTHandwrittenPrefixOneLivePackage whose statements depend back on symbols
# declared inside this monolith.  Keeping those imports therefore creates an
# impossible circular module boundary.  The exact U2D collision replacement
# does not use either incidence layer, so remove only these two stale imports.
removed_stale_imports = 0
for stale_import in STALE_UNUSED_IMPORTS:
    count = s.count(stale_import)
    if count != 1:
        raise SystemExit(
            f'expected exactly one stale incidence import {stale_import.strip()!r}, found {count}'
        )
    s = s.replace(stale_import, '', 1)
    removed_stale_imports += 1

if s.count(TARGET) != 1:
    raise SystemExit(f'expected exactly one production theorem start, found {s.count(TARGET)}')
if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in s:
    raise SystemExit('U2D collision helper already exists before atomic transplant')

packet_marker_re = re.compile(r'(?m)^-- (?:BEGIN|END) ATTACHED [^\n]+$')
packet_markers_before = packet_marker_re.findall(s)

start = s.index(TARGET)
end = s.find(TARGET_END, start)
if end < 0:
    raise SystemExit('production theorem end marker not found')

helpers = extract_green_helpers()

target_replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad
'''

s2 = s[:start] + helpers + target_replacement + s[end:]

if s2.count(TARGET) != 1:
    raise SystemExit('post-surgery target theorem multiplicity check failed')
if s2.count('theorem gst_prefix_one_u2d_atomic_collision_inline') != 1:
    raise SystemExit('post-surgery U2D collision theorem multiplicity check failed')
public_lift_count = len(re.findall(r'(?m)^theorem gst_prefix_one_navigation_lift\b', s2))
if public_lift_count != 1:
    raise SystemExit(f'public prefix-one theorem multiplicity changed: {public_lift_count}')
if packet_marker_re.findall(s2) != packet_markers_before:
    raise SystemExit('historical attached-packet structure changed')
for stale_import in STALE_UNUSED_IMPORTS:
    if stale_import in s2:
        raise SystemExit(f'stale circular import survived: {stale_import.strip()}')

new_target = s2.index(TARGET)
new_end = s2.find(TARGET_END, new_target)
region = s2[new_target:new_end]
if re.search(r'(?m)^\s*gst_end\s*$', region):
    raise SystemExit('gst_end survived target theorem surgery')
if 'gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad' not in region:
    raise SystemExit('minimal U2D collision application missing from target theorem')
for forbidden in (
    'trace_state',
    'contradiction',
    'GSTResidualBoundary',
    'gst_prefix_one_bigN_future_zero_inline',
    'let r := v3 n',
):
    if forbidden in region:
        raise SystemExit(f'legacy proof path survived target theorem: {forbidden}')

MONOLITH.write_text(s2, encoding='utf-8')
written = MONOLITH.read_text(encoding='utf-8')
if written != s2:
    raise SystemExit('post-write monolith integrity check failed')

print(f'ATOMIC_INPUT_BYTES={original_bytes}')
print(f'ATOMIC_OUTPUT_BYTES={len(written.encode("utf-8"))}')
print('ATOMIC_GREEN_HELPERS=3')
print('ATOMIC_TARGET_SIGNATURE_PRESERVED=1')
print('ATOMIC_PUBLIC_LIFT_MULTIPLICITY=1')
print(f'ATOMIC_STALE_CIRCULAR_IMPORTS_REMOVED={removed_stale_imports}')
print('ATOMIC_SURGERY=U2D_HELPERS_PLUS_ONE_THEOREM_BODY')
for i, line in enumerate(written.splitlines(), 1):
    if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in line:
        print(f'ATOMIC_COLLISION_START={i}')
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'ATOMIC_TARGET_START={i}')
