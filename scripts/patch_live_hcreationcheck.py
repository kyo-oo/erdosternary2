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

# Keep the already-proved universal adapter contract exactly as restored by the
# historical U2D generator.  The previous bounded hCreationCheck shortcut is
# intentionally forbidden here because the collision exponent K is unbounded.
required_call = 'h_creation_for_4pow k hk5 hk7'
if required_call not in helper:
    raise SystemExit('universal h_creation_for_4pow adapter call is not intact')
if 'hCreationCheck_univ k hk7' in helper:
    raise SystemExit('bounded hCreationCheck shortcut survived in U2D helper')

# Production retains the complete general theorem inside the quarantined legacy
# block.  Lift that exact theorem text out of quarantine and place one live copy
# immediately before the U2D helper.  Do not rewrite its proof.
qstart = s.index(creation_marker)
qend = s.index(next_marker, qstart)
if qstart >= helper_start:
    raise SystemExit('expected quarantined h_creation theorem before U2D helper')
creation_decl = s[qstart:qend].rstrip() + '\n\n'
if not creation_decl.startswith(creation_marker):
    raise SystemExit('h_creation extraction boundary changed')
if creation_decl.count(creation_marker) != 1:
    raise SystemExit('h_creation extraction multiplicity changed')

# Guard against accidental double activation if this patcher is invoked twice.
live_stamp = '-- SOL56 LIVE GENERAL H_CREATION REACTIVATED\n'
if live_stamp in s:
    print('FULL_H_CREATION_ALREADY_REACTIVATED=1')
    p.write_text(s, encoding='utf-8')
    raise SystemExit(0)

s = s[:helper_start] + live_stamp + creation_decl + s[helper_start:]

# Exactly one live copy sits after the explicit stamp; the original textual copy
# remains quarantined for archaeology.
live_start = s.index(live_stamp) + len(live_stamp)
live_helper = s.index(helper_marker, live_start)
live_slice = s[live_start:live_helper]
if live_slice.count(creation_marker) != 1:
    raise SystemExit('expected exactly one reactivated live h_creation theorem')
if required_call not in s[live_helper:s.index(helper_next, live_helper)]:
    raise SystemExit('U2D helper no longer consumes general h_creation theorem')

p.write_text(s, encoding='utf-8')
print('FULL_H_CREATION_REACTIVATED=1')
print('UNBOUNDED_U2D_CREATION_ADAPTER_PRESERVED=1')
