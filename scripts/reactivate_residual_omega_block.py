#!/usr/bin/env python3
from pathlib import Path

PATH = Path('ErdosTernary2.lean')
START = '/- QUARANTINED LEGACY RESIDUAL OMEGA START'
END = 'QUARANTINED LEGACY RESIDUAL OMEGA END -/'

s = PATH.read_text(encoding='utf-8')

if s.count(START) != 1:
    raise SystemExit(f'expected exactly one residual Omega quarantine start, found {s.count(START)}')
if s.count(END) != 1:
    raise SystemExit(f'expected exactly one residual Omega quarantine end, found {s.count(END)}')

s = s.replace(START, '-- REACTIVATED RESIDUAL OMEGA START', 1)
s = s.replace(END, '-- REACTIVATED RESIDUAL OMEGA END', 1)

if START in s or END in s:
    raise SystemExit('residual Omega quarantine marker survived reactivation')

# The point of this probe is to expose the actual theorem to Lean, not merely
# make its name visible in commented source.
needle = 'theorem gst_residual_navigation_lift : GSTResidualNavigationLift :='
if s.count(needle) != 1:
    raise SystemExit(f'expected exactly one residual navigation theorem after reactivation, found {s.count(needle)}')

PATH.write_text(s, encoding='utf-8')
print('RESIDUAL_OMEGA_REACTIVATED=1')
