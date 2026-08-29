#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

creation_marker = 'theorem h_creation_for_4pow'
helper_marker = 'theorem gst_h_creation_full_power_navigation_atomic'
helper_next = 'theorem gst_full_power_navigation_descends_atomic'
live_stamp = '-- SOL56 LIVE GENERAL H_CREATION REACTIVATED\n'
reuse_stamp = '-- Existing certified declaration reused; no duplicate strong-recursion wrapper.\n'

creation_start = s.index(creation_marker)
helper_start = s.index(helper_marker)
helper_end = s.index(helper_next, helper_start)

if creation_start >= helper_start:
    raise SystemExit('certified h_creation_for_4pow must precede the atomic adapter')

helper = s[helper_start:helper_end]
required_call = 'h_creation_for_4pow k hk5 hk7'
if required_call not in helper:
    raise SystemExit('atomic adapter no longer consumes h_creation_for_4pow')
if 'hCreationCheck_univ k hk7' in helper:
    raise SystemExit('bounded hCreationCheck shortcut survived in atomic adapter')

# The former surgery duplicated h_creation_for_4pow and wrapped its exact
# proposition in a second strong-recursion motive.  At the adapter call this
# elaborated as P -> P.  Reuse the already-compiled declaration instead.
if live_stamp not in s:
    s = s[:helper_start] + live_stamp + reuse_stamp + s[helper_start:]
    helper_start = s.index(helper_marker)
    helper_end = s.index(helper_next, helper_start)

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
live_helper = s[helper_start:helper_end]
if helper_old in live_helper:
    s = s[:helper_start] + live_helper.replace(helper_old, helper_new, 1) + s[helper_end:]
elif 'rw [hC, hdDigit] at hnext' not in live_helper:
    raise SystemExit('atomic carry-one adapter rewrite shape changed')

if s.count(creation_marker) != 1:
    raise SystemExit('h_creation_for_4pow must remain a single declaration')
helper_start = s.index(helper_marker)
helper_end = s.index(helper_next, helper_start)
if required_call not in s[helper_start:helper_end]:
    raise SystemExit('unbounded creation adapter call was lost')
if 'Nat.strongRecOn (motive := fun k =>' in s[helper_start:helper_end]:
    raise SystemExit('duplicate strong-recursion wrapper survived in adapter')

p.write_text(s, encoding='utf-8')
print('FULL_H_CREATION_ALREADY_AVAILABLE=1')
print('DUPLICATE_STRONG_RECURSION_WRAPPER_REMOVED=1')
print('GSTDIGIT_RC2_REPAIR=1')
print('UNBOUNDED_U2D_CREATION_ADAPTER_PRESERVED=1')
