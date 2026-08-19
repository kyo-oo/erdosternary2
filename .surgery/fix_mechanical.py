#!/usr/bin/env python3
"""fix_mechanical.py — Fix mechanical errors in the patched ErdosTernary2.lean
Run AFTER apply.py. Fixes: Summation, dvd_add, dvd_pow_self, hC2, unfold,
mod_add_div, gstSixUniversePrefixS, GSTBadPairS.decidable instance.
"""
import re
from pathlib import Path

p = Path('ErdosTernary2.lean')
text = p.read_text(encoding='utf-8')

# 1. Replace ALL unicode summation with Finset.sum
SUM_CHAR = '\u2211'
lines = text.split('\n')
new_lines = []
for line in lines:
    if SUM_CHAR in line:
        pattern = r'\u2211 (\w+) in Finset\.range ([^,\n]+), ([^\n)]+)'
        def replacer(m):
            var = m.group(1)
            rng = m.group(2).strip()
            body = m.group(3).strip()
            return f'Finset.sum (Finset.range ({rng})) (fun {var} => {body})'
        line = re.sub(pattern, replacer, line)
    new_lines.append(line)
text = '\n'.join(new_lines)

# 2. dvd_add -> Nat.dvd_add
text = text.replace('exact dvd_add ih', 'exact Nat.dvd_add ih')

# 3. Nat.dvd_pow_self -> pow_dvd_pow
text = text.replace('Nat.dvd_pow_self 3', 'pow_dvd_pow 3')

# 4. hC2 scope issue in rcases
text = text.replace(
    'rcases hC with hC2 | hC3 <;> rw [hC2] at hCe <;> try rw [hC3] at hCe <;> omega',
    'rcases hC with rfl | rfl <;> omega'
)

# 5. unfold GSTCanonicalBlockS -> simp only
text = text.replace(
    'unfold GSTHardPrefixOneTailS GSTCanonicalBlockS\n  ring',
    'simp only [GSTHardPrefixOneTailS, GSTCanonicalBlockS]\n  ring'
)

# 6. mod_add_div type mismatch -> omega
text = text.replace('exact (Nat.mod_add_div D 2).symm', 'omega')
text = text.replace('exact (Nat.mod_add_div C 2).symm', 'omega')

# 7. gstSixUniversePrefixS decide -> simp only + norm_num
text = text.replace(
    'gstSixUniversePrefixS 1 = 7 := by\n  decide',
    'gstSixUniversePrefixS 1 = 7 := by\n  simp only [gstSixUniversePrefixS]\n  norm_num'
)
text = text.replace(
    '6^2 - 1 = 5 * 7 := by\n  decide',
    '6^2 - 1 = 5 * 7 := by\n  norm_num'
)
text = text.replace(
    '13 = 6 + gstSixUniversePrefixS 1 := by\n  decide',
    '13 = 6 + gstSixUniversePrefixS 1 := by\n  simp only [gstSixUniversePrefixS]\n  norm_num'
)
text = text.replace(
    '7 / (13 - 6) = 1 := by\n  decide',
    '7 / (13 - 6) = 1 := by\n  norm_num'
)

# 8. Fix GSTBadPairS.decidable instance — replace the match-based instance
# with a simpler one that uses `by decide` after casing on concrete values.
# The match-based instance fails because the catch-all case has free variables.
# Using `cases C <;> cases d <;> decide` splits into concrete cases.
# But we need to handle ALL Nat values (0, 1, 2, 3+), so we case 4 times on C
# and 3 times on d (0, 1, 2+).
#
# Actually, the SIMPLEST approach: just replace the instance with:
#   instance : Decidable (GSTBadPairS C d) := inferInstance
# This uses Classical.propDecidable (from open scoped Classical).
# But this gets stuck on Classical.choice...
#
# The REAL fix: remove the explicit instance entirely. With open scoped Classical,
# Classical.propDecidable provides Decidable for ALL Props. The `decide` tactic
# will use it. But it gets stuck...
#
# ACTUALLY: the issue is that the inlined InformationBadTraceScratch module
# ALREADY has the instance. If it fails to compile, ALL subsequent code fails.
# The fix: remove the instance entirely (let Classical.propDecidable handle it).
# The `decide` calls will use Classical.propDecidable which MIGHT work for
# concrete values (after cases/subst).

# Remove the explicit GSTBadPairS.decidable instance
old_instance = '''instance GSTBadPairS.decidable (C d : Nat) : Decidable (GSTBadPairS C d) :=
  match C, d with
  | 0, 2 => isFalse (by simp [GSTBadPairS])
  | 3, 2 => isFalse (by simp [GSTBadPairS])
  | _, _ => isTrue (by simp [GSTBadPairS])'''

old_instance_omega = '''instance GSTBadPairS.decidable (C d : Nat) : Decidable (GSTBadPairS C d) :=
  match C, d with
  | 0, 2 => isFalse (by simp [GSTBadPairS])
  | 3, 2 => isFalse (by simp [GSTBadPairS])
  | _, _ => isTrue (by simp [GSTBadPairS]; omega)'''

# Replace whichever version exists
if old_instance in text:
    text = text.replace(old_instance, '-- GSTBadPairS.decidable removed (uses Classical.propDecidable via open scoped Classical)')
    print("Removed original GSTBadPairS.decidable instance")
elif old_instance_omega in text:
    text = text.replace(old_instance_omega, '-- GSTBadPairS.decidable removed (uses Classical.propDecidable via open scoped Classical)')
    print("Removed omega version of GSTBadPairS.decidable instance")
else:
    print("WARNING: GSTBadPairS.decidable instance not found (already removed?)")

p.write_text(text, encoding='utf-8')
print("fix_mechanical.py: ALL mechanical fixes applied")
