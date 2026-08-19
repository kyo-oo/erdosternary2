#!/usr/bin/env python3
"""fix_mechanical.py — Fix mechanical errors in the patched ErdosTernary2.lean
Run AFTER apply.py. With reordered modules, GSTBadPairS + its Decidable instance
are defined BEFORE any decide call. So decide should work as-is.

Only fixes: Summation notation, dvd_add, dvd_pow_self, hC2, unfold,
mod_add_div, gstSixUniversePrefixS decide.
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

# NOTE: Do NOT replace decide — with reordered modules, the Decidable instance
# for GSTBadPairS is defined BEFORE any decide call. decide should work as-is.

p.write_text(text, encoding='utf-8')
print("fix_mechanical.py: mechanical fixes applied (NO decide replacement, NO Decidable instance)")

# 9. Fix the GSTBadPairS.decidable instance body — simp [GSTBadPairS] fails
# to close the isTrue case. Use simp [GSTBadPairS]; omega instead.
text = text.replace(
    '  | 0, 2 => isFalse (by simp [GSTBadPairS])\n  | 3, 2 => isFalse (by simp [GSTBadPairS])\n  | _, _ => isTrue (by simp [GSTBadPairS])',
    '  | 0, 2 => isFalse (by simp [GSTBadPairS])\n  | 3, 2 => isFalse (by simp [GSTBadPairS])\n  | _, _ => isTrue (by simp [GSTBadPairS]; omega)'
)
p.write_text(text, encoding='utf-8')
print("fix_mechanical.py: instance body fixed (simp [GSTBadPairS] → simp [GSTBadPairS]; omega)")
