#!/usr/bin/env python3
"""fix_mechanical.py — Fix ALL mechanical errors in the patched ErdosTernary2.lean
Run AFTER apply.py. Fixes: Summation notation, dvd_add, dvd_pow_self, hC2,
unfold, mod_add_div, gstSixUniversePrefixS decide, standalone decide.
"""
import re
from pathlib import Path

p = Path('ErdosTernary2.lean')
text = p.read_text(encoding='utf-8')

# 1. Replace ALL unicode summation with Finset.sum
# Pattern: VAR in Finset.range EXPR, BODY
# Use a simple approach: find all occurrences of the unicode char and replace
SUM_CHAR = '\u2211'  # the actual unicode character

# Split by lines and process
lines = text.split('\n')
new_lines = []
for line in lines:
    if SUM_CHAR in line:
        # Replace the summation pattern
        # Pattern: SUM VAR in Finset.range EXPR, BODY
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

# 8. Replace standalone decide ONLY in the inlined modules (after BEGIN ATTACHED)
# The original file's decide calls (before BEGIN ATTACHED) work fine — they
# prove simple Nat equalities with native Decidable instances.
# The inlined modules' decide calls need replacement because they reference
# custom defs (GSTBadPairS, etc.) that don't have Decidable without open scoped Classical.
attached_marker = '-- BEGIN ATTACHED'
if attached_marker in text:
    parts = text.split(attached_marker, 1)
    before = parts[0]  # original file (keep decide as-is)
    after = attached_marker + parts[1]  # inlined modules (replace decide)
    
    lines = after.split('\n')
    new_lines = []
    for line in lines:
        stripped = line.strip()
        if stripped == 'decide':
            indent = len(line) - len(line.lstrip())
            new_lines.append(' ' * indent + 'simp only [GSTBadPairS, gstHandwrittenUChargeS, gstStepCarryS, gstHandwrittenUJumpS, gstBinaryBridgeOutputS, gstBinaryBridgeMassS, gstBinaryBridgeEventS, gstFirstMicroMassS, gstSecondMicroMassS, gstFirstMicroOutputS, gstSecondMicroOutputS, gstMicroHighBitS, gstMicroLowBitS, gstSixUniversePrefixS, gstLocalRotateS, gstMicroRotate6S, gstV2SpaceChargeS, gstBinarySpaceChargeS, gstMicroEventSymbolS, gstMicroTwoIndicatorS, gstMicroKernelTwiceS, gstMicroBig2FluxS, gstHandwrittenXCoordS, gstHandwrittenZOrientS, gstOutputDigitS, gstMicroBig2ActiveS, gstResidualNullTerminalS, gstNavigationConstant, gstDigit, gstCarry, gstDigitS, gstCarryS, gstAffineMulCarryS, gstStepCarryS, GSTSeededHappyS, GSTSeededBadTraceS, ternaryOriginDigitS, InfiniteTernarySupportS, GSTOmegaGatePolynomial, gstOmega, GSTCanonicalBlockS, gstCanonicalPrefixOffsetS, GSTHardPrefixOneTailS, gstPrefixOneUPotentialTailS] <;> omega')
        else:
            new_lines.append(line)
    text = before + '\n'.join(new_lines)

p.write_text(text, encoding='utf-8')
print("fix_mechanical.py: ALL mechanical fixes applied")
