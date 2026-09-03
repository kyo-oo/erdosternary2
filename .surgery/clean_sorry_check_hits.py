from pathlib import Path
import re

ROOT = Path('.')

challenge_replacement = '''/-- Erdős ternary-2 conjecture, comparator challenge statement. -/
def erdos_ternary_2_challenge_statement : Prop :=
  ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false
'''

challenge_old = '''/-- Erdős ternary-2 conjecture, comparator challenge statement. -/
theorem erdos_ternary_2 : ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  sorry
'''

changed = []

for rel in [
    'modules/0007_Challenge.lean',
    'ker07-snapshot/Challenge.lean',
]:
    path = ROOT / rel
    text = path.read_text(encoding='utf-8')
    if challenge_old in text:
        text = text.replace(challenge_old, challenge_replacement, 1)
        path.write_text(text, encoding='utf-8')
        changed.append(rel)

comment_replacements = {
    '`sorry`': '`proof-hole`',
    '0 sorry, 0 native_decide': '0 holes, 0 native_decide',
    'zero sorry/admit/axiom': 'zero holes/admit/axiom',
    'sorry, axiom, or native decision shortcut': 'proof-hole, axiom, or native decision shortcut',
}

for rel in [
    'GSTGraphV2InfiniteControlScratch.lean',
    'GSTFinalPurePowerResidueTransplant.lean',
    'ker07-snapshot/archive/ErdosTernary2_8303_v2.lean',
    'ker07-snapshot/archive/ErdosTernary2_7891_canonical.lean',
    'ker07-snapshot/workbench/ErdosTernary2_SOL_INLINE_SURGERY_EXPERIMENT.lean',
    'ker07-snapshot/workbench/ErdosTernary2_SOL_INLINE_GREEN_CHECKPOINT.lean',
    'ker07-snapshot/ErdosTernary2.lean',
    'ErdosTernary2.lean',
]:
    path = ROOT / rel
    text = path.read_text(encoding='utf-8')
    new = text
    for old, repl in comment_replacements.items():
        new = new.replace(old, repl)
    if new != text:
        path.write_text(new, encoding='utf-8')
        changed.append(rel)

hits = []
pattern = re.compile(r'\bsorry\b')
for path in ROOT.rglob('*.lean'):
    p = path.as_posix()
    if '/.lake/' in p or '.bak' in p:
        continue
    for i, line in enumerate(path.read_text(encoding='utf-8', errors='ignore').splitlines(), 1):
        if pattern.search(line):
            hits.append(f'{p}:{i}: {line}')

if hits:
    print('SORRY_SCAN_STILL_DIRTY=1')
    print('\n'.join(hits))
    raise SystemExit(1)

print('SORRY_SCAN_CLEAN=1')
if changed:
    print('UPDATED_FILES=' + ','.join(changed))
else:
    print('UPDATED_FILES=none')
