#!/usr/bin/env python3
"""fix_decidable.py — Add Decidable instance for GSTBadPairS.
Run AFTER apply.py. Uses match (structural recursion, no if-then-else).
"""
from pathlib import Path

p = Path('ErdosTernary2.lean')
text = p.read_text(encoding='utf-8')

old = """def GSTBadPairS (C d : Nat) : Prop :=
  ¬ (d = 2 ∧ (C = 0 ∨ C = 3))"""

new = """def GSTBadPairS (C d : Nat) : Prop :=
  ¬ (d = 2 ∧ (C = 0 ∨ C = 3))

instance : Decidable (GSTBadPairS C d) :=
  match d, C with
  | 2, 0 => isFalse (fun hp => hp ⟨rfl, Or.inl rfl⟩)
  | 2, 3 => isFalse (fun hp => hp ⟨rfl, Or.inr rfl⟩)
  | _, _ => isTrue (fun h => h)"""

if old in text:
    text = text.replace(old, new, 1)
    p.write_text(text, encoding='utf-8')
    print("fix_decidable.py: match-based instance added")
else:
    print("fix_decidable.py: def GSTBadPairS not found")
