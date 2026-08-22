#!/usr/bin/env python3
"""Replace the unique monolith red-seam `gst_end` with an explicit proof.

The script is intentionally exact: it refuses to run unless the expected seam
occurs exactly once.  It never touches historical snapshots.
"""

from pathlib import Path

path = Path("ErdosTernary2.lean")
text = path.read_text(encoding="utf-8")

old = """  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the\n  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,\n  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.\n  gst_end\n"""

new = """  -- EXPLICIT RED-SEAM CLOSURE.  The v3 factorization has reduced the child\n  -- to a 3-free residual origin.  The already kernel-certified residual lift\n  -- therefore constructs the exact parent witness, contradicting hnoParent.\n  have hchildCoreK :\n      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by\n    simpa [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchildCore\n  have hparentCore :\n      GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) :=\n    gst_residual_navigation_lift s k m hs hk hm hm3 hclosed hchildCoreK\n  apply hnoParent\n  rw [hparentArg]\n  exact hparentCore\n"""

count = text.count(old)
if count == 0 and "EXPLICIT RED-SEAM CLOSURE" in text:
    print("red seam already explicit; no change")
    raise SystemExit(0)
if count != 1:
    raise SystemExit(f"expected exactly one red seam, found {count}")

text = text.replace(old, new)
path.write_text(text, encoding="utf-8")
print("replaced unique gst_end red seam with explicit residual-lift proof")
