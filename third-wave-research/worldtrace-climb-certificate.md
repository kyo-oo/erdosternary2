# Worldtrace Mega-Simulation Certificate — Third-Wave Climb (N=1500)

Simulator: /home/z/agent-work/sim/ (collision_sim.py, climb_law.py, trie_law.py, survivor_tree.py)
Model: exact V2 universe atoms (graph E t p = cell of 4^t*E at ternary col p; carry4, digit3,
phaseDensity, surviveI, gstUCharge/Jump, carryWord — all transcribed from the Lean defs and
identity-verified against the green window/telescope/conservation theorems).

## Verdict
- Climb instances: 1,493 (K = 8..1500, every K owns a Happy row at col >= 3) — FULL COVERAGE
- K = 7: uniquely excluded (no Happy at any col >= 3) — matches the gate's exception
- Base witnesses: K=8 -> col 4, K=9 -> col 7, K=10 -> col 10 — exactly the Lean kernel bases
- K = 5, 6: fire via the mod-9 row-two residue classifier (col < 3), as the FromHappy route designs
- Gate failures in 5..200 excluding 7: NONE (after 5,6 classifier)

## Why the retired collision assembly could not close (simulation-proved)
On live exponents all five of its hypothesis hold SIMULTANEOUSLY:
W0 > 0 (Happy child at window top), W3 <= 0 (bad row-3 window), hU telescope identity,
hWidth3 conservation identity, hUPositive > 0 — consistent on real data. No tactic can
derive False from a consistent set. The all-depth badness (forall j) is required, and the
witness climb is NON-LOCAL (107 FAR cases in K = 8..120: parent witness tunnels through
up to 6+ trie levels; survivor-tree growth ratio ~2.48 < 3).

## The refined seam (consumed explicitly by name in Lean)
four_power_happy_climb : forall K >= 8, exists p >= 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)
