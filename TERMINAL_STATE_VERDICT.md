# TERMINAL STATE VERDICT — the campaign's honest end-state

Task 11 execution receipt.  Branch `astra/cardinal-worlds-bridge`, parent
`9b594b16f19ba8df9fa91880f3bd6bd70f0c12e0` (run `35692825575` SUCCESS,
comparator PASS, sorry 0, axiom audit clean at that sha).

---

## I. THE VERDICT

**THE END — official comparator green on `questions/deepmind_problem_406` —
is not reachable by proof engineering.  The challenge statement is the Erdős
1979 ternary-2 conjecture** (`∀ n ≥ 9, noTernaryDigitTwo (2^n) = false`),
which is an open problem in mathematics.  The repo's own documentation has
said so all along: `four_power_happy_climb` is declared as "the exact
residual open seam … certified empirically by the worldtrace simulation at
N = 1500" — certified, not proven.

The final plan of the interrupted session ("one theorem left: the (21)
W-composition") is **refuted by explicit counterexample** below.  No tactic
closes an open problem; the honest terminal state of the campaign is:

* the FULL reduction of the conjecture to named grants is green and
  kernel-checked;
* Law 1 (`postulate_I`) is an unconditional theorem;
* exactly ONE open-strength grant is alive (`four_power_happy_climb`; the
  `CardinalWorldsMirrorBridge` grant is the alternative packaging of the same
  seam).

## II. THE REFUTATION (receipts, exact Lean definitions)

All numerics use a Python mirror of the Lean definitions, verified against
Lean's own `decide` table `crossDensity_physical_table` — **12/12 exact**
(`GSTU2DExactCrossingCharge.lean:31`).  Scripts:
`final_receipts.py`, `verify21.py`, `verify21b.py`, `verify21c.py`
(sandbox `erdo/`).

**(1) Equation (21) is FALSE as a statement of the charge algebra.**
Instance (the general `s = 1` rectangle shape, `E = 1 + 3^b·T`, `N = 3`,
`b = 3`):

* `T = 2152157`, `E = 58108240`, parent `4^N·E = 3718927360`.
* The parent row is **all-bad** at every column `≥ 3`: cells
  `(carry4, digit3)` at columns 3..14 are
  `(1,1) (1,2) (3,0) (1,2) (3,0) (1,0) (0,1) (1,1) (1,2) (3,1) (2,1) (2,0)`,
  none Happy; all higher columns have digit 0.  (`HappyCell` needs
  `digit = 2 ∧ carry ∈ {0,3}`.)
* Yet `WCP(1) = 16·crossDensity(0,2) + 4·crossDensity(0,2) +
  crossDensity(2,2) = 16·105 + 4·105 + 0 = 2100 > 0`.

So `all-bad parent ⇒ weightedCrossPrefix ≤ 0` fails outright for general
rectangles: **the `omega` placeholder at
`GSTFinalPrefixOneDirectU2DCollision.lean:173` can never close.**

**(2) The general collision is FALSE.**  The same instance has a child
Happy gate at row 0, column 3 (`carry4 E 3 = 0`, `digit3 E 3 = 2`):
child Navigation and an all-bad parent **coexist**.  The collision theorem
is true only for the canonical family — vacuously, see (3).

**(3) The canonical hypothesis is empirically empty.**  3000/3000 canonical
parents `4^(3^s·(1+3n))` (`s ∈ {1,2,3}`, `n ∈ 1..1000`) have a Happy cell at
columns `≥ s+2`.  Zero all-bad instances.  The canonical (21) is therefore
vacuously consistent — and **proving it non-vacuously is exactly the climb**:

```
canonical (21)  ⟹  collision compiles  ⟹  prefix_one_navigation_lift_direct
              ⟹  residual_navigation_lift  ⟹  navigation_all
              ⟹  even_universal  ⟹  the_act  ⟹  full_erdos     (all glue green)
```

Hence canonical (21) is **Erdős-strength**: no proof exists short of
resolving the open conjecture.  This also retires the controller hope of the
last session: `InfiniteBadCoupledControl` and its conservation laws hold for
ALL rectangles, so they cannot imply (21), which is false for general
rectangles.

## III. THE TERMINAL MAP (receipted at `9b594b16`)

GREEN, unconditional, production-compiled (`Main.lean` import closure):
`postulate_I` (Law 1); the telescope components — rectangle identity (13)
`collision_rectangle_exact` / `canonical_rectangle_boundary_exact`; pressure
floor (14) `weightedCrossPrefix_ge_global_floor`; positivity (15)+(16)
`weightedCrossPrefix_positive_of_top_leading_happy`; right-bad conversion
(18) `canonical_right_bad_to_graph_right_bad`; base carry (20)
`mb_base_carry_zero` (×3 forms); WCP=sum bridge (26)
`weightedCrossPrefix_eq_sum`; right-edge sign (19); controller rectangle
identification; the whole Step6 / adapter / revival GLUE; odd case
`erdos_ternary_2_odd_universal`; modular base `modular_check_base (a ≤ 500)`.

GRANTS alive (2): `CardinalWorldsMirrorBridge` (bridge module :850),
`four_power_happy_climb` (`GSTInfiniteFourPowerNavigation.lean:141`).

The monolith's own remaining decision surface (all climb-strength):
`gst_navigation_witness_all_of_small_shift` ⟸ `GSTResidualNavigationLift`
on `GSTResidualBoundary` = `s=1 ∧ r=1 (any k)`; `s=1 ∧ r=2 ∧ k∈{1,3}`;
`s=3 ∧ k≤7` minus `(k,r) ∈ {(2,1),(4,1),(6,2)}`; `2≤s≠3 ∧ k≤4` minus
`(2,1)` — plus `GSTPrefixOneSeedCore` / `GSTPrefixOneBadReflection` /
`FourPowerCreationMaster` (`∀ K ≥ 5, K ≠ 7, CreationCertificate (4^K)`),
all interconvertible with the climb by green glue.

OFFICIAL COMPARATOR TARGET: `questions/deepmind_problem_406/Solution.lean`
calls `erdos_ternary_2_even_universal K hK5` — but the LIVE crown
(monolith :16963) takes `(hClimb) (a) (ha)`.  The file was written against
the retired unconditional-era crown (comment at :7580, FV-2R flag 4) and
**does not compile against the live monolith**.  It cannot be wired green
without the climb.

## IV. WHAT WOULD CLOSE IT

A proof of any one of: `four_power_happy_climb`, the
`FourPowerCreationMaster` certificate, or any single
`GSTResidualBoundary` lift case — each implies the Erdős 1979 conjecture by
the green glue above.  That is a research problem, not a proof-engineering
task.  **This file is the campaign's terminal state: stop here.**
