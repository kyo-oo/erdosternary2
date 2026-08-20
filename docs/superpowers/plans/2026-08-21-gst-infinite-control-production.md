# GST Infinite-Control Production Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the old `h_creation_for_4pow` / duality / residual-Ω production seam with a kernel-checked all-Nat GST V2 infinite-control collision and make the repository comparator print `Your solution is okay!`.

**Architecture:** Promote the strongest existing GST V2 all-depth conservation and finite-origin collision machinery into a production-facing core, then prove a prefix-one collision theorem that preserves origin information instead of terminating it. `ErdosTernary2.lean` becomes a consumer of that theorem; old Ω-termination and quarantined creation machinery are not repaired or reintroduced.

**Tech Stack:** Lean 4, Mathlib, GitHub Actions, repository comparator scripts.

**Spec:** `docs/superpowers/specs/2026-08-21-gst-infinite-control-production-design.md`

## Global Constraints

- Work on `sol/gpt56-infinite-control-production`, never directly on `main`.
- Do not use quarantined `h_creation_for_4pow` as a production dependency.
- Do not use old residual Ω termination as a production dependency.
- No `sorry`, `admit`, `sorryAx`, custom axioms, or universal `native_decide` escape.
- Preserve exact origin information (offset, multiplier, seed, and conserved energy) through recursion.
- Verification is incomplete until `scripts/comparator.sh` prints exactly `Your solution is okay!` on a fresh run.

---

### Task 1: Establish the RED production seam

**Files:**
- Create: `GSTInfiniteControlProductionSmoke.lean`
- Read: `ErdosTernary2.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/RetainedOffsetUStateScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/ResidualNullTerminalScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/ResidualNullPrefixFourCutScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/CanonicalResidualInfiniteSupportBridgeScratch.lean`

**Interfaces:**
- Consumes: `GSTNavigationWitness`, `gstNavigationConstant`, `GSTOmegaInfiniteBadTrace`, retained-offset recursion, NULL terminal/cut lemmas.
- Produces: a smoke theorem with the exact desired signature of `gst_v2_infinite_prefix_one_collision` or its residual infinite-support bridge.

- [ ] **Step 1: Write the failing smoke theorem**

Create a minimal theorem that imports the strongest existing V2 modules and asks Lean for the exact production seam without adding proof code. The expected RED is the missing collision/bridge proof, not an import/name error.

- [ ] **Step 2: Run the smoke in GitHub Actions**

Run `lake env lean GSTInfiniteControlProductionSmoke.lean` in a dedicated workflow.

Expected: FAIL at the body of the new bridge/collision theorem while all imported exact V2 modules elaborate.

- [ ] **Step 3: Record the exact remaining hypotheses/state**

Use the compiler error and source signatures to choose the smallest sufficient retained-state invariant. Do not weaken the target to a fixed finite depth.

- [ ] **Step 4: Commit the RED smoke**

Commit message: `test: expose infinite-control production seam`.

---

### Task 2: Promote the all-Nat production control interface

**Files:**
- Create: `GSTInfiniteControlProduction.lean`
- Modify: `GSTInfiniteControlProductionSmoke.lean`

**Interfaces:**
- Consumes: kernel-checked V2 Omega Past/Future conservation, Pi/U conservation, cardinal-world equations, six-world finite-origin collision, BIG-N horizon control, retained offset state.
- Produces: production-facing structures/lemmas that package existing exact invariants without adding axioms.

- [ ] **Step 1: Add a smoke assertion for the packaged controller**

The smoke should construct the production controller for arbitrary natural depth `K` from existing exact V2 theorems.

- [ ] **Step 2: Verify the smoke fails because the production wrapper is absent**

Run `lake env lean GSTInfiniteControlProductionSmoke.lean`.

- [ ] **Step 3: Implement only definitional/derived wrappers**

Create `GSTInfiniteControlProduction.lean`. The wrapper must preserve all-Nat quantification and expose exact conservation equations; it must not introduce a new unproved `Prop` as a substitute for the missing bridge.

- [ ] **Step 4: Verify the wrapper smoke passes and print axioms**

Run `lake env lean GSTInfiniteControlProductionSmoke.lean` and add `#print axioms` for each promoted theorem.

Expected: PASS, with no `sorryAx`.

- [ ] **Step 5: Commit**

Commit message: `feat: promote GST V2 infinite-control core`.

---

### Task 3: Prove the canonical residual infinite-support bridge

**Files:**
- Create: `GSTInfinitePrefixOneCollision.lean`
- Modify: `GSTInfiniteControlProductionSmoke.lean`

**Interfaces:**
- Consumes: retained-state step, NULL-origin terminal contradiction, prefix-four cut, n%3=2 CREATE/origin recurrence, child Navigation witness, production all-Nat controller.
- Produces:

```lean
theorem gst_canonical_residual_infinite_support_bridge
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) :
    InfiniteTernarySupportS n
```

- [ ] **Step 1: Make the smoke call the bridge**

Expected RED: unknown theorem or unsolved proof body.

- [ ] **Step 2: Implement a retained-state arbitrary-cutoff induction**

For arbitrary cutoff `K`, repeatedly transport the exact retained state through the origin digit recursion. Each step must preserve the affine word equality, bad suffix, and conserved U-origin energy. Use the existing NULL terminal theorem to rule out finite exhaustion, prefix-four cut to eliminate the known NULL cylinder, and exact CREATE recursion for residue 2. The induction output must be `∃ j, K ≤ j ∧ gstDigitS n j ≠ 0`, not a fixed witness.

- [ ] **Step 3: Verify both residue branches**

Run dedicated smoke cases for `n % 3 = 1` and `n % 3 = 2`; neither may invoke residual Ω termination.

- [ ] **Step 4: Run `#print axioms gst_canonical_residual_infinite_support_bridge`**

Expected: no `sorryAx` and no custom axioms.

- [ ] **Step 5: Commit**

Commit message: `feat: force infinite residual origin support`.

---

### Task 4: Close the prefix-one collision with finite-origin incompatibility

**Files:**
- Modify: `GSTInfinitePrefixOneCollision.lean`
- Modify: `GSTInfiniteControlProductionSmoke.lean`

**Interfaces:**
- Consumes: `gst_canonical_residual_infinite_support_bridge`, finite natural support theorem, prefix-one bad-trace construction.
- Produces:

```lean
theorem gst_v2_infinite_prefix_one_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False
```

- [ ] **Step 1: Write the smoke call to the collision theorem**

- [ ] **Step 2: Split the residual divisibility cases exactly**

Use the live prefix-one domain facts to discharge/transform the `n % 3 = 0` case and invoke the residual bridge on `n % 3 ≠ 0`. The final contradiction must be between infinite support/control and finite natural realization, not a terminal Ω theorem.

- [ ] **Step 3: Run smoke and `#print axioms`**

Expected: PASS, no `sorryAx`.

- [ ] **Step 4: Commit**

Commit message: `feat: close prefix-one via infinite-control collision`.

---

### Task 5: Replace the old monolith proof seam

**Files:**
- Modify: `ErdosTernary2.lean`
- Modify or remove from active dependency path: legacy residual Ω declarations as necessary.

**Interfaces:**
- Consumes: `gst_v2_infinite_prefix_one_collision`.
- Produces: `gst_prefix_one_navigation_lift` whose contradiction body no longer calls `gst_residual_omega_termination`; downstream residual navigation is reconstructed through the new prefix-one theorem.

- [ ] **Step 1: Add the new production imports**

Import the new modules without changing theorem bodies yet.

- [ ] **Step 2: Verify current monolith still has the known legacy failure/dependency**

Run `lake env lean ErdosTernary2.lean` or the dedicated Action and capture the exact RED.

- [ ] **Step 3: Replace only the contradiction body**

Use:

```lean
by_contra hnoParent
have hBad :=
  gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
exact gst_v2_infinite_prefix_one_collision s n hs hn hchild hBad
```

Adjust only to exact live theorem signatures.

- [ ] **Step 4: Redirect residual consumers**

Ensure downstream construction uses `gst_residual_navigation_lift_of_prefix_one gst_prefix_one_navigation_lift` (or its exact live equivalent), with no production call to residual Ω termination.

- [ ] **Step 5: Verify monolith elaborates**

Run `lake env lean ErdosTernary2.lean`.

- [ ] **Step 6: Commit**

Commit message: `refactor: replace legacy Omega seam with infinite control`.

---

### Task 6: Delete the old direct-bypass error path from CI

**Files:**
- Modify: `.github/workflows/repair_finish_ci.yml`
- Modify/remove diagnostic-only `.github/workflows/direct_induction_smoke.yml` if it still targets `h_creation_for_4pow`.

**Interfaces:**
- Consumes: production monolith.
- Produces: CI that verifies the new source directly rather than truncating and appending the old direct-induction proof.

- [ ] **Step 1: Change CI to compile the checked-in production source**

Remove the runner behavior that truncates at `gst_omega_termination_s1` and appends a theorem requiring `h_creation_for_4pow`.

- [ ] **Step 2: Run the workflow**

Expected: no `Unknown identifier h_creation_for_4pow` because that theorem is no longer part of the production path.

- [ ] **Step 3: Commit**

Commit message: `ci: verify infinite-control production proof`.

---

### Task 7: Full verification and comparator gate

**Files:**
- No proof changes unless a verification failure identifies a genuine defect.

**Interfaces:**
- Consumes: completed production branch.
- Produces: fresh, externally visible verification evidence.

- [ ] **Step 1: Run Lean module checks**

Run:

```bash
lake env lean GSTInfiniteControlProduction.lean
lake env lean GSTInfinitePrefixOneCollision.lean
lake env lean ErdosTernary2.lean
```

Expected: all PASS.

- [ ] **Step 2: Run repository build**

```bash
lake build
```

Expected: PASS.

- [ ] **Step 3: Run sorry check**

```bash
bash scripts/sorry_check.sh
```

Expected: PASS with no forbidden proof placeholders.

- [ ] **Step 4: Run comparator**

```bash
bash scripts/comparator.sh
```

Expected exact line:

```text
Your solution is okay!
```

- [ ] **Step 5: Inspect final theorem axioms**

`#print axioms` for the new bridge, collision theorem, prefix-one lift, and final universal theorem must contain no `sorryAx` or project-created axiom.

- [ ] **Step 6: Commit any verification-only workflow cleanup**

Commit message: `test: verify infinite-control proof end to end`.
