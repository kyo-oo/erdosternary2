# GST V2 Infinite-Control Production Upgrade Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the legacy one-error proof corridor and residual Ω termination dependency with the strongest current GST V2 all-Nat information-control/collision architecture, then obtain a fresh green comparator.

**Architecture:** Promote already kernelized V2 invariants into a one-way production dependency spine: infinite control -> retained information/origin control -> finite-origin collision -> prefix-one navigation -> residual lift -> universal power theorem. The quarantined `h_creation_for_4pow`, legacy Ω termination trio, and foundational use of old `gst_duality` are not repaired; they are bypassed and eventually demoted to compatibility-only code.

**Tech Stack:** Lean 4, Mathlib, GitHub Actions, repository comparator/sorry checks.

**Spec:** `docs/superpowers/specs/2026-08-21-gst-v2-infinite-control-production-design.md`

## Global Constraints

- Work only on branch `sol/gpt56-close-one-error`.
- Do not reactivate quarantined `h_creation_for_4pow`.
- Do not use the legacy residual Ω termination trio in the new production dependency chain.
- Do not introduce `sorry`, `admit`, `sorryAx`, custom axioms, or `native_decide` escapes.
- Treat CREATE/DESTROY as local observational event labels; preserve global information through exact all-depth ledgers.
- Use GitHub Actions as the Lean verification runtime.
- Completion requires a fresh comparator output containing exactly `Your solution is okay!`.

---

### Task 1: Freeze the exact RED seam and dependency map

**Files:**
- Read: `ErdosTernary2.lean`
- Read: `.github/workflows/repair_finish_ci.yml`
- Read: `docs/superpowers/plans/2026-08-20-gst-v2-infinite-production-surgery.md`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/docs/GST_V2_FINAL_BRIDGE_PROOF_CONTRACT.md`

**Interfaces:**
- Consumes: current branch and prior Aug-20 one-error CI evidence.
- Produces: exact theorem seam and list of legacy dependencies to remove.

- [ ] **Step 1:** Confirm the existing direct-bypass RED remains `Unknown identifier h_creation_for_4pow` and record that this workflow is legacy, not the target architecture.
- [ ] **Step 2:** Locate the active `gst_prefix_one_navigation_lift`, `gst_residual_omega_termination`, `gst_residual_navigation_lift_of_prefix_one`, and universal theorem consumers.
- [ ] **Step 3:** Confirm the strongest current scratch interfaces and theorem names needed for the new bridge.

### Task 2: Build a standalone RED smoke for the modern collision seam

**Files:**
- Create: `.github/workflows/gst_v2_infinite_collision_smoke.yml`
- Create or modify only as needed: a generated Lean smoke file inside the workflow workspace.

**Interfaces:**
- Consumes:
  ```lean
  GSTNavigationWitness (gstNavigationConstant (s+1) n)
  GSTOmegaInfiniteBadTrace s 1 n
  ```
- Produces target:
  ```lean
  theorem gst_v2_infinite_prefix_one_collision
      (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
      (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
      (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False
  ```

- [ ] **Step 1:** Write smoke theorem importing only the strongest V2/origin scratch modules plus the monolith interface required for the seam.
- [ ] **Step 2:** Run Actions and verify RED is in the missing bridge logic, not import/name noise.
- [ ] **Step 3:** Add `#print axioms` for every new candidate theorem once it elaborates.

### Task 3: Construct the retained-origin infinite-support bridge

**Files:**
- Promote from/read:
  - `RetainedOffsetUStateScratch.lean`
  - `ResidualNullTerminalScratch.lean`
  - `ResidualNullPrefixFourCutScratch.lean`
  - `PrefixOneOriginPhaseRecursionScratch.lean`
  - `InformationForcingScratch.lean`
  - `GSTGraphV2InfiniteOmegaLedgerMasterScratch.lean`
  - `GSTGraphV2InfiniteNaturalContradictionScratch.lean`
  - `GSTGraphV2InfiniteOriginWorldCollisionScratch.lean`
- Create as focused production module if possible: `GSTInfiniteCollision.lean`

**Interfaces:**
- Produces the concrete bridge (or an equivalent theorem with no abstract assumption):
  ```lean
  theorem gst_canonical_residual_infinite_support_bridge
      (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : n % 3 ≠ 0)
      (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
      (hbad : GSTSeededBadTraceS 1
        (gstCanonicalOffsetS s + gstCanonicalMultiplierS s *
          gstNavigationConstant (s+1) n)) :
      InfiniteTernarySupportS n
  ```
  Exact local names may follow the repo's already-defined offset/multiplier notation.

- [ ] **Step 1:** Reuse exact retained-state step to consume one residual trit while preserving `(offset,multiplier,seed)` and U-origin energy.
- [ ] **Step 2:** Close `n % 3 = 1` terminal case with the kernelized `n = 1` NULL Happy-Gate impossibility, never a terminal-NULL assumption.
- [ ] **Step 3:** Apply the `n ≡ 4 (mod 9), s ≥ 2` position-2 NULL cut to eliminate that cylinder immediately.
- [ ] **Step 4:** Handle the remaining NULL descendants and the `n % 3 = 2` CREATE branch by repeated retained-state/origin descent while preserving the exact outer state.
- [ ] **Step 5:** Convert indefinite avoidance of a Happy Gate into all-depth nonzero origin information (or cofinal six-world synchronization) and invoke the finite-natural support/world collision.
- [ ] **Step 6:** Kernel-check and `#print axioms` the bridge.

### Task 4: Close the direct prefix-one collision

**Files:**
- Create/modify: `GSTInfiniteCollision.lean` or the smallest appropriate production module.
- Update smoke workflow from Task 2.

**Interfaces:**
- Consumes: residual bridge from Task 3 plus existing parent-bad/origin adapter.
- Produces:
  ```lean
  theorem gst_v2_infinite_prefix_one_collision
      (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
      (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
      (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False
  ```

- [ ] **Step 1:** Translate `GSTOmegaInfiniteBadTrace` into the seeded/canonical retained-origin bad trace already used by the scratch adapters.
- [ ] **Step 2:** Establish `n % 3 ≠ 0` from the canonical residual hypotheses available at this seam.
- [ ] **Step 3:** Apply the concrete infinite-support bridge.
- [ ] **Step 4:** Contradict finite natural support.
- [ ] **Step 5:** Run smoke and `#print axioms`; require no `sorryAx`.

### Task 5: Replace the active legacy Ω seam in `ErdosTernary2.lean`

**Files:**
- Modify: `ErdosTernary2.lean`
- Potentially add imports for focused production V2 modules.

**Interfaces:**
- New `gst_prefix_one_navigation_lift` contradiction branch:
  ```lean
  by_contra hnoParent
  have hBad :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_v2_infinite_prefix_one_collision s n hs hn hchild hBad
  ```
- Downstream residual navigation uses:
  ```lean
  gst_residual_navigation_lift_of_prefix_one gst_prefix_one_navigation_lift
  ```

- [ ] **Step 1:** Wire the new collision theorem into `gst_prefix_one_navigation_lift`.
- [ ] **Step 2:** Remove active dependency on `gst_omega_termination_s1`, `gst_omega_termination_s3`, `gst_omega_termination_stable`, and `gst_residual_omega_termination` from the final theorem graph.
- [ ] **Step 3:** Redirect residual construction through `gst_residual_navigation_lift_of_prefix_one`.
- [ ] **Step 4:** Leave obsolete code quarantined/commented until final comparator is green; do not delete useful archaeology prematurely.

### Task 6: Replace the legacy direct-bypass workflow with V2 verification

**Files:**
- Modify or retire: `.github/workflows/repair_finish_ci.yml`
- Modify: `.github/workflows/gst_v2_infinite_collision_smoke.yml`

**Interfaces:**
- Consumes: actual production monolith after Task 5.
- Produces: fresh build/sorry/comparator evidence without synthesizing `h_creation_for_4pow`.

- [ ] **Step 1:** Stop generating a direct-induction theorem that references quarantined `h_creation_for_4pow`.
- [ ] **Step 2:** Run `lake env lean ErdosTernary2.lean`.
- [ ] **Step 3:** Run `lake build`.
- [ ] **Step 4:** Run `bash scripts/sorry_check.sh`.
- [ ] **Step 5:** Run `bash scripts/comparator.sh`.

### Task 7: Final verification and cleanup

**Files:**
- Modify only diagnostics/workflows proven obsolete after green.

**Interfaces:**
- Produces final acceptance evidence.

- [ ] **Step 1:** Fetch the exact GitHub Actions job logs for the production verification commit.
- [ ] **Step 2:** Confirm no `declaration uses 'sorry'`, no `sorryAx` in printed axioms, and no legacy direct-bypass unknown identifier.
- [ ] **Step 3:** Confirm exact output `Your solution is okay!` and `COMPARATOR RESULT: PASS`.
- [ ] **Step 4:** Only after Step 3, remove assistant-only diagnostic workflows that are no longer useful and rerun the comparator if cleanup changes production-relevant files.
