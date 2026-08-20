# GST V2 Infinite Production Surgery Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the active legacy Ω-termination dependency with a kernel-checked exponential/infinite GST Graph V2 prefix-one collision mechanism, then run the real comparator.

**Architecture:** The production proof will no longer prove or consume `GSTResidualOmegaTermination`. Instead, the child Navigation gate plus a hypothetical prefix-one parent bad trace is embedded into the all-Nat V2 controller (Ω information stream, Π/U conservation, base-six world projections, BIG-N horizon, and `I ≠ BIG1` branch control). The new mechanism proves the prefix-one parent cannot stay bad; this gives `GSTPrefixOneNavigationLift`. Existing `gst_residual_navigation_lift_of_prefix_one` then lifts that single theorem to the residual/general Navigation machinery without any Ω-termination theorem.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, GitHub Actions, existing `GSTTactic`, repo comparator `scripts/comparator.sh`.

**Spec:** `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/docs/GST_V2_FINAL_BRIDGE_PROOF_CONTRACT.md`, together with the kernel-green infinite-controller modules in `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/`.

## Global Constraints

- Do not use `sorry`, `admit`, custom axioms, `native_decide`, or a false generic recursion principle.
- Do not use the legacy `gst_omega_termination_s1`, `gst_omega_termination_s3`, `gst_omega_termination_stable`, or `gst_residual_omega_termination` as proof dependencies.
- Do not install Lean locally; verify with GitHub Actions using `leanprover/lean4:v4.33.0-rc2`.
- Do not use web search; repository evidence and connected GitHub are the source of truth.
- Preserve the handwritten semantics: Ω∞ information flow, Π/U conservation, base-six `6^K` worlds, BIG-N as Navigation horizon, and scoped/pathwise `I ≠ BIG1` behavior.
- The actual completion gate is `bash scripts/comparator.sh` returning PASS after the committed monolith compiles.

---

### Task 1: Production-Safe Infinite Controller Layer

**Files:**
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteControlScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteNaturalContradictionScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteNavigationHorizonScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteWorldTowerScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteCardinalMasterScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteElevenEquationMasterScratch.lean`
- Read: `ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery/GSTGraphV2InfiniteOmegaLedgerMasterScratch.lean`
- Create if needed: root-level production modules with the same theorem content but no dependency on `ErdosTernary2`.
- Test: new GitHub Actions smoke workflow dedicated to the V2 production layer.

**Interfaces:**
- Consumes: only Mathlib and already-independent V2 modules.
- Produces: namespace `GSTInfiniteV2` all-scale orbit/control, BIG-N horizon, Π/U ledger, world-tower projections, and natural finite-realization contradiction lemmas.

- [ ] **Step 1: Verify import direction of every selected infinite module.**

Fetch the first 30 lines of each selected file. Reject any module that imports `ErdosTernary2`; production dependencies must point toward the monolith, never back from it.

- [ ] **Step 2: Write a failing production-import smoke.**

Create a workflow that compiles the selected independent modules with the pinned toolchain and then compiles a tiny `V2ProductionImportSmoke.lean` importing exactly the intended production set. The smoke must fail if any import cycle, duplicate declaration, or `sorryAx` appears.

- [ ] **Step 3: Promote only the needed independent modules.**

If normal project `LEAN_PATH` cannot import snapshot files, copy the verified modules to focused root-level files (preserving namespace `GSTInfiniteV2`) and adjust only their import paths. Do not alter theorem statements during promotion.

- [ ] **Step 4: Re-run the production-import smoke.**

Expected: every promoted module compiles under Lean 4.33.0-rc2 and `#print axioms` for the production-facing theorems contains no `sorryAx` or custom axiom.

- [ ] **Step 5: Commit.**

Commit message: `feat: promote infinite GST V2 control layer`.

---

### Task 2: Exponential Prefix-One Collision Adapter

**Files:**
- Modify/test in an isolated generated smoke first: `ErdosPreOmega.lean` plus the production V2 imports.
- Later transplant into: `ErdosTernary2.lean`.
- Reference: `CanonicalCausalityScratch.lean`, `CanonicalOriginCutIntersectionScratch.lean`, `RetainedOffsetUStateScratch.lean`, `RightChordCanonicalGateScratch.lean`, and the all-scale V2 production modules.

**Interfaces:**
- Consumes: `GSTNavigationWitness (gstNavigationConstant (s+1) n)`, `GSTOmegaInfiniteBadTrace s 1 n`, exact child gate data, and all-scale V2 controller laws.
- Produces: a direct contradiction `False` for the hypothetical bad parent, sufficient to establish `GSTPrefixOneNavigationLift`.

- [ ] **Step 1: Write the failing seam theorem in a generated smoke.**

Use the exact target:

```lean
theorem gst_v2_infinite_prefix_one_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  -- implementation supplied only after the smoke demonstrates the missing bridge
```

The smoke is successful as a test only when Lean reports this theorem as the remaining unsolved seam while all imported V2 machinery compiles.

- [ ] **Step 2: Embed the child gate in the all-Nat V2 controller.**

Use `gst_prefix_one_omegaData`/the child witness to obtain the physical child gate. Translate old `gstDigit`/`gstCarry` values into the production namespace's digit/carry representation with explicit equalities; do not assume name-level definitional equality unless Lean confirms it.

- [ ] **Step 3: Split by handwritten information regime, not by termination world.**

For the `I ≠ BIG1` regime, instantiate the green infinite BIG1-clear path/world-prefix theorems. The resulting all-BIG2/SURVIVE `6^K-1` prefixes must collide with the finite natural realization using the existing natural contradiction/world-tower theorem.

For the BIG-N regime, instantiate the exact Navigation-horizon Ω stream. Use the all-scale Ω/Π/U ledger and world projection at arbitrary `K`; after the finite Navigation horizon the transfer stream is zero, while the hypothetical complete bad parent must continue satisfying the all-scale controller constraints. Derive the production contradiction from the finite natural/horizon collision theorem rather than from a terminal Ω theorem.

- [ ] **Step 4: Connect physical gate/event semantics.**

Use the exact physical six-state/right-chord dictionary where needed: a physical Happy gate is `(4,2)` or `(5,5)`, the BIG1-clear nonzero two-layer branch is `(5,5)`, and its base-six chord is `35 = 6^2-1`. No global mirror/reflection assumption is permitted.

- [ ] **Step 5: Kernel-check the adapter.**

Compile the generated smoke and print axioms for `gst_v2_infinite_prefix_one_collision`. Expected: only standard Lean/Mathlib logical axioms (`propext`, `Classical.choice`, `Quot.sound` as induced by Mathlib), with no `sorryAx` and no custom axiom.

- [ ] **Step 6: Commit the green adapter test/proof.**

Commit message: `prove: close prefix-one bad trace by infinite V2 control`.

---

### Task 3: Atomic Monolith Replacement

**Files:**
- Modify: `ErdosTernary2.lean` around the legacy residual Ω block and the active prefix-one information-descent seam.

**Interfaces:**
- Consumes: green `gst_v2_infinite_prefix_one_collision` theorem body/mechanism.
- Produces: active `gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift` with no dependency on `GSTResidualOmegaTermination`.

- [ ] **Step 1: Remove the active legacy Ω-termination dependency.**

Delete or comment out the active declarations `gst_omega_termination_s1`, `gst_omega_termination_s3`, `gst_omega_termination_stable`, `gst_residual_omega_termination`, and the old `gst_residual_navigation_lift` that is constructed from them. Historical prose may remain in comments, but no active theorem may call `gst_omega` to prove `False`.

- [ ] **Step 2: Replace the circular information-descent theorem.**

Remove `gst_prefix_one_information_bad_descends_inline` as a production dependency. Rewrite `gst_prefix_one_child_gate_contradicts_parent_bad_inline` (or replace it with a direct theorem of the same consumer strength) so it invokes the green V2 infinite collision directly from `data.childGate`/`hchild` and `hBad`.

- [ ] **Step 3: Keep the existing public prefix-one theorem interface.**

`gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift` remains the public theorem. Its contradiction branch must now be:

```lean
by_contra hnoParent
have hBad := gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
exact gst_v2_infinite_prefix_one_collision s n hs hn hchild hBad
```

up to the exact compiled adapter signature.

- [ ] **Step 4: Rebuild the general residual theorem from prefix-one.**

Any downstream use of the removed `gst_residual_navigation_lift` must be redirected to:

```lean
gst_residual_navigation_lift_of_prefix_one gst_prefix_one_navigation_lift
```

or to `gst_navigation_witness_all_of_prefix_one gst_prefix_one_navigation_lift` where that interface is already available.

- [ ] **Step 5: Compile the full monolith.**

Run in CI: `lake env lean ErdosTernary2.lean`.
Expected: zero errors from the former three `gst_omega` sites and zero new circular dependencies.

- [ ] **Step 6: Commit.**

Commit message: `refactor: replace legacy omega corridor with infinite V2 bridge`.

---

### Task 4: Comparator and Proof Audit

**Files:**
- Read/run: `scripts/comparator.sh`
- Build: `ErdosTernary2.lean`, `Main.lean`, and comparator-generated/required solution artifacts.

**Interfaces:**
- Consumes: committed monolith after Task 3.
- Produces: actual comparator PASS and auditable proof status.

- [ ] **Step 1: Run full pinned build.**

Run `lake build GSTTactic` then `lake env lean ErdosTernary2.lean` under Lean 4.33.0-rc2.

- [ ] **Step 2: Run forbidden-placeholder audit.**

Search active Lean sources for `sorry`, `admit`, `sorryAx`, custom axioms introduced by the surgery, and `native_decide`. Historical comments do not count as proof terms; active declarations do.

- [ ] **Step 3: Run the real comparator.**

Run `bash scripts/comparator.sh` without `continue-on-error`.
Expected: explicit comparator PASS.

- [ ] **Step 4: Re-run from the committed branch head.**

A fresh GitHub Actions run must checkout the committed surgery with no generated source transformation and produce the same Lean/comparator PASS.

- [ ] **Step 5: Report only verified status.**

If any stage fails, report the exact remaining theorem/error. Claim completion only after the fresh committed run is green and the comparator says PASS.
