# Problem 406 Presentation Layer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a professional, non-invasive presentation layer around the accepted Problem 406 Lean artifact without editing the green monolith proof.

**Architecture:** Treat `ErdosTernary2.lean` as the fossil artifact: preserved, cited, and imported, but not directly renamed or rewritten. Add small public wrapper files, theorem-map documentation, and CI checks that expose clean names while keeping the original comparator-passing proof intact.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, Lake, GitHub Actions, Markdown documentation.

**Spec:** This plan is the controlling spec for the first presentation phase. It starts from the comparator-passing artifact on branch `sol/gpt56-canonical-tail-escape-20260827` and preserves the current monolith as a protected proof checkpoint.

## Global Constraints

- Do not edit `ErdosTernary2.lean` in this phase.
- Do not rename internal theorem declarations in this phase.
- Do not weaken `questions/deepmind_problem_406/Solution.lean`.
- Preserve the comparator theorem statement `erdos_ternary_2` exactly.
- Keep the disabled `GPT56 Residual Omega Probe` manual-only unless explicitly re-enabled later.
- Public-facing Lean files must use calm Mathlib-style module docs, imports at the top, namespaces, and descriptive theorem names.
- Any new Lean wrapper must compile by importing the existing green artifact instead of copying proof bodies.
- Any CI addition must be additive and must not make the historical auxiliary probe required.

---

## File Structure

- Create `GST/Problem406/PublicAPI.lean`: clean public Lean names for the main theorem and predicate bridge, implemented as wrappers around existing declarations.
- Create `GST/Problem406/TheoremMap.lean`: a lightweight Lean index containing `#check` declarations for the public API and key internal bridge theorems.
- Create `docs/problem406/theorem-map.md`: human-readable map from public theorem names to internal fossil-artifact names.
- Create `docs/problem406/submission-surface.md`: short explanation of what an external reviewer should inspect first.
- Create `.github/workflows/gpt56-problem406-public-api.yml`: additive CI lane that builds only the public presentation layer.
- Do not modify `ErdosTernary2.lean`.

---

### Task 1: Public API wrapper

**Files:**
- Create: `GST/Problem406/PublicAPI.lean`
- Test: `lake env lean GST/Problem406/PublicAPI.lean`

**Interfaces:**
- Consumes: `ErdosTernary2.erdos_ternary_2_universal`, `noTernaryTwo`, and the existing challenge-compatible predicate bridge from `questions/deepmind_problem_406/Solution.lean` if imported safely.
- Produces: `GST.Problem406.contains_two_digit_of_nine_le` as the calm public theorem name.

- [ ] **Step 1: Create the wrapper file**

```lean
import ErdosTernary2

/-!
# Public API for Problem 406

This file gives stable, readable names for the comparator-passing theorem.
It does not alter the monolith proof.  The original proof artifact remains
`ErdosTernary2.lean`; this file only re-exports its main result under a clean
review-facing namespace.
-/

namespace GST
namespace Problem406

/-- For every exponent `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`. -/
theorem contains_two_digit_of_nine_le
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false := by
  exact erdos_ternary_2_universal n hn

end Problem406
end GST
```

- [ ] **Step 2: Build the wrapper file**

Run:

```bash
lake env lean GST/Problem406/PublicAPI.lean
```

Expected:

```text
no errors
```

- [ ] **Step 3: Commit the wrapper**

```bash
git add GST/Problem406/PublicAPI.lean
git commit -m "Add Problem 406 public API wrapper"
```

---

### Task 2: Lean theorem map

**Files:**
- Create: `GST/Problem406/TheoremMap.lean`
- Test: `lake env lean GST/Problem406/TheoremMap.lean`

**Interfaces:**
- Consumes: `GST.Problem406.contains_two_digit_of_nine_le` from Task 1.
- Produces: a compile-checked Lean index of the review-facing theorem surface.

- [ ] **Step 1: Create theorem-map Lean file**

```lean
import GST.Problem406.PublicAPI

/-!
# Problem 406 theorem map

This file is a compile-checked index of the public theorem surface.  It exists
for reviewers and automation.  It contains no new proof obligations.
-/

#check GST.Problem406.contains_two_digit_of_nine_le
#check erdos_ternary_2_universal
#check noTernaryTwo
```

- [ ] **Step 2: Build theorem map**

Run:

```bash
lake env lean GST/Problem406/TheoremMap.lean
```

Expected:

```text
no errors
```

- [ ] **Step 3: Commit theorem map**

```bash
git add GST/Problem406/TheoremMap.lean
git commit -m "Add Problem 406 theorem map"
```

---

### Task 3: Human-readable theorem map

**Files:**
- Create: `docs/problem406/theorem-map.md`
- Test: manual review plus `grep` checks shown below.

**Interfaces:**
- Consumes: public theorem names from Tasks 1 and 2.
- Produces: a reviewer-facing Markdown guide linking clean names to internal fossil names.

- [ ] **Step 1: Create Markdown theorem map**

```markdown
# Problem 406 Theorem Map

This document maps the clean public API to the internal fossil artifact.

## Public theorem

| Public name | Internal source | Meaning |
|---|---|---|
| `GST.Problem406.contains_two_digit_of_nine_le` | `erdos_ternary_2_universal` in `ErdosTernary2.lean` | For every `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`. |

## Comparator surface

| File | Role |
|---|---|
| `questions/deepmind_problem_406/Challenge.lean` | Benchmark statement with intentional challenge-side `sorry`. |
| `questions/deepmind_problem_406/Solution.lean` | Submitted solution bridge importing the green monolith. |
| `ErdosTernary2.lean` | Preserved proof artifact containing the accepted theorem stack. |

## Preservation rule

`ErdosTernary2.lean` is treated as a preserved proof artifact.  Presentation
work should add wrappers, maps, and documentation around it before attempting
any direct internal rename or source surgery.
```

- [ ] **Step 2: Verify required names appear**

Run:

```bash
grep -R "GST.Problem406.contains_two_digit_of_nine_le" docs/problem406/theorem-map.md
grep -R "erdos_ternary_2_universal" docs/problem406/theorem-map.md
grep -R "ErdosTernary2.lean" docs/problem406/theorem-map.md
```

Expected: all three commands print matching lines.

- [ ] **Step 3: Commit Markdown theorem map**

```bash
git add docs/problem406/theorem-map.md
git commit -m "Document Problem 406 theorem map"
```

---

### Task 4: Submission surface guide

**Files:**
- Create: `docs/problem406/submission-surface.md`
- Test: manual review plus `grep` checks shown below.

**Interfaces:**
- Consumes: theorem-map document from Task 3.
- Produces: short reviewer path explaining what to inspect first.

- [ ] **Step 1: Create submission guide**

```markdown
# Problem 406 Submission Surface

This page gives the shortest review path for the Lean artifact.

## Review order

1. Read `questions/deepmind_problem_406/Challenge.lean` for the exact benchmark statement.
2. Read `questions/deepmind_problem_406/Solution.lean` for the submitted theorem bridge.
3. Read `GST/Problem406/PublicAPI.lean` for the clean public theorem name.
4. Treat `ErdosTernary2.lean` as the preserved proof artifact that the public API imports.

## Verification command

```bash
bash scripts/comparator.sh
```

Expected successful verdict:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
Build:   0 errors
Sorries: 0
Status:  CLEAN ✓
```

## Scope statement

The comparator-facing theorem is the arithmetic Problem 406 statement: for all
`n ≥ 9`, the ternary expansion of `2^n` contains digit `2`.
```

- [ ] **Step 2: Verify required reviewer path appears**

Run:

```bash
grep -R "questions/deepmind_problem_406/Solution.lean" docs/problem406/submission-surface.md
grep -R "bash scripts/comparator.sh" docs/problem406/submission-surface.md
grep -R "Your solution is okay" docs/problem406/submission-surface.md
```

Expected: all three commands print matching lines.

- [ ] **Step 3: Commit submission guide**

```bash
git add docs/problem406/submission-surface.md
git commit -m "Document Problem 406 submission surface"
```

---

### Task 5: Add public API CI lane

**Files:**
- Create: `.github/workflows/gpt56-problem406-public-api.yml`
- Test: GitHub Actions run on branch `sol/gpt56-canonical-tail-escape-20260827`.

**Interfaces:**
- Consumes: `GST/Problem406/PublicAPI.lean` and `GST/Problem406/TheoremMap.lean`.
- Produces: a small green CI lane proving the presentation layer compiles independently.

- [ ] **Step 1: Create workflow file**

```yaml
name: GPT56 Problem406 Public API

on:
  push:
    branches:
      - sol/gpt56-canonical-tail-escape-20260827
  workflow_dispatch:

jobs:
  public-api:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@v5
      - name: Install exact Lean RC2
        shell: bash
        run: |
          set -euo pipefail
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0-rc2
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
      - name: Build public Problem 406 API
        shell: bash
        run: |
          set -euo pipefail
          export PATH="$HOME/.elan/bin:$PATH"
          lake update
          lake exe cache get
          lake env lean GST/Problem406/PublicAPI.lean
          lake env lean GST/Problem406/TheoremMap.lean
          echo 'PROBLEM406_PUBLIC_API_GREEN=1'
```

- [ ] **Step 2: Commit workflow**

```bash
git add .github/workflows/gpt56-problem406-public-api.yml
git commit -m "Add Problem 406 public API CI"
```

- [ ] **Step 3: Verify GitHub Actions result**

Expected run result:

```text
GPT56 Problem406 Public API: completed / success
PROBLEM406_PUBLIC_API_GREEN=1
```

---

### Task 6: Freeze direct monolith surgery until wrapper layer is green

**Files:**
- No code files modified.
- Review: Git history and CI dashboard.

**Interfaces:**
- Consumes: successful completion of Tasks 1 through 5.
- Produces: a stable rule for the next phase.

- [ ] **Step 1: Confirm wrapper layer is green**

Run:

```bash
lake env lean GST/Problem406/PublicAPI.lean
lake env lean GST/Problem406/TheoremMap.lean
bash scripts/comparator.sh
```

Expected:

```text
PublicAPI.lean: no errors
TheoremMap.lean: no errors
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
```

- [ ] **Step 2: Record the direct-surgery freeze rule**

Add this rule to the next planning document before any rename/refactor phase:

```text
No internal monolith theorem rename begins until the public API wrapper, theorem map, submission surface, and public API CI lane are green.
```

- [ ] **Step 3: Decide next phase**

Choose exactly one next phase after this plan is complete:

```text
A. Public API expansion
B. Documentation and LaTeX exposition
C. Internal theorem-name aliasing
D. Monolith split/refactor
```

Recommended next phase: `A. Public API expansion`.
