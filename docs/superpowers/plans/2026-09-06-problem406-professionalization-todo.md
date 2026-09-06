# Problem 406 Professionalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the green Problem 406 proof artifact into a professional, reviewer-friendly Lean project without damaging the accepted monolith.

**Architecture:** Keep `ErdosTernary2.lean` as the protected fossil/kernel checkpoint. Build a clean outer shell around it: public API wrappers, theorem maps, tactic documentation, generated manifests, and CI lanes. Only after those layers are green should any internal rename, split, or monolith surgery be considered.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, Lake, GitHub Actions, Markdown documentation.

**Spec:** This plan implements the post-rest architecture decision: naming cleanup by public aliases first, comments/imports/tactics cleanup by outer shell first, and theory presentation as layered arithmetic core -> GST structural engine -> bridge/certificate layer -> Problem 406 theorem -> exposition.

## Global Constraints

- Do not edit `ErdosTernary2.lean` during Phases 1-5.
- Do not mass-rename internal theorem declarations during Phases 1-5.
- Do not weaken `questions/deepmind_problem_406/Solution.lean`.
- Preserve the comparator theorem statement `erdos_ternary_2` exactly.
- Keep custom tactics; document and isolate them instead of deleting them.
- Keep emotional/history/philosophy text out of public Lean source; move it to docs/exposition when needed.
- Every new Lean wrapper must compile by importing existing green artifacts, not by copying proof bodies.
- Every CI lane must be additive and must not make experimental probes required.
- Any strict no-axiom claim must be supported by an explicit axiom audit; do not hide the legacy direct-existence boundary.

---

## Phase status board

| Phase | Name | Status | Rule |
|---|---|---|---|
| 0 | Groundwork already created | Done | `docs/gst/*` exists as initial architecture docs. |
| 1 | Master roadmap and freeze rules | In progress | Create this plan and make it the controlling checklist. |
| 2 | Public Lean API shell | Next | Add clean wrapper modules only; no proof surgery. |
| 3 | Theorem manifest and declaration counts | Next | Generate/searchable manifest of all theorem families. |
| 4 | Tactic and audit hygiene | Next | Document tactics and move audit-only checks out of public files where safe. |
| 5 | Human exposition layer | Next | Separate arithmetic proof, GST mechanism, and speculative extensions. |
| 6 | CI verification and dashboard cleanup | Next | Verify wrappers, comparator, sorry scan, and axiom reports. |
| 7 | Optional monolith split/refactor | Locked | Do not begin until Phases 1-6 are green. |

---

## Phase 1: Master roadmap and freeze rules

**Files:**
- Create: `docs/superpowers/plans/2026-09-06-problem406-professionalization-todo.md`
- Read: `docs/gst/README.md`
- Read: `docs/gst/presentation-rules.md`
- Test: GitHub file listing for `docs/gst` and this plan.

**Interfaces:**
- Consumes: existing monolith `ErdosTernary2.lean`, `GST/Problem406/PublicAPI.lean`, `docs/gst/*`.
- Produces: controlling checklist for all later execution phases.

- [x] **Step 1: Admit the correction**

Record that the prior docs pass was useful groundwork, but execution must now return to a phased roadmap.

- [x] **Step 2: Freeze the monolith**

Rule: `ErdosTernary2.lean` remains untouched until wrapper API, theorem manifest, and CI lanes are green.

- [x] **Step 3: Preserve non-GST major theorem families**

Rule: supporting engines such as 2D Mixed Emergence, U2D, four-power arithmetic, affine channels, provider pipeline, and prefix-one escape must be documented as first-class theorem families, not erased under a vague GST label.

- [ ] **Step 4: Verify roadmap file exists**

Run through GitHub contents API or local checkout:

```bash
ls docs/superpowers/plans/2026-09-06-problem406-professionalization-todo.md
```

Expected: file exists.

---

## Phase 2: Public Lean API shell

**Files:**
- Existing: `GST/Problem406/PublicAPI.lean`
- Existing: `GST/Problem406/TheoremMap.lean`
- Create: `GST/Arithmetic/TernaryDigits.lean`
- Create: `GST/Arithmetic/Carries.lean`
- Create: `GST/FourPower/CommonTwo.lean`
- Create: `GST/FourPower/PrefixLaw.lean`
- Create: `GST/FourPower/Certificate.lean`
- Create: `GST/PublicAPI.lean`
- Optionally create: `ErdosTernary2/PublicAPI.lean` only if Lake module naming supports it cleanly.

**Interfaces:**
- Consumes: existing declarations from `GSTCanonicalTailStateIso`, `GSTCanonicalCarryDynamics`, `GSTFourPowerDirectExistence`, `GSTFourPowerExponentTritObstruction`, `GSTFourPowerOntologicalAdapter`, and `GST.Problem406.PublicAPI`.
- Produces: calm public theorem/definition aliases under namespaces `GST.Arithmetic`, `GST.FourPower`, and `GST.Problem406`.

- [ ] **Step 1: Create arithmetic digit wrapper**

Create `GST/Arithmetic/TernaryDigits.lean`:

```lean
import GSTCanonicalTailStateIso

/-!
# Ternary digit API

Clean public names for the ternary digit primitives used by the Problem 406 proof.
This file contains wrappers only and does not copy proof bodies.
-/

namespace GST
namespace Arithmetic

/-- Ternary digit at position `p`. -/
abbrev digit3 : Nat -> Nat -> Nat := GSTCanonicalTailStateIso.digit3

/-- A number has a physical ternary digit-two gate if it has a Happy cell somewhere. -/
abbrev Navigation : Nat -> Prop := GSTCanonicalTailStateIso.Navigation

end Arithmetic
end GST
```

- [ ] **Step 2: Create carry wrapper**

Create `GST/Arithmetic/Carries.lean`:

```lean
import GSTCanonicalCarryDynamics

/-!
# Carry API

Clean public names for exact base-three carry dynamics.
-/

namespace GST
namespace Arithmetic

/-- Exact carry at row `p` when multiplying by four. -/
abbrev carry4 : Nat -> Nat -> Nat := GSTCanonicalTailStateIso.carry4

/-- Every physical carry is below four. -/
theorem carry4_lt_four (R p : Nat) : carry4 R p < 4 := by
  exact GSTCanonicalCarryDynamics.carry4_lt_four R p

/-- Exact one-column carry-forward law. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = (carry4 R p + 4 * GSTCanonicalTailStateIso.digit3 R p) / 3 := by
  exact GSTCanonicalCarryDynamics.carry4_forward_exact R p

end Arithmetic
end GST
```

- [ ] **Step 3: Create four-power common-two wrapper**

Create `GST/FourPower/CommonTwo.lean`:

```lean
import GSTFourPowerDirectExistence

/-!
# Four-power common-two API

Public names for the direct arithmetic common digit-two witness between two consecutive powers of four.
-/

namespace GST
namespace FourPower

abbrev CommonTwo : Nat -> Prop := GSTFourPowerDirectExistence.CommonTwo

abbrev DirectExistence : Prop := GSTFourPowerDirectExistence.FourPowerDirectExistence

/-- A common-two witness gives a digit two in the source power. -/
theorem common_two_has_source_two
    (K : Nat) (h : CommonTwo K) :
    exists p : Nat, 1 <= p /\ GSTFourPowerDirectResidue.digit3 (4^K) p = 2 := by
  exact GSTFourPowerDirectExistence.commonTwo_has_source_two K h

end FourPower
end GST
```

- [ ] **Step 4: Create exponent-prefix wrapper**

Create `GST/FourPower/PrefixLaw.lean`:

```lean
import GSTFourPowerExponentTritObstruction

/-!
# Exponent-prefix API

Public names for the parametric exponent-prefix law.
-/

namespace GST
namespace FourPower

abbrev exponentPrefix : Nat -> Nat -> Nat := GSTFourPowerExponentTritObstruction.exponentPrefix
abbrev exponentTrit : Nat -> Nat -> Nat := GSTFourPowerExponentTritObstruction.exponentTrit

/-- Exact decomposition of an exponent into low prefix, current trit, and high suffix. -/
theorem exponent_prefix_trit_decomposition (K p : Nat) :
    K = exponentPrefix K p
      + exponentTrit K p * 3^p
      + 3^(p+1) * ((K / 3^p) / 3) := by
  exact GSTFourPowerExponentTritObstruction.exponent_prefix_trit_decomposition K p

end FourPower
end GST
```

- [ ] **Step 5: Create certificate wrapper**

Create `GST/FourPower/Certificate.lean`:

```lean
import GSTFourPowerOntologicalAdapter

/-!
# Four-power certificate API

Public certificate names connecting direct arithmetic witnesses to physical navigation.
-/

namespace GST
namespace FourPower

abbrev CreationCertificate : Nat -> Prop := GSTFourPowerOntologicalAdapter.CreationCertificate
abbrev CreationMaster : Prop := GSTFourPowerOntologicalAdapter.FourPowerCreationMaster

/-- A creation certificate gives a navigation witness. -/
theorem creation_certificate_to_navigation
    (R : Nat) (h : CreationCertificate R) : GSTCanonicalTailStateIso.Navigation R := by
  exact GSTFourPowerOntologicalAdapter.creation_certificate_to_navigation R h

end FourPower
end GST
```

- [ ] **Step 6: Create umbrella public API**

Create `GST/PublicAPI.lean`:

```lean
import GST.Problem406.PublicAPI
import GST.Arithmetic.TernaryDigits
import GST.Arithmetic.Carries
import GST.FourPower.CommonTwo
import GST.FourPower.PrefixLaw
import GST.FourPower.Certificate

/-!
# GST public API

Reviewer-facing imports for the Problem 406 formalization.
-/
```

- [ ] **Step 7: Build wrappers**

Run:

```bash
lake env lean GST/Arithmetic/TernaryDigits.lean
lake env lean GST/Arithmetic/Carries.lean
lake env lean GST/FourPower/CommonTwo.lean
lake env lean GST/FourPower/PrefixLaw.lean
lake env lean GST/FourPower/Certificate.lean
lake env lean GST/PublicAPI.lean
```

Expected: no errors.

- [ ] **Step 8: Commit public API shell**

```bash
git add GST/Arithmetic GST/FourPower GST/PublicAPI.lean
git commit -m "Add GST public API shell"
```

---

## Phase 3: Theorem manifest and declaration counts

**Files:**
- Create: `scripts/generate_theorem_manifest.py`
- Create: `docs/gst/generated/theorem-manifest.md`
- Create: `docs/gst/generated/declaration-counts.md`
- Create: `docs/gst/generated/public-alias-candidates.md`

**Interfaces:**
- Consumes: all `.lean` files in the repo except `.lake` build output.
- Produces: searchable declaration inventory grouped by file and family.

- [ ] **Step 1: Write manifest script**

Script behavior:

```text
Scan *.lean files.
Collect lines beginning with theorem, lemma, def, abbrev, structure, inductive, axiom.
Group by file.
Classify by filename prefix: GSTCanonical, GSTFourPower, GSTGraphV2, GSTU2D, GSTPrefixOne, Problem406, Monolith, Other.
Write Markdown files under docs/gst/generated/.
```

- [ ] **Step 2: Run manifest generation**

```bash
python scripts/generate_theorem_manifest.py
```

Expected: generated docs exist and include `erdos_ternary_2_universal`, `contains_two_digit_of_nine_le`, `CommonTwo`, `exponentPrefix`, and `CreationCertificate`.

- [ ] **Step 3: Commit generated manifest**

```bash
git add scripts/generate_theorem_manifest.py docs/gst/generated
git commit -m "Generate GST theorem manifest"
```

---

## Phase 4: Tactic and audit hygiene

**Files:**
- Existing: `GSTTactic.lean`
- Existing: `docs/gst/tactic-index.md`
- Create: `GST/Audit/Problem406AxiomReport.lean`
- Create: `GST/Audit/PublicSurfaceCheck.lean`

**Interfaces:**
- Consumes: existing custom tactics and public API wrappers.
- Produces: reviewer-safe audit files so public modules can avoid stray `#check` and `#print axioms` noise.

- [ ] **Step 1: Read `GSTTactic.lean` fully**

Extract all custom syntax/tactic names such as `gst_omega`, `gst_carry_cases`, `gst_digit_cases`, and `gst_end`.

- [ ] **Step 2: Update `docs/gst/tactic-index.md`**

Document for each tactic:

```text
name
purpose
trusted kernel status
where used
whether public reviewers need to inspect it
```

- [ ] **Step 3: Create audit namespace files**

Create `GST/Audit/Problem406AxiomReport.lean` and `GST/Audit/PublicSurfaceCheck.lean` containing only imports, `#check`, and `#print axioms` commands.

- [ ] **Step 4: Add additive CI for audit files**

Create or extend a workflow so the audit files compile, without making experimental probes required.

---

## Phase 5: Human exposition layer

**Files:**
- Create: `docs/problem406/exposition/arithmetic-core.md`
- Create: `docs/problem406/exposition/gst-mechanism.md`
- Create: `docs/problem406/exposition/bridge-layer.md`
- Create: `docs/problem406/exposition/external-interpretation-boundary.md`

**Interfaces:**
- Consumes: theorem map, public API shell, and theorem manifest.
- Produces: professional human-readable explanation that separates proved Lean statements from interpretation.

- [ ] **Step 1: Write arithmetic-core exposition**

Explain only exact definitions: ternary digits, carries, `noTernaryTwo`, `CommonTwo`, exponent prefixes.

- [ ] **Step 2: Write GST mechanism exposition**

Explain GST as structural mechanism: carry transport, Graph V2, U2D, mixed emergence, and prefix-one escape.

- [ ] **Step 3: Write bridge-layer exposition**

Explain the chain:

```text
GST structural engine
-> CommonTwo / HappyCell / CreationCertificate
-> digit two in powers of four
-> digit two in powers of two
-> Problem 406 theorem
```

- [ ] **Step 4: Write external interpretation boundary**

State clearly:

```text
Lean certifies the arithmetic theorem. GST exposition explains the mechanism. Physics or universe-level interpretations are future theoretical extensions and are not certified by the Problem 406 comparator.
```

---

## Phase 6: CI verification and dashboard cleanup

**Files:**
- Existing: `.github/workflows/gpt56-problem406-public-api.yml`
- Existing: `.github/workflows/gpt56-full-monolith-axiom-and-official-comparator.yml`
- Existing: `.github/workflows/gpt56-canonical-tail-escape-ci.yml`
- Existing: `scripts/comparator.sh`
- Existing: `scripts/sorry_check.sh`

**Interfaces:**
- Consumes: wrapper API, manifest, audit files.
- Produces: clear green dashboard for reviewers.

- [ ] **Step 1: Run public API CI**

Expected marker:

```text
PROBLEM406_PUBLIC_API_GREEN=1
```

- [ ] **Step 2: Run comparator**

Expected markers:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
```

- [ ] **Step 3: Run sorry scan**

Expected markers:

```text
SORRY_SCAN_CLEAN=1
INTENTIONAL_PROBLEM406_CHALLENGE_HOLE_EXCLUDED=1
```

- [ ] **Step 4: Run axiom report**

Expected result: public no-axiom endpoint audit reports only Lean/kernel axioms where applicable and reports the known legacy inline boundary honestly.

---

## Phase 7: Optional monolith split/refactor

**Files:**
- Potentially modify: `ErdosTernary2.lean`
- Potentially create: split modules under `GST/Arithmetic`, `GST/FourPower`, `GST/GraphV2`, `GST/Problem406`.

**Interfaces:**
- Consumes: all green prior phases.
- Produces: internal cleanup only if it can be done without breaking comparator or axiom status.

- [ ] **Gate 1: Do not start unless Phases 1-6 are green**

This phase is locked until the public shell, manifest, exposition, and CI pass.

- [ ] **Gate 2: Create a fresh branch before touching monolith**

```bash
git checkout -b sol/problem406-monolith-refactor-safe
```

- [ ] **Gate 3: Split one tiny section only**

Move one self-contained group, build, compare, then stop for review.

- [ ] **Gate 4: Never mass-rename blindly**

Every internal rename must have a compatibility alias or proof-preserving migration path.

---

## Immediate next action

Begin Phase 2 only after this roadmap is verified. The first Phase 2 deliverable is the wrapper `GST/Arithmetic/TernaryDigits.lean`, because it exposes clean arithmetic names without changing any proof body.
