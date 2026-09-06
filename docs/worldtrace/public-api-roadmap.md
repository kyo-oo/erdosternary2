# Worldtrace public API roadmap

This document defines the next professionalization phase after confirming the umbrella name **Worldtrace Arithmetic**.

## Status

Completed:

- Clean Problem 406 public API under `GST.Problem406.*`.
- Reviewer-facing theorem map for the curated Problem 406 surface.
- Professional monolith comments and header discipline.
- FINISHER theorem-family census.
- `Worldtrace.PublicAPI` facade over the checked proof corpus.

Not completed yet:

- Full dependency-safe neutralization of old internal `gpt56*` / tool-era declaration names.
- Worldtrace-level wrappers for every major family outside the current Problem 406 spine.
- Reviewer guide that tells a mathematician exactly how to audit the proof route.
- CI workflow naming cleanup.

## Public API categories

The public API should be arranged by mathematical role, not by construction history.

| Category | Purpose | Public module target |
| --- | --- | --- |
| Core theorem | Final Problem 406 statement. | `Worldtrace.PublicAPI` |
| Ternary events | Digit-two predicates and finite-position witnesses. | `Worldtrace.Ternary` |
| Carry information | Carry bounds, affine carry, and carry transport. | `Worldtrace.Carry` |
| Residue towers | Stable `3^k` residue fingerprints. | `Worldtrace.Residue` |
| Four-power dynamics | Adjacent powers, common-two witnesses, exponent-prefix obstruction. | `Worldtrace.FourPower` |
| Navigation geometry | General Space Theory gates, spaces, witnesses, certificates. | `Worldtrace.Navigation` |
| Collision closure | Canonical tail, bad-trace, collision, and terminal-extinction layer. | `Worldtrace.Collision` |
| Phase cycles | NULL regeneration, phase transport, shared information equations. | `Worldtrace.Phase` |
| Finite certificates | Kernel-decided local certificates and base closures. | `Worldtrace.Certificate` |

## Phase plan

### Phase 1 — identity lock

Goal: make Worldtrace Arithmetic visible as the umbrella without changing proof internals.

Deliverables:

- `WORLDTRACE.md` top-level identity document.
- `docs/worldtrace/architecture.md` architecture document.
- `Worldtrace/PublicAPI.lean` Lean facade.
- README and FINISHER updates.

### Phase 2 — API expansion by layer

Goal: promote the proof stack into clean mathematical modules.

Deliverables:

- `Worldtrace.Ternary`
- `Worldtrace.Carry`
- `Worldtrace.Residue`
- `Worldtrace.FourPower`
- `Worldtrace.Navigation`
- `Worldtrace.Collision`
- `Worldtrace.Phase`
- `Worldtrace.Certificate`

Each module should expose a small curated set of wrapper names and docstrings.  It should not rename internal declarations directly.

### Phase 3 — internal-name migration

Goal: remove tool-era names from live source without breaking dependencies.

Rules:

1. Generate a dependency manifest for every non-public historical name.
2. Introduce neutral names first.
3. Rewrite references file-by-file.
4. Keep compatibility aliases temporarily when needed.
5. Run the full Lean build before deleting aliases.

### Phase 4 — reviewer packet

Goal: make the project auditable by an external reader.

Deliverables:

- `FINISHER/REVIEWER_GUIDE.md`
- `FINISHER/WORLDTRACE_ARITHMETIC.md`
- `FINISHER/API_MAP.md`
- `FINISHER/AUDIT_STATUS.md`

### Phase 5 — CI and release polish

Goal: presentation looks professional from the first GitHub page.

Deliverables:

- neutral CI workflow names;
- updated badge surface;
- public API build check for `Worldtrace.PublicAPI`;
- release tag or branch freeze once green.

## Decision rule

Worldtrace Arithmetic is the public identity.  GST remains a named pillar and compatibility namespace.  The public surface should explain the full mathematics without pretending every theorem belongs only to GST.
