# GST Tactic and Audit Hygiene

This document fixes the reviewer-facing rule for the post-comparator cleanup phase.

## Protected kernel artifact

`ErdosTernary2.lean` remains the protected proof checkpoint. It is not edited by the professionalization phases. The cleanup work builds an outer shell: wrappers, audits, generated manifests, and exposition.

## Tactic policy

Custom tactics are allowed when they reduce repetitive finite-state arithmetic. They are proof automation, not new assumptions. Reviewer-facing files should prefer direct proof terms such as `exact existing_theorem ...` whenever possible.

The tactical surface is documented in `docs/gst/tactic-index.md`. Public API wrappers should not become tactic showcases; they should expose stable names and delegate to already-green declarations.

## Audit policy

Audit-only commands live in audit modules, not in the smallest public API files.

Current audit modules:

- `GST/Audit/PublicSurfaceCheck.lean`: compile-checked `#check` surface for public names.
- `GST/Audit/Problem406AxiomReport.lean`: `#print axioms` report for the Problem 406 endpoint.

## CI policy

The public API workflow must build transitive Lean dependencies before invoking file-level checks. The red public-API run failed because it called raw `lake env lean` on wrapper files before the imported `.olean` files were guaranteed to exist. The hardened lane now performs a dependency build first, then checks the public files and audit files.

## Non-negotiable rule

Do not use audit cleanup as an excuse to weaken the comparator result, rename the monolith, or hide the known proof boundaries. The professional shell should make the proof easier to inspect, not harder to audit.
