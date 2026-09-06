# Worldtrace CI and release plan

This document defines the green path for the Worldtrace Arithmetic presentation layer.

## Required checks

| Check | Required meaning |
| --- | --- |
| `Worldtrace.PublicAPI` | Umbrella public facade resolves and builds. |
| `Worldtrace.TheoremMap` | Every promoted public theorem name resolves. |
| `GST.PublicAPI` | Historical compatibility surface still builds. |
| `GST.Problem406.TheoremMap` | Existing Problem 406 map remains intact. |
| `ErdosTernary2` | Monolithic proof artifact remains buildable. |
| `FINISHER` bundle | Frozen proof bundle regenerates with Worldtrace overlay. |
| Census scripts | Theorem-family counts remain machine-readable. |

## CI workflow state

The existing public API workflow has been renamed at the workflow-title level to:

```text
Worldtrace Public API
```

It now builds the Worldtrace layer modules in addition to the existing GST/Problem406 wrappers.

## Build order

Preferred local/CI order:

```bash
lake build GST.PublicAPI
lake build Worldtrace.Genesis
lake build Worldtrace.Ternary
lake build Worldtrace.Carry
lake build Worldtrace.Residue
lake build Worldtrace.FourPower
lake build Worldtrace.Navigation
lake build Worldtrace.Collision
lake build Worldtrace.Phase
lake build Worldtrace.Certificate
lake build Worldtrace.PublicAPI
lake build Worldtrace.TheoremMap
```

## Release checklist

Before tagging a release:

- README starts with Worldtrace Arithmetic.
- `WORLDTRACE.md` explains the branch-level identity.
- `Worldtrace/PublicAPI.lean` is the public umbrella import.
- `Worldtrace/TheoremMap.lean` builds.
- `docs/worldtrace/theorem-promotion-map.md` maps internal names to public names.
- FINISHER includes the Worldtrace overlay.
- Internal historical names are not exposed as the public API.
- CI has a completed green run for the final branch tip or a clearly identified equivalent tested commit.

## Non-goal

This phase does not claim that every internal theorem declaration has been renamed.  That is a later dependency-safe migration.  The goal here is a professional, stable, reviewable Worldtrace surface over the checked proof corpus.
