# GST Proof Dependency Map

This document gives the high-level dependency flow from General Space Theory (GST) infrastructure into the Problem 406 / Erdős ternary-2 certificate.

It is a presentation map. Lean source and CI remain authoritative.

## High-level flow

```text
Mathlib arithmetic and Nat infrastructure
        ↓
GST finite-state tactics and canonical digit/carry objects
        ↓
2D Mixed Emergence, U2D transport, and crossing-charge inequalities
        ↓
GST Graph V2 production sheet and graph laws
        ↓
Four-power direct arithmetic: LTE, periodicity, residue rows
        ↓
Exponent-prefix / exponent-trit obstruction law
        ↓
Affine channel automaton and Chat-2 bad-channel realization
        ↓
Provider pipeline and creation-certificate bridge
        ↓
Prefix-one ontological escape and monolith theorem stack
        ↓
Problem 406 public API and comparator theorem
```

## Dependency layers

### Layer 0 — External foundations

| Input | Role |
|---|---|
| Mathlib | Natural-number arithmetic, modular arithmetic, tactics, algebraic rewriting. |
| Lean kernel | Final checker for theorem terms. |

### Layer 1 — GST finite-state and canonical state core

| Module | Role |
|---|---|
| `GSTTactic.lean` | Finite case helpers and custom GST tactics. |
| `GSTCanonicalTailStateIso.lean` | `digit3`, `carry4`, `HappyCell`, `Navigation`, tail-state isomorphism. |
| `GSTCanonicalCarryDynamics.lean` | Carry bound and exact carry-forward law. |

### Layer 2 — Emergence and graph state

| Module | Role |
|---|---|
| `GST2DMixedEmergence.lean` | Local and rectangular divergence/emergence equations. |
| `GSTU2D*` modules | U2D transport, crossing charge, sharp domination, phase density. |
| `GSTGraphV2Production.lean` | Production graph object and frames. |
| `GSTGraphV2ProductionLaws.lean` | Edge laws and frame identities. |

### Layer 3 — Four-power arithmetic spine

| Module | Role |
|---|---|
| `GSTFourPowerDirectResidue.lean` | LTE identity, exponent periodicity, row-two classifier. |
| `GSTFourPowerDirectResidue27.lean` | Row-three classifier. |
| `GSTFourPowerDirectResidue81.lean` | Row-four classifier. |
| `GSTFourPowerDirectNo22.lean` | No-common trace forbids adjacent source `22`. |
| `GSTFourPowerExponentTritObstruction.lean` | Parametric exponent-prefix/trit obstruction law. |

### Layer 4 — Counterexample language

| Module | Role |
|---|---|
| `GSTFourPowerDirectExistence.lean` | Defines `CommonTwo` and `FourPowerDirectExistence`. |
| `GSTFourPowerAffineChannelAutomaton.lean` | Converts common-two failure into finite affine channel dynamics. |
| `GSTFourPowerDirectChat2Application.lean` | Identifies the direct problem with bad affine channel `B₁`. |

### Layer 5 — Provider and certificate bridge

| Module | Role |
|---|---|
| `GSTFourPowerHappyProvider.lean` | Converts row-three-or-higher common-two or prefix-hit providers into physical Happy witnesses. |
| `GSTFourPowerDirectExistenceProviderPipeline.lean` | Names the provider gates and no-axiom direct-existence/certificate routes. |
| `GSTFourPowerOntologicalAdapter.lean` | Converts creation certificates into Navigation. |
| `GSTPrefixOneOntologicalEscape.lean` | Prefix-one escape and transplant entrypoints. |

### Layer 6 — Problem 406 surface

| Module/file | Role |
|---|---|
| `ErdosTernary2.lean` | Preserved monolith proof artifact. |
| `questions/deepmind_problem_406/Solution.lean` | Comparator-facing theorem bridge. |
| `GST/Problem406/PublicAPI.lean` | Clean public theorem wrapper. |
| `GST/Problem406/TheoremMap.lean` | Compile-checked public theorem map. |

## Honest boundary rule

The documentation must not hide proof boundaries. If a route uses an explicit compatibility boundary, it must be named. If a route is a no-axiom transplant endpoint, it must be documented separately from the historical monolith path.

For public presentation, say:

- The comparator-facing Problem 406 artifact passed the repository V5 comparator.
- The no-axiom transplant endpoints are separately audited in CI.
- The monolith remains preserved until a planned refactor replaces internal historical names with verified public wrappers or aliases.
