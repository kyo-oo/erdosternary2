# Worldtrace Arithmetic — Lean Erdős Ternary-2 Workspace

This repository contains a Lean formalization of the Erdős ternary-2 / Problem 406 proof, presented as the first flagship theorem of **Worldtrace Arithmetic**.

Worldtrace Arithmetic studies arithmetic objects as trace-bearing worlds: their digit states, carry fields, residue towers, navigation positions, collision layers, and obstruction certificates are tracked together rather than treated as isolated local calculations.

## Main result

The public theorem surface proves the Erdős ternary-2 statement:

```text
For every n >= 9, the ternary expansion of 2^n contains the digit 2.
```

Reviewer-facing Lean entrypoints:

```lean
import Worldtrace.PublicAPI

#check Worldtrace.erdos_ternary_two
#check Worldtrace.four_power_contains_digit_two
```

Historical/internal API entrypoints remain available:

```lean
#check GST.Problem406.contains_two_digit_of_nine_le
#check erdos_ternary_2_universal
```

## Framework position

General Space Theory (GST) is a major pillar of Worldtrace Arithmetic, not the entire mathematics.

The proof stack also contains:

- True Duality Transcendence;
- ternary digit and prefix arithmetic;
- carry-information transport;
- residue tower stabilization;
- four-power dynamics;
- exponent-prefix obstruction;
- canonical collision and wave theory;
- phase-cycle regeneration;
- finite certificate kernels.

## Proof-corpus census

The FINISHER census tracks the comparator-final monolith plus its recursive custom import closure.

| Item | Count |
| --- | ---: |
| Main monolith lines | 17,041 |
| Custom import-closure files | 74 |
| Custom import-closure lines | 30,416 |
| Total declarations | 1,791 |
| Theorem-like declarations | 1,396 |
| General Space Theory proper theorem-like declarations | 77 |
| Non-GST theorem-like declarations | 1,319 |

This is why the public identity is **Worldtrace Arithmetic**, with GST as one named pillar.

## Repository map

| Path | Role |
| --- | --- |
| `ErdosTernary2.lean` | Monolithic checked proof artifact. |
| `Worldtrace/PublicAPI.lean` | New umbrella public API facade. |
| `GST/Problem406/*.lean` | Stable Problem 406 public wrappers. |
| `GST/PublicAPI.lean` | Compatibility public API over historical GST namespace. |
| `FINISHER/` | Frozen proof/presentation bundle. |
| `FINISHER/THEOREM_FAMILIES.md` | Theorem-family census. |
| `WORLDTRACE.md` | Public identity document for the new mathematics. |
| `docs/worldtrace/architecture.md` | Framework architecture and layer map. |
| `docs/worldtrace/public-api-roadmap.md` | Next public API expansion plan. |
| `docs/problem406/` | Problem 406-specific reviewer docs. |
| `docs/gst/` | GST-specific pillar documentation. |

## Naming policy

Use **Worldtrace Arithmetic** for the whole mathematical framework.

Use **General Space Theory (GST)** only for the navigation/geometric pillar and for historical Lean namespace compatibility.

Do not mass-rename internal theorem declarations blindly.  Public promotion happens through curated wrapper modules first; internal migration should be dependency-safe and CI-checked.

## Current presentation strategy

The repository is arranged into three review layers:

1. **Worldtrace identity** — branch-level mathematical framing.
2. **Curated public API** — stable names for the proof spine.
3. **Frozen proof corpus** — monolith, import closure, theorem census, and audit artifacts.
