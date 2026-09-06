# Worldtrace Arithmetic

Worldtrace Arithmetic is the public umbrella name for the mathematics represented by this proof bundle.

The FINISHER bundle freezes the Lean proof corpus and presents it through a professional layer: theorem-family census, curated public API, audit documents, and framework architecture.

## Identity

Worldtrace Arithmetic studies arithmetic objects as trace-bearing worlds.  A worldtrace records how digit states, carry states, residue towers, navigation positions, collision layers, phase cycles, and obstruction certificates remain coupled across transformations.

## Why this is not only GST

General Space Theory (GST) is a major pillar, but the proof corpus contains many theorem families outside GST proper.

The FINISHER census reports:

| Item | Count |
| --- | ---: |
| Theorem-like declarations | 1,396 |
| General Space Theory proper theorem-like declarations | 77 |
| Non-GST theorem-like declarations | 1,319 |

So the correct presentation is:

```text
Worldtrace Arithmetic = whole mathematics
General Space Theory = navigation-geometric pillar
Problem 406 = first flagship theorem
```

## Layer map

```text
Worldtrace Arithmetic
├── True Duality Transcendence / genesis arithmetic
├── Ternary Event Arithmetic
├── Carry-Information Theory
├── Residue Tower Theory
├── Four-Power Dynamics
├── General Space Theory
├── Canonical Collision Theory
├── Phase-Cycle Algebra
├── Finite Certificate Theory
└── Problem 406 theorem layer
```

## Public Lean entrypoints

```lean
import Worldtrace.PublicAPI
import Worldtrace.TheoremMap

#check Worldtrace.erdos_ternary_two
#check Worldtrace.four_power_contains_digit_two
#check Worldtrace.Genesis.low_tower_identity
#check Worldtrace.Navigation.orthogonal_origin_split
#check Worldtrace.Phase.phase_zero_to_one_shared_information
```

Historical compatibility entrypoints remain:

```lean
import GST.PublicAPI

#check GST.Problem406.contains_two_digit_of_nine_le
#check erdos_ternary_2_universal
```

## Review route

A reviewer should read the bundle in this order:

1. `WORLDTRACE_ARITHMETIC.md` — branch identity and layer map.
2. `REVIEWER_GUIDE.md` — proof-reading route.
3. `API_MAP.md` — promoted public names by layer.
4. `THEOREM_FAMILIES.md` — census of the frozen proof corpus.
5. `Worldtrace/TheoremMap.lean` — compile-checked promoted theorem surface.
6. `Worldtrace/PublicAPI.lean` — umbrella public facade.
7. `GST/Problem406/TheoremMap.lean` — compatibility theorem map.
8. `ErdosTernary2.lean` — monolithic proof object.
9. `FINISHER.lock.json` — exact pinned source and machine-readable census.

## Policy

Worldtrace names are promoted through thin wrapper modules first.  The internal proof corpus should not be mass-renamed until a dependency-safe migration and full CI pass are complete.
