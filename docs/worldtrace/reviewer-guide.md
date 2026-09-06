# Worldtrace reviewer guide

This guide explains how to read the repository after the Worldtrace Arithmetic naming lock.

## Reading order

1. `README.md` — repository identity and current public entrypoints.
2. `WORLDTRACE.md` — definition of Worldtrace Arithmetic and its layer map.
3. `Worldtrace/PublicAPI.lean` — umbrella Lean facade.
4. `Worldtrace/TheoremMap.lean` — compile-checked promoted theorem surface.
5. `docs/worldtrace/theorem-promotion-map.md` — mapping from internal names to public names.
6. `GST/Problem406/TheoremMap.lean` — compatibility map for the previous GST-centered presentation.
7. `FINISHER/THEOREM_FAMILIES.md` — theorem-family census of the frozen proof source.
8. `ErdosTernary2.lean` — monolithic checked proof object.
9. `FINISHER/FINISHER.lock.json` — machine-readable lock for the frozen bundle.

## Main theorem

The main public theorem is:

```lean
Worldtrace.erdos_ternary_two
```

It states that for every `n >= 9`, the ternary expansion of `2^n` contains digit `2`.

The historical/internal final theorem remains:

```lean
erdos_ternary_2_universal
```

## Why Worldtrace Arithmetic

The proof stack is not only General Space Theory.  General Space Theory is the navigation-geometric pillar, but the proof also depends on the original arithmetic genesis layer, ternary event predicates, carry-information transport, residue towers, four-power dynamics, canonical collision closure, phase cycles, and finite certificates.

## Layer interpretation

| Layer | What to verify |
| --- | --- |
| Genesis | Cascade constant, low-tower identity, structural modular computation, cascade lift. |
| Ternary | Digit-two predicates, finite prefix scanning, position witnesses. |
| Carry | Carry bounds, carry-forward laws, affine carry transport, shared information. |
| Residue | Stable low residues and exponent-prefix obstructions. |
| FourPower | Consecutive four-power witnesses and creation certificates. |
| Navigation | Origin fingerprints, navigation constants, graph lifts, shifted equivalences. |
| Collision | Bad-trace closure, terminal NULL branches, local chord classifiers. |
| Phase | Regeneration and the conserved 0->1->2->0 seed cycle. |
| Certificate | Finite kernel certificates and final bridge packages. |
| PublicAPI | Final Problem 406 theorem and selected stable aliases. |

## Audit expectation

The public wrapper modules should compile without changing proof bodies.  The monolith is still the proof source.  The Worldtrace layer is the professional mathematical interface over that source.

## What not to assume

- Do not assume every internal theorem has already been renamed.
- Do not read `GST` as the entire branch; it is one pillar.
- Do not treat the FINISHER census as a public API list; it is the full proof inventory.
- Do not remove historical aliases until a dependency-safe migration is complete and CI is green.
