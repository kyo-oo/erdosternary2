# Worldtrace Arithmetic architecture

Worldtrace Arithmetic is the umbrella mathematics for this repository.  It is not a replacement name for General Space Theory (GST); it is the larger framework in which GST is one major pillar.

## One-sentence identity

Worldtrace Arithmetic studies arithmetic objects as trace-bearing worlds whose digit, carry, residue, navigation, collision, and obstruction states must remain consistent across transformations.

## Why the umbrella is needed

The finalized proof corpus is not a single-theory stack.  The FINISHER census separates the proof into many families: final Problem 406/universal theorem layer, four-power/residue arithmetic, canonical tail/collision/wave control, bridge/cascade/crossing, General Space Theory proper, carry/affine information, finite verification, ternary digit arithmetic, and custom automation.

GST is therefore not the whole mathematics.  GST is the graph/navigation/certificate pillar.  The other layers provide the arithmetic origin, residue stability, carry transport, finite certificates, and collision closure that make the final theorem work.

## Main layers

| Layer | Public role | Typical internal objects |
| --- | --- | --- |
| True Duality Transcendence | Arithmetic genesis layer. | `c`, `c_stable`, cascade cubic, two-world/three-world bridge. |
| Ternary Event Arithmetic | Digit and prefix mechanics. | `hasTernaryTwo`, `noTernaryTwo`, digit-at-position, first-k detection. |
| Carry-Information Theory | Exact carry movement under multiplication. | carry-at-position, affine carry, carry bounds, carry semigroup. |
| Residue Tower Theory | Stable local fingerprints. | mod `3^k` laws, stable residues, tower stabilization. |
| Four-Power Dynamics | Even-exponent engine. | adjacent powers of four, common-two witnesses, exponent-prefix obstruction. |
| General Space Theory | Navigation geometry. | spaces, Happy gates, navigation witnesses, creation certificates. |
| Canonical Collision Theory | Infinite-wave and bad-trace closure. | canonical tails, collisions, terminal extinction, residual NULL branches. |
| Phase-Cycle Algebra | Regeneration and cyclic information transport. | phase `0 -> 1 -> 2 -> 0`, shared information equations. |
| Finite Certificate Theory | Kernel-decided local closure. | local cell classifications, base cases, bounded structural decisions. |
| Problem 406 Layer | Final theorem surface. | `erdos_ternary_2_universal`, `Worldtrace.erdos_ternary_two`. |

## Proof-flow map

```text
True Duality Transcendence
  -> ternary/carry structural predicates
  -> residue tower stabilization
  -> four-power dynamics
  -> exponent-prefix obstruction
  -> General Space Theory navigation gates
  -> collision / bad-trace analysis
  -> phase-cycle regeneration
  -> finite terminal certificates
  -> Problem 406 final theorem
```

## Naming hierarchy

```text
Worldtrace Arithmetic
├── True Duality Transcendence
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

## Public API policy

The public API should not mass-alias every internal theorem.  It should expose the proof spine:

- final theorem;
- four-power and residue engine;
- exponent-prefix obstruction;
- navigation/certificate bridge;
- local cell classifiers;
- collision and phase-cycle closure;
- finite terminal certificates.

Internal declaration names remain stable until a dependency-safe migration is performed.  Public names are promoted through curated modules, starting with `Worldtrace.PublicAPI` and the existing `GST.Problem406.*` wrappers.
