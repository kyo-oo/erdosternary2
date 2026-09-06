# Worldtrace Arithmetic

**Worldtrace Arithmetic** is the public umbrella name for the mathematics in this repository.

It studies arithmetic objects as trace-bearing worlds: structures whose digit states, carry fields, residue towers, navigation positions, collision layers, and finite/infinite obstruction behavior must remain mutually consistent.

The Erdős ternary-2 / Problem 406 proof is the first flagship Lean-formalized theorem presented through this framework.

## Core thesis

Classical arithmetic often studies a number by value, congruence class, or expansion.  Worldtrace Arithmetic studies how an arithmetic object keeps an identifiable trace while it moves through several coupled representations:

```text
integer value
  -> ternary digit field
  -> carry field
  -> residue tower
  -> navigation state
  -> collision/wave state
  -> certificate or obstruction
```

The point is not to replace ordinary number theory.  The point is to preserve origin, transport, and consistency information that ordinary local modular views can discard.

## Position of General Space Theory

General Space Theory (GST) is a major pillar of Worldtrace Arithmetic, not the whole framework.

GST supplies the navigation-geometric language: spaces, graph states, gates, witnesses, and certificates.  Other theorem families supply the arithmetic engine, including ternary digit arithmetic, carry dynamics, residue laws, exponent-prefix obstruction, collision/wave control, bridge/cascade structure, and finite certificate layers.

## Public framework layers

| Layer | Role |
| --- | --- |
| True Duality Transcendence | Early arithmetic genesis layer connecting the two-world and three-world views. |
| Ternary Event Arithmetic | Digit, prefix, and finite-position mechanics. |
| Carry-Information Theory | Exact carry transport and affine carry state. |
| Residue Tower Theory | Stable low residues and modulus towers. |
| Four-Power Dynamics | Consecutive four-power, common-two, and exponent-prefix laws. |
| General Space Theory | Navigation-geometric pillar: graph states, gates, spaces, certificates. |
| Canonical Collision Theory | Collision, wave, terminal-extinction, and bad-trace obstruction. |
| Phase-Cycle Algebra | Regeneration and conserved phase transport. |
| Finite Certificate Theory | Kernel-decidable local certificates used by the formal proof. |
| Problem 406 Layer | Final theorem surface for the Erdős ternary-2 result. |

## Lean naming policy

The existing Lean proof corpus uses historical namespaces such as `GST.*`.  These names remain stable for compatibility.

New public prose should use:

```text
Worldtrace Arithmetic
```

New umbrella imports should use:

```lean
import Worldtrace.PublicAPI
```

The `Worldtrace` Lean module is a thin public facade over the checked proof corpus.  It does not rewrite proof bodies.

## Flagship theorem

```lean
Worldtrace.erdos_ternary_two
```

states the reviewer-facing form of the final theorem:

```text
for every n >= 9, the ternary expansion of 2^n contains a digit 2.
```

## Review policy

The repository should present three levels:

1. **Worldtrace identity** — the branch-level mathematical frame.
2. **Curated public API** — stable names for the proof spine.
3. **Frozen proof corpus** — full Lean evidence, import closure, theorem census, and audit files.

Do not mass-rename the proof corpus without a dependency-safe migration.  Promotion happens through stable wrapper modules and documentation first.
