# Worldtrace Arithmetic

**Worldtrace Arithmetic** is the public umbrella name for the mathematics in this repository.

It studies arithmetic objects as trace-bearing worlds: structures whose digit states, carry fields, residue towers, navigation positions, collision layers, phase cycles, and finite/infinite obstruction behavior must remain mutually consistent.

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
  -> phase cycle
  -> certificate or obstruction
```

The point is not to replace ordinary number theory.  The point is to preserve origin, transport, and consistency information that ordinary local modular views can discard.

## Position of General Space Theory

General Space Theory (GST) is a major pillar of Worldtrace Arithmetic, not the whole framework.

GST supplies the navigation-geometric language: spaces, graph states, gates, witnesses, and certificates.  Other theorem families supply the arithmetic engine, including the original True Duality Transcendence layer, ternary digit arithmetic, carry dynamics, residue laws, exponent-prefix obstruction, collision/wave control, bridge/cascade structure, phase regeneration, and finite certificate layers.

## Public framework layers

| Layer | Public Lean module | Role |
| --- | --- | --- |
| True Duality Transcendence / genesis arithmetic | `Worldtrace.Genesis` | Original early monolith engine: cascade constant, low-tower identity, structural modular computation, cascade lift. |
| Ternary Event Arithmetic | `Worldtrace.Ternary` | Digit, prefix, finite-position mechanics, and digit-two witnesses. |
| Carry-Information Theory | `Worldtrace.Carry` | Exact carry transport, affine carry state, and shared information. |
| Residue Tower Theory | `Worldtrace.Residue` | Stable low residues, residue fingerprints, and exponent-prefix obstruction. |
| Four-Power Dynamics | `Worldtrace.FourPower` | Consecutive four-power, common-two, adjacent-wave, and creation-master laws. |
| General Space Theory | `Worldtrace.Navigation` | Navigation-geometric pillar: graph states, gates, origin fingerprints, spaces, certificates. |
| Canonical Collision Theory | `Worldtrace.Collision` | Collision, wave, terminal-extinction, residual NULL, exact-rectangle, and bad-trace obstruction. |
| Phase-Cycle Algebra | `Worldtrace.Phase` | NULL regeneration, seed cycle, and conserved phase transport. |
| Finite Certificate Theory | `Worldtrace.Certificate` | Kernel-decidable local certificates and bridge packages used by the formal proof. |
| Problem 406 Layer | `Worldtrace.PublicAPI` | Final theorem surface for the Erdős ternary-2 result. |

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

The promoted theorem index is:

```lean
import Worldtrace.TheoremMap
```

The `Worldtrace` Lean modules are thin public facades over the checked proof corpus.  They do not rewrite proof bodies.

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
2. **Curated public API** — stable names for the proof spine and major supporting theorem families.
3. **Frozen proof corpus** — full Lean evidence, import closure, theorem census, and audit files.

Do not mass-rename the proof corpus without a dependency-safe migration.  Promotion happens through stable wrapper modules and documentation first.
