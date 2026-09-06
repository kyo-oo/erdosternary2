# General Space Theory (GST)

General Space Theory (GST) is the mathematical framework developed by Nidhish for organizing the digit, carry, graph, transport, and certificate machinery formalized in this repository.

This directory documents GST as the umbrella theory and also preserves the other major theorem families that support the Problem 406 / Erdős ternary-2 Lean artifact. The goal is not to rewrite the accepted proof artifact. The goal is to make the structure reviewable.

## Source-of-truth rule

Lean source is authoritative. These documents are a presentation layer.

`ErdosTernary2.lean` is treated as the preserved proof artifact: it is the battle-tested monolith imported by the comparator-facing solution and by the public wrapper layer. During presentation work, do not rename or rewrite declarations inside the monolith unless a separate proof-preserving refactor plan explicitly authorizes it.

## Main documentation map

| File | Purpose |
|---|---|
| `module-map.md` | Groups Lean modules into the major GST and supporting theorem families. |
| `theorem-family-index.md` | Organizes the 630+ theorem/declaration surface by mathematical role instead of one flat list. |
| `tactic-index.md` | Documents the custom GST tactics and where they belong. |
| `graph-v2.md` | Explains the Graph V2 production object and graph-law layer. |
| `proof-dependency-map.md` | Shows the high-level dependency flow into Problem 406. |
| `presentation-rules.md` | Records the rules for public naming, aliases, and fossil-artifact preservation. |

## Top-level theory families

The first-pass taxonomy is:

1. GST core tactics and finite-state infrastructure.
2. Canonical digit, carry, HappyCell, and Navigation objects.
3. Two-dimensional mixed emergence and divergence laws.
4. GST Graph V2 production objects and graph laws.
5. U2D and crossing-charge domination theorems.
6. Four-power direct arithmetic, residue filters, and LTE/periodicity laws.
7. Exponent-prefix and exponent-trit obstruction laws.
8. Affine channel automata and Chat-2 bad-channel realization.
9. Provider, creation-certificate, and no-axiom bridge pipeline.
10. Prefix-one ontological escape and tail projection.
11. Problem 406 public certificate and comparator surface.

## Reviewer stance

The public story should be calm:

- GST is the organizing framework.
- The theorem families are the checked Lean mechanism.
- The monolith is the preserved proof artifact.
- The public API exposes clean theorem names.
- The comparator surface verifies the Problem 406 statement.
