# GST Graph V2

GST Graph V2 is the graph/navigation layer of General Space Theory (GST). It organizes digit/carry arithmetic as a two-dimensional production lattice rather than as isolated residue calculations.

The production source is `GSTGraphV2Production.lean`. The law source is `GSTGraphV2ProductionLaws.lean`.

## Core idea

Graph V2 should be presented as one absolute arithmetic sheet:

```text
source energy E
horizontal coordinate t  = multiplication by 4 / exponent-time direction
vertical coordinate p    = ternary digit/carry depth
cell(E,t,p)              = all arithmetic observables at that coordinate
```

Finite rectangles, origin frames, residual frames, and canonical cut frames are observations or re-coordinatizations of the same sheet. They are not alternative graphs.

## Main objects

| Object | Source | Meaning |
|---|---|---|
| `Cell` | `GSTGraphV2Production.lean` | Production state at one `(E,t,p)` coordinate. |
| `Sheet` | `GSTGraphV2Production.lean` | Infinite grid of cells. |
| `graph` | `GSTGraphV2Production.lean` | The sheet generated from a source energy. |
| `Direction` | `GSTGraphV2Production.lean` | Horizontal x4 or vertical ternary direction. |
| `Edge` | `GSTGraphV2Production.lean` | Directed graph edge between cells. |
| `Lattice` | `GSTGraphV2Production.lean` | Vertex and edge functions for the graph. |
| `Neighborhood` | `GSTGraphV2Production.lean` | Center cell plus horizontal and vertical successors. |
| `Rectangle` | `GSTGraphV2Production.lean` | Finite horizontal rectangle observed inside the infinite sheet. |
| `OriginCoordinates` | `GSTGraphV2Production.lean` | Origin prefix/suffix/phase decomposition. |
| `OriginFrame` | `GSTGraphV2Production.lean` | Full, neutral-tail, and phased-tail coordinates. |
| `ResidualFrame` | `GSTGraphV2Production.lean` | Residual production frame used by the proof seam. |
| `ResidualGateFrame` | `GSTGraphV2Production.lean` | Residual frame pinned to a child gate row. |
| `CanonicalCutFrame` | `GSTGraphV2Production.lean` | Canonical production-cut frame. |

## Main laws

| Theorem | Source | Meaning |
|---|---|---|
| `horizontal_digit_exact` | `GSTGraphV2ProductionLaws.lean` | The horizontal edge is exactly the x4 digit edge. |
| `vertical_carry_exact` | `GSTGraphV2ProductionLaws.lean` | The vertical edge is exactly the ternary carry edge. |
| `navigation_nullspace_flux_exact` | `GSTGraphV2ProductionLaws.lean` | Equation-I/nullspace flux identity for each cell. |
| `origin_frame_phased_state_exact` | `GSTGraphV2ProductionLaws.lean` | Full state and re-phased tail agree in carry/digit coordinates. |
| `canonical_cut_neutral_tail` | `GSTGraphV2ProductionLaws.lean` | Canonical production cut exposes neutral tail state. |
| `residual_gate_neutral_tail` | `GSTGraphV2ProductionLaws.lean` | Residual gate row exposes neutral higher-level tail. |
| `residual_gate_left_is_phased_tail` | `GSTGraphV2ProductionLaws.lean` | Residual left endpoint is the re-phased U-tail state. |
| `residual_right_absolute_state_exact` | `GSTGraphV2ProductionLaws.lean` | Residual right endpoint matches the absolute parent sheet. |

## Relationship to other theorem families

Graph V2 sits above the arithmetic core and below the final certificate layer:

```text
canonical digit/carry objects
        ↓
2D Mixed Emergence and U2D transport
        ↓
GST Graph V2 production sheet
        ↓
Graph V2 laws and residual frames
        ↓
Prefix-one / four-power certificate bridge
        ↓
Problem 406 theorem surface
```

## Presentation rule

Do not present Graph V2 as a metaphor. Present it as a Lean-defined data structure plus theorem-backed edge laws. The diagrams and LaTeX exposition can be dramatic later, but the Lean story should be precise: cells, edges, frames, and exact identities.
