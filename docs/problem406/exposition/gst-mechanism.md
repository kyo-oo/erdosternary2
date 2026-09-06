# GST Mechanism Layer

The GST layer explains the mechanism behind the arithmetic certificate. It is not a replacement for the Lean proof; it is the structured map of why the proof works.

## Main mechanism families

- Carry transport: exact movement of ternary carry states across positions.
- Four-power arithmetic: direct control of digit-two creation in consecutive powers of four.
- Affine channels: finite-state channels used to organize prefix and residue behavior.
- Graph V2: navigation and descent structure for the proof space.
- U2D and mixed emergence: supporting theorem families that connect local digit/carry events to global obstruction behavior.
- Prefix-one escape: the tail-navigation family used to prevent unresolved bad channels from persisting indefinitely.

## Presentation rule

Each family stays first-class. The professional exposition should not collapse every result into a vague GST slogan. The reviewer should be able to trace which exact Lean module supports each step.

## Boundary

GST terminology is allowed in docs and theorem maps, but public Lean wrappers should remain ordinary Lean: definitions, abbreviations, theorem aliases, and direct bridges to existing declarations.
