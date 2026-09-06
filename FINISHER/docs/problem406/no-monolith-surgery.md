# No Monolith Surgery Rule

During the public presentation phase, do not edit `ErdosTernary2.lean`.

The monolith is preserved as the proof artifact. New work should happen in wrapper files, documentation files, theorem maps, or additive CI checks.

Direct cleanup of the monolith is a later phase and requires a separate plan plus a green wrapper layer first.
