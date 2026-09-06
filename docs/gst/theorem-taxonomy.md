# Worldtrace Arithmetic theorem taxonomy

This taxonomy is the management layer for the large theorem space in the Problem 406 proof corpus.

The generated manifest gives raw coverage.  This file gives the conceptual classification and separates the full Worldtrace Arithmetic framework from the General Space Theory pillar.

## Taxonomy

| Class | Description | Public exposure |
| --- | --- | --- |
| Final theorem | Benchmark-facing Problem 406 result. | Public alias required. |
| Genesis theorem | Early arithmetic bridge/cascade theorem. | Public when part of the main narrative. |
| Bridge theorem | Converts one major language into another. | Public when stable. |
| Structural theorem | Describes graph/navigation/certificate structure. | Curated docs and API wrappers. |
| Arithmetic theorem | Ternary digits, carries, residues, powers. | Public when reused externally. |
| Obstruction theorem | Eliminates bad/common-two-free cases. | Public when central. |
| Collision theorem | Controls canonical tails, waves, bad traces, and terminal branches. | Public when central. |
| Phase theorem | Describes regeneration and cyclic information transport. | Public when central. |
| Provider theorem | Supplies witnesses/certificates to the final bridge. | Public when central. |
| Tactical helper | Exists to close Lean proof branches. | Internal, generated manifest only. |
| Local helper | File-local algebra or case split. | Internal, generated manifest only. |

## Public naming rule

Use the branch name for the whole mathematics:

```text
Worldtrace Arithmetic
```

Use General Space Theory only for the navigation-geometric pillar:

```text
General Space Theory (GST)
```

In Lean, both surfaces may coexist:

```lean
Worldtrace.*
GST.Arithmetic.*
GST.FourPower.*
GST.Problem406.*
```

In docs, avoid implying that every theorem belongs to GST.  Prefer:

```text
Worldtrace Arithmetic's carry-information layer
Worldtrace Arithmetic's four-power dynamics layer
General Space Theory's navigation layer
Worldtrace Arithmetic's final Problem 406 theorem layer
```

## Current primary public names

```lean
Worldtrace.erdos_ternary_two
Worldtrace.four_power_contains_digit_two
Worldtrace.adjacent_four_power_identity
Worldtrace.prefix_one_navigation_lift
Worldtrace.four_power_creation_master
GST.Problem406.contains_two_digit_of_nine_le
GST.Arithmetic.digit3
GST.Arithmetic.carry4
GST.Arithmetic.HappyCell
GST.Arithmetic.Navigation
GST.FourPower.CommonTwo
GST.FourPower.DirectExistence
GST.FourPower.exponentPrefix
GST.FourPower.exponentTrit
GST.FourPower.no_common_two_exponent_trit_obstruction
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
```

## Raw inventory destination

The complete theorem universe should be tracked by generated files:

```text
docs/gst/generated/theorem-manifest.md
docs/gst/generated/declaration-counts.md
FINISHER/THEOREM_FAMILIES.md
```

This keeps the project reviewable without hiding the full theorem count.
