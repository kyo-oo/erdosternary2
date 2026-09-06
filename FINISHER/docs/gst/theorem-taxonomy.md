# General Space Theory (GST) theorem taxonomy

This taxonomy is the management layer for the 630+ theorem space.

The generated manifest gives raw coverage. This file gives the conceptual classification.

## Taxonomy

| Class | Description | Public exposure |
| --- | --- | --- |
| Final theorem | Benchmark-facing Problem 406 result. | Public alias required. |
| Bridge theorem | Converts one major language into another. | Public when stable. |
| Structural theorem | Describes GST graph/navigation/certificate structure. | Curated docs. |
| Arithmetic theorem | Ternary digits, carries, residues, powers. | Public when reused externally. |
| Obstruction theorem | Eliminates bad/common-two-free cases. | Public when central. |
| Provider theorem | Supplies witnesses/certificates to the final bridge. | Public when central. |
| Tactical helper | Exists to close Lean proof branches. | Internal, generated manifest only. |
| Local helper | File-local algebra or case split. | Internal, generated manifest only. |

## Public naming rule

Use short Lean namespace names but full prose explanations:

```text
General Space Theory (GST)
```

In Lean:

```lean
GST.Arithmetic.*
GST.FourPower.*
GST.Problem406.*
```

In docs:

```text
General Space Theory (GST) arithmetic layer
General Space Theory (GST) Graph V2 layer
General Space Theory (GST) certificate bridge
```

## Current primary public names

```lean
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

The complete large theorem universe should be tracked by generated files:

```text
docs/gst/generated/theorem-manifest.md
docs/gst/generated/declaration-counts.md
```

This keeps the project reviewable without hiding the full theorem count.
