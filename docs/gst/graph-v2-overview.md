# General Space Theory (GST) Graph V2 overview

GST Graph V2 is the graph/navigation interpretation layer for the Problem 406 formalization.

It should be read as the structural layer between arithmetic facts and the final theorem. The graph language gives names to how digit states, carry states, Happy cells, and creation certificates move through the proof.

## Core interpretation

In this repository, General Space Theory has three connected roles:

1. **State representation** — encode ternary digit and carry data as structured states.
2. **Navigation** — identify proof-relevant paths through those states.
3. **Certification** — turn arithmetic witnesses into graph/navigation certificates.

## Main concepts

| Concept | Role |
| --- | --- |
| Space | Ambient proof state or structural region. |
| Cell | Local digit/carry configuration. |
| HappyCell | A cell that satisfies the navigation gate condition. |
| Navigation | Existence of a GST-valid route through the arithmetic state space. |
| CommonTwo | A row where consecutive four-powers both expose ternary digit `2`. |
| CreationCertificate | A certificate that a number produces the required GST navigation structure. |
| CreationMaster | The universal master proposition for four-power creation certificates. |

## Relation to arithmetic

The graph layer is not a replacement for arithmetic. It is a way to organize arithmetic facts into proof-carrying structure.

```text
ternary digits
  -> carry dynamics
  -> HappyCell gates
  -> Navigation witnesses
  -> CreationCertificate
  -> Problem 406 theorem
```

## Relation to four powers

The four-power engine studies pairs:

```lean
4^K
4^(K+1)
```

The common-two and prefix-law layers identify where those powers produce the digit-two witnesses needed for the GST graph/navigation interpretation.

## Public bridge names

```lean
GST.FourPower.CommonTwo
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
GST.FourPower.creation_certificate_to_navigation
GST.FourPower.four_power_navigation_of_master
```

## Documentation boundary

This file describes the intended graph interpretation. The checked Lean proof source remains the formal authority. During the current professionalization phase, this documentation does not rewrite the monolith.
