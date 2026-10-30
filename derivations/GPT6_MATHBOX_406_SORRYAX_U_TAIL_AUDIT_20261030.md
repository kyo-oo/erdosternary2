# Mathbox proof audit — GST 406 exact `sorryAx` source and physical U-flux repair

Date: 2026-10-30. Research branch:
`gpt6/problem406-u-flux-tail-closure-audit-20261030`.
Starting broken direct proof on
`gpt6/problem406-strict-universal-closure-attack-20261030`.

## 1. Fixed objective

```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2
```

No replacement hypothesis, no sorryAx, no circular dependency.
Previously verified all-K source bound `4^K < 3^ceil(24K/19)`
for K≥13 is accepted as established and not re-proved here.

## 2. First actual proof failure and dependency chain

Original strict build:
https://github.com/kyo-oo/erdosternary2/actions/runs/41039244379

```text
GSTInfiniteFourPowerNavigation.lean:176:2
linarith failed to find a contradiction
```

Inside `power_three_step_collision(K,q,hChild,hRightBad)`,
`hChild` is Happy on actual E=4^K, column 0, row 3+q,
and `hRightBad` is BAD on E*4^3, column 3, at *every*
row 3+j.

The attempted proof assembles:
- `hleft : 0 < graphPhaseWindow E 0 3 (q+1)`;
- `hright : graphPhaseWindow E 3 3 (q+1) ≤ 0`;
- exact width-three digit/carry conservation at p=3+q;
- Eq-III signed U vertical telescope, all finite heights;
- `hUPositive : 0 < 3P(4+q)-P(3+q)`;
- phase-digit and phase-carry boundary equations.

All of these are true statements. But they do NOT contain an
inequality comparing the two different phase windows or a sign
restriction on the *full* U telescope. The universal
`hRightAbs : ∀ j, ¬ HappyCell(...j)` is neither instantiated
at a decisive FUTURE row nor converted into a contradiction by
the final `four_power_collision_arith` / `linarith` tactic.

When Lean cannot close the declaration, its error recovery
uses `sorryAx`. `#print axioms` then shows `sorryAx` in
`power_three_step_collision`, propagating to
`four_power_happy_ge_three`, `gst_four_power_navigation_universal`,
and `GSTFourPowerDirectExistenceFromHappy.fourPowerDirectExistence_closed`.
This is not repaired by increasing tactic heartbeats.

## 3. Genuine-source finite-window discriminator (Wolfram exact)

Take K=8, E=4^8=65536, right 4^(K+3)=4^11.
At child row p=4, the original exact cell is (C,d)=(0,2):
a genuine Happy cell. The right edge is BAD for
p=3,4,5,6,7,8, then eventually Happy at p=10.
Exactly:
```text
graphPhaseWindow (4^8) 0 3 2 =  2
graphPhaseWindow (4^8) 3 3 2 = -4

P_8(4) = -185, P_8(5) = 111
3 P_8(5) - P_8(4) = 518 > 0
D_8(8) = -1536 < 0
```
where `D_K(p) = J_right(p)-64J_left(p)`.
Thus the source-specific *local* Eq-III derivative changes sign
before the right edge's first Happy gate. The finite-window
hypotheses satisfy the other conservation equations, and hence
cannot imply a right collision by finite sign monotonicity.

Module: `GST406PhysicalULocalSign.lean` (strict kernel CI separately).

## 4. New universal true-power terminal theorem — already GREEN

Module `GST406PhysicalUTerminal.lean`.
Exact all-K theorem, no original gate hypothesis:

Let `p ≥ 4^(K+4)`, a deliberately generous terminal
height. Every first-four-column physical cell has digit=carry=0,
and the width-three retained carry word Z=0.
Since GST U-charge is `U(0)=5`, the actual coupled potential
```text
P_K(p)=U(C_right)-64 U(C_left)+24 Z
      =5-64*5+0=-315.
```
Its signed vertical derivative is
```text
3 P_K(p+1)-P_K(p)=3*(-315)-(-315)=-630.
```
This matches the direct terminal jump values
`J(0,0)=10` at both edges:
`10-64*10=-630`.

Strict Lean PASS, including no sorryAx:
https://github.com/kyo-oo/erdosternary2/actions/runs/41046581852 .

Hence the raw coupled U potential is NOT zero in the terminal
zero-information tail. A positive earlier derivative does not
force positivity forever, and cannot contradict right BAD.

## 5. New exact compensated full-word equation — already GREEN

Module `GST406CenteredUConservation.lean`.

Define `Q_K(p)=P_K(p)+315`.
Then for EVERY K,p:
```text
D_K(p)+630 = 3 Q_K(p+1)-Q_K(p).
```
The true physical terminal is `Q_K(H)=0`.
At any starting b≤H with H≥4^(K+4), a formal all-K
telescope proves:
```text
Σ_{j=0}^{H-b-1} 3^j (D_K(b+j)+630)
  = 3^(H-b)*Q_K(H)-Q_K(b)
  = -Q_K(b).
```

Strict Lean PASS with no sorryAx:
https://github.com/kyo-oo/erdosternary2/actions/runs/41047669782 .

This is the complete finite physical conservation law with
correct baseline, NOT a conditional theorem. It repairs the
accounting missing from the old one-row collision tactic.

## 6. Nine exact physical initial charges

At source row b=3, the four carries and width-three carry
word depend only on the literal physical source `4^K mod27`.
Since `4^9=1 (mod27)`, `Q_K(3)` is periodic in K
with period 9. Independent exact Wolfram arithmetic gives:

| K mod9 | Q_K(3) | full-word compensated budget |
|---:|---:|---:|
| 0 | 58 | -58 |
| 1 | 226 | -226 |
| 2 | 264 | -264 |
| 3 | -78 | 78 |
| 4 | 96 | -96 |
| 5 | 402 | -402 |
| 6 | 440 | -440 |
| 7 | 224 | -224 |
| 8 | -246 | 246 |

The finite table comes with a proved modular reason for
its all-K validity; formal independent Lean implementation:
`GST406PhysicalNineCharges.lean` (strict CI separately).

The sign varies by residue class, so a generic all-K
positive/negative boundary assertion is incorrect.
Moreover, earlier strict Lean established an arbitrary-source
BAD witness `R=143*2^67` that is highly divisible by 2,
and whose 3-step child has a Happy row. The fully generic
sign-only transfer does not distinguish such sources from
literal powers `4^K`.

## 7. Exact missing mathematical implication

There is no longer an ambiguity about a mere Lean tactic.
The old theorem needs a genuinely SOURCE-SPECIFIC global
restriction on the signed interior trajectory:

For the exact physical 4^K source, a child Happy row at p≥3
must exclude an all-depth BAD right edge at power 4^(K+3).

The all-K terminal identity and budget prove the *correct
bookkeeping*. They do NOT impose a sign on the compensated
interior sum under the infinite BAD condition and do NOT
force an actual shared-two row for arbitrary K.

Do not promote `power_three_step_collision` to a proved
theorem, replace the missing sign claim with a hypothesis,
or plug it into production before an axiom-free proof.
Production `Solution.lean` remains unchanged.

**Verdict for current direct-U approach:** incomplete at one
precise all-depth, source-specific sign/exclusion implication;
not a syntax issue or an insufficient tactic budget.
