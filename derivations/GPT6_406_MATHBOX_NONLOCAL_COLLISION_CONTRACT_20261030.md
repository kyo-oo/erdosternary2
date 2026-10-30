# Mathbox GST 406 — pure-power nonlocal three-step collision audit (2026-10-30)

## Fixed objective

Do not change it:
```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    GSTFourPowerDirectResidue.digit3 (4^K) p = 2 ∧
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) p = 2
```

This record is NOT a proof of the fixed objective.
The final production `hGate` is not discharged.

## NEW axiom-free all-horizon theorem

Source: `GSTProblem406PurePowerNonlocalTransport.lean`
Branch: `gpt6/problem406-pure-power-nonlocal-contradiction-20261030`
Strict Lean CI PASS with no `sorryAx`:
https://github.com/kyo-oo/erdosternary2/actions/runs/41077343986

For EVERY finite horizon H≥9 there exists a literal natural exponent
K≥8 with:
- the genuine source pair `4^K, 4^(K+1)` has a shared digit-2 at row **4**;
- the genuine three-step parent pair `4^(K+3),4^(K+4)` has **no**
  shared digit-2 at ANY row `1≤p≤H`.

The proof starts with `K=8`, whose parent `4^11` first
shares a digit-2 with `4^12` at row 10.
To extend BAD through p+1, let `m=K+3` and choose
`a=(3-digit3(4^m,p+1)) mod 3`. The repository's exact
`pow4_exponent_trit_lift_digit` proves
`digit3(4^(m+a*3^p),p+1)=0`.
The exact `pow4_digit_period` proves all lower rows `≤p`
unchanged for both original powers and their neighbors.
The child row-4 Happy event persists, since p≥9.
Induct over p. No unbounded numerical scan, axiom or hypothetical
universal gate is used.

The new declarations are:
- `exponent_trit_preserves_lower_rows`
- `choose_exponent_trit_source_zero`
- `true_child_eight_parent_eleven_seed`
- `extend_pure_power_bad_parent`
- `arbitrary_pure_power_parent_bad_prefix`
- `no_uniform_bounded_three_step_reappearance`

## Exact implication for the missing `power_three_step_collision`

The original theorem can still be true: it quantifies a FIXED
natural K and bans a parent trajectory at EVERY depth.
The above result changes K with the finite horizon H. Thus
one cannot derive the all-depth contradiction from a fixed
number of local GST carries, phase windows, finite ternary
rows, or bounded x4 lookahead—even on perfect powers.

The old `GSTInfiniteFourPowerNavigation.power_three_step_collision`
remains RED at source line 176; the last `linarith` has no
sufficient sign/bridge hypothesis. The earlier terminal
U-potential (-315) and finite renormalized checksum are
true all-K identities:
https://github.com/kyo-oo/erdosternary2/actions/runs/41061241211
but they also cannot force an all-depth parent Happy event
using a fixed finite-height phase comparison.

## The same fixed target, now with correct quantitative focus

Let `L(K)=ceil(24*K/19)`, previously Lean-verified for K≥13.
The actual pure-power source `R=4^K` obeys

```text
R < 3^L(K),  v2(R)=2K.
```

Hence the target for K≥13 is precisely a prohibition of the
literal source `4^K` being BAD through its **K-dependent**
physical horizon `L(K)`. This is NOT a new hypothesis,
not a renamed form of the solution, and not proved here.

A noncircular contradiction must compare the exponent K's
exact binary-origin/odd-cofactor-one constraint with the
admissible ternary BAD path at the synchronised physical
horizon L(K). All source-independent U/phase conservation
identities and bounded lookahead transfers are insufficient.
The older broad all-R valuation 4L/3 barrier is false
(kernel countermodel: 143*2^67, 47 ternary places):
https://github.com/kyo-oo/erdosternary2/actions/runs/41039922733
Do not restore it as an axiom.

### Evidence classification

- All-horizon finite-prefix extension: **proved as written**, strict Lean.
- Terminal U boundary/renormalized checksum: **proved**, separate strict Lean.
- A finite-window GST three-step contradiction: **refuted** by this theorem.
- Fixed-natural-exponent, all-depth three-step collision:
  **not proved by these results**.
- Original universal `hGate`: **not proved**; remain unchanged.
