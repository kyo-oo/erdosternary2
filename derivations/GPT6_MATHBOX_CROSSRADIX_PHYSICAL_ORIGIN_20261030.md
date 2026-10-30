# GST Problem 406 — Mathbox / Deep Research integration and strict boundary audit

**Research branch:** `gpt6/problem406-mathbox-crossradix-origin-20261030`  
**Forked from:** `gpt6/problem406-direct-hgate-collision-audit-20261030`, commit `e304d61c588f8bc264a87102c5e9ad521d633aaf`.  
**Original target, unchanged:** `∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K`.  
**Production:** `gst_four_power_third_wave_gate` and binder-free `questions/deepmind_problem_406/Solution.lean`.

## 1. Exact physical binary origin from the Deep Research report — proved

`GSTProblem406MathboxExactOrigin.lean` uses the **actual original source**
and the already proved short cutoff:

```lean
L(K) = (4*K-1)/3
t(K) = (3*L(K))/2+1

K>=13 =>
  (K%3=0 and 4^K=2^(t(K)+1)) or
  (K%3!=0 and 4^K=2^(t(K))).
```

The complete three-residue proof is kernel-checked. The same module
proves the **original** `CommonTwo K` is equivalent to a physical
same-row hit below `L(K)` of the exact origin source

```lean
if K%3=0 then 2^(t(K)+1) else 2^(t(K)).
```

The power identity is meaningful exact arithmetic; the equivalence
is logically the SAME unresolved universal existence statement
rather than a solution. It does not imply a hit merely because
the source has been normalized.

**Strict Lean run PASS (no `sorryAx` and no new custom axiom):**
https://github.com/kyo-oo/erdosternary2/actions/runs/41017155443 .

## 2. Mathematical limitation of fixed binary precision — proved

The research report proposed augmenting the carry automaton state with
a residue `rho mod 64`. That alone cannot force collision, even
after imposing source modulo three equals one.

For every `T>=0`, set

```math
m=2^T
R_m = \sum_{j=0}^{m-1}9^j = (9^m-1)/8.
```

Then

```math
4R_m = (9^m-1)/2
     = \sum_{p=0}^{2m-1}3^p,
```

whose base-three representation is **2m copies of digit 1**,
hence never contains the digit 2, even at position zero.
Also `R_m%3=1` and

```math
R_{2m} = R_m (1+9^m).
```

The multiplier is even, so iterating `T` binary doublings proves
`2^T | R_(2^T)`. Indeed by elementary 2-adic LTE, the exact
valuation is `v_2(R_m)=v_2(m)`, so `v_2(R_(2^T))=T`.

Consequently:

```lean
forall T, exists R>0,
  R%3=1 and 2^T|R
  and forall p>=1,
    not (digit3 R p=2 and digit3 (4*R) p=2).
```

This is implemented, **as an unbounded all-T proof**, in
`GSTProblem406MathboxBinaryResidueNoGo.lean`, together with an
explicit negation of the candidate theorem

```lean
not (forall R>0, R%3=1 -> 2^T|R -> GenericCommonTwo R).
```

**First complete unbounded theorem strict Lean CI PASS:**
https://github.com/kyo-oo/erdosternary2/actions/runs/41017816589 .
The later file addition receives its own subsequent strict check.

This is NOT a counterexample to the physical-power `4^K` theorem.
The word length of the constructed source is `2m-1`;
for `m=2^T`, its 2-adic order `T` is only logarithmic in
length, while the actual physical sources have order about
`(3/2)L`. Fixed-precision automata can never replace the
needed **length-adaptive** cross-radix condition.

Wolfram independently checked `T=0..7`, obtaining exact
binary valuations `0,1,..,7`, source mod 3 = 1 and no
digit-2 anywhere in each quadrupled source.
The universal proof is the Lean induction, not extrapolation.

## 3. What was NOT proved

No kernel term of the exact type

```lean
forall K, 5<=K -> K!=7 -> CommonTwo K
```

has been produced. Therefore `gst_four_power_third_wave_gate`
has NOT been proved, and the final `Solution.lean` must retain its
explicit `hGate` binder. Do not present any successful CI for
the two modules above as an unconditional proof of Erdős 406.

The old repository's three direct closure attempts still need
the physical source-specific interior-sign, propagation, or
residual-chord theorem identified in
`derivations/GPT6_DIRECT_HGATE_GST_KERNEL_OBLIGATIONS_20261030.md`.
Their Lean fails are substantive rather than mere tactic problems.

## 4. Constrained next mathematical approaches

- **Adaptive cross-radix length/valuation:** prove that the exact
  high-valuation source `R=2^(2K)`, at the exact
  cutoff `L=(4K-1)/3`, cannot lie in the full finite
  ternary BAD language. The target is exact all-K exclusion,
  not a counting estimate or another renamed hypothesis.
  An all-integer version for `R<3^L, R%3=1,
  2^(floor(3L/2)+1)|R` is stronger than necessary and
  currently backed by a finite test only.
- **GST signed physical U2D rectangle:** directly derive a
  nonnegative/controlled sign for the interior
  `reverseSurviveCode` and physical boundary,
  rather than applying `omega` to an unconstrained rectangle.
- **Exact 3-adic exponent termination:** combine the original
  `4^K` finite endpoint with the exponent-prefix isometry,
  not merely finite-prefix cylinders; arbitrary good/bad
  prefixes have genuine physical mimics at every finite depth.

All three routes remain open. The new no-go theorem excludes
the specific `carry x rho mod 2^T` **fixed-T** proof method,
not the adaptive version, and certainly not the original
conjecture.

## 5. Verification discipline

The acceptance contract is a binder-free term of the exact final
type, a strict Lean build, a `#print axioms` audit free of
custom-axiom proxies and `sorryAx`, and a comparator test on the
same commit. A proof that assumes `no_physical_endpoint_bad`
or `gst_four_power_third_wave_gate` under another name
is **conditional** and does not count.
