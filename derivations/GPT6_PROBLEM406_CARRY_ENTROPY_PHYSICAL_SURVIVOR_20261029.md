# Problem 406 — physical affine carry-entropy contraction

**Branch:** `gpt6/problem406-cubic-universal-research-20261029`  
**Goal:** `∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K`  
**Status:** The universal target is NOT proved by the present contraction.
The result is an unbounded-depth structural theorem, plus independent
finite audit of original physical 4-power representatives.

## Exact original physical source-neighbor reduction

From the kernel-certified affine identity, put
`A_K=(4^K-1)/3`. Then `A_{K+1}=4A_K+1`, and the original
`CommonTwo(K)` is equivalent to `∃j≥0` where both the `j`th
base-3 digit of `A_K` and of `4A_K+1` are 2. This is **not**
a substituted generic target: the original powers are recovered
digit-for-digit from the one-trit shift.

For any base-three source word `X`, write its digits `a_j∈{0,1,2}`,
and perform ordinary long multiplication by four plus one.
The initial carry is `c_0=1`; given carry `c_j∈{0,1,2,3}`,
the next target digit and carry are

```
b_j = (4 a_j + c_j) mod 3,
c_(j+1) = floor((4 a_j + c_j)/3).
```

A forbidden *common-two* event is `a_j=b_j=2`. It occurs
precisely for `a_j=2` and `c_j∈{0,3}`.

The noncollision transition matrix (rows = incoming state,
columns = next state, states 0,1,2,3) is

```text
M = [[1,1,0,0],
     [1,1,0,1],
     [1,0,1,1],
     [0,1,1,0]].
```

The allowed two-digit word totals `M² 1` are exactly
`(5,7,7,6)`. Consequently, no matter the entering carry,
two consecutive ternary positions admit at most **7** of the
`3²=9` possible source-digit pairs.

Let `S_p(c)` count common-two-free length-`p` source words
starting at carry `c`. Then
`S_0(c)=1` and `S_(p+1)=M S_p`, whence, for EVERY `m≥0`,
ALL incoming states `c` and arbitrarily large `p`,

```text
S_(2m)(c) ≤ 7^m,
S_(2m+1)(c) ≤ 3 * 7^m.
```

**Proof:** From any carry, each pair of source trits offers
at most seven admissible completions; inductively multiply the
bound for every earlier stage. The odd bound uses at most three
additional trits. A Lean formalization of this four-state
recurrence and induction is in
`GSTProblem406CarryEntropyBound.lean`, with strict kernel CI
in `.github/workflows/gpt6_problem406_carry_entropy.yml`.

Wolfram independently computed
`CharacteristicPolynomial[M,x] = x^4 - 3 x^3 + 4 x - 2`
and spectral radius `2.48119430409...` (numerical). The
simple explicit seven-of-nine bound avoids reliance on a
spectral approximation.

## Original exponent residue population, not sampled surrogates

The existing prefix isometry asserts for all `p,a,b`:

```text
A_a mod 3^p = A_b mod 3^p  iff  a mod 3^p = b mod 3^p.
```

If this module and its finite-surjectivity successor are kernel
verified, the map `K mod 3^p ↦ A_K mod 3^p` is bijective.
Therefore, the same count `S_p(1)` applies exactly to
ALL `3^p` original exponent residue classes modulo `3^p`.

Even without relying on unverified Lean dependencies, the number
theoretic bijection follows from `ord_(3^(p+1))(4)=3^p`:
if `4^a ≡ 4^b mod 3^(p+1)`, then `a≡b mod 3^p`.
Since `4^K=1+3A_K`, congruence of the `A_K` modulo `3^p`
is equivalent to congruence of the powers modulo `3^(p+1)`.

Independent exact audit (not a universal proof):

```text
p        0    1    2    3    4    5    6    7     8
3^p      1    3    9   27   81  243  729 2187  6561
survive  1    3    7   18   44  110  272  676  1676
```

Reproduce with
`python3 scripts/gst_406_carry_entropy_independent_audit.py`.
For each `p`, it **exhaustively** enumerates K=0,...,3^p-1
using independent modular exponentiation, checks the cardinality
and uniqueness of actual physical affine residues, and compares
the original source-neighbor trit predicate against the separate
carry recurrence.

## Important interpretation

The fraction of exponent residue classes with no shared 2
among the first `2m` affine positions is bounded by

```text
S_(2m)(1) / 3^(2m) ≤ (7/9)^m.
```

This proves a strong *zero-Haar-measure* statement on the
3-adic exponent parameter space, and gives a Hausdorff-dimension
upper bound `log(7)/log(9) < 1` for its infinite survivor set.

But it does **not** prove that no particular natural integer
K≥5, K≠7 lies in that measure-zero exceptional set.
The all-zero 3-adic affine coordinate, corresponding to K=0,
is an example of an infinite controller survivor.
Moreover, some finite survivors at large depths are
actual large positive original perfect-power exponents:
finite-survivor elimination cannot by itself yield the target.

The next genuinely decisive implication must be:
**every natural exponent K≥5 except K=7 eventually exits
this carry automaton**, using the finite size/archimedean
termination of the actual perfect-power orbit, not mere
small measure or generic 3-adic prefix exclusion.

No custom axiom, custom universal hGate premise, or
unbounded numerical extrapolation may substitute for this.

## Density-one corollary for actual natural exponents

By the finite exponent-prefix isometry (strict CI PASS
https://github.com/kyo-oo/erdosternary2/actions/runs/40860951943),
the exact noncollision automaton count at depth 2m is also the
number of exponent residue classes K<3^(2m) whose physical pair
4^K and 4^(K+1) has not yet met a common-two position among
rows 1,...,2m. Therefore

```text
#{ K<3^(2m) : not CommonTwo(K) } ≤ 7^m.
```

Indeed global no-CommonTwo implies finite prefix survival.
Consequently any infinite set of exceptional natural exponents
has natural density zero and counting function
`O(N^(log(7)/log(9)))` with exponent approximately 0.8856.

This is a rigorous number-theoretic density-one result by
finite-state counting and physical finite-prefix isometry.
The standalone Lean carry bound and independent finite physical
audit passed strict CI:
https://github.com/kyo-oo/erdosternary2/actions/runs/40860395471
The specific automaton-to-physical cardinality transfer is
explained here mathematically but is not yet separately written
as a kernel-certified finite-set-counting declaration.

## Second route: new all-scale physical hGate families

A separate exact derivation in
`GSTProblem406UnboundedPureThreePowerFamily.lean` uses
`c_L=(4^(3^L)-1)/3^(L+1)`.
The exact recurrence

```text
c_(L+1) = c_L + 3^(L+1) c_L^2 + 3^(2L+1) c_L^3
```

and `c_4 mod243=178` prove `c_L mod243=178`
for EVERY L>=4. For K=u*3^L and ANY natural u, the source
and neighbor quotient's first five trits are those of
`178*u` and `712*u`, respectively. Thus any u with a
common digit 2 among these two words in positions j<5 gives
an exact original CommonTwo certificate at row `L+1+j`.

In particular ALL u with u mod243=1 satisfy the fifth-trit
condition, proving `CommonTwo(u*3^L)` for every L>=4,
including the infinite family K=3^L.

Wolfram's independent exact finite residue classification shows
**169 of the 243 possible u residues mod243** have some common
2 among the first five quotient trits. This is unconditional
mathematics at the stated finite-width modular scale; strict
Lean verification of the wider family is tracked separately
in the dedicated workflow. Nothing here is extrapolated to
the remaining 74 classes or to all arbitrary K.
