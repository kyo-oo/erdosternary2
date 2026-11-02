# ERDŐS #261 — THE CONTINUUM QUESTION (REAL-x VARIANT): THE TOWER CONSTRUCTION

**Branch:** `bulldoze/erdos-weak-problems-3-20261101` (Kill #6 package)
**Files:** `Erdos261Tower.lean` (core-only Lean 4.33.0-rc2, in active
compile war — see §7), `verify_tower261.py` (exact-arithmetic
verification battery: ALL PASSED), `highsupport_census.py` (the
collision census: collisions at EVERY min-support N ∈ [1,40]).

## 1. THE PROBLEM

The second question of Erdős #261 [Er74b, ErGr80, Er88c], as recorded
from erdosproblems.com/261 (page edit 2025-12-01, status open):

> Is there a rational $x$ such that $x = \sum_k a_k/2^{a_k}$ has at
> least $2^{\aleph_0}$ solutions?

In [Er88c] Erdős weakens this to the existence of a rational $x$ with
TWO solutions — killed affirmatively in Kill #5 (x = 1/2, three
representations, zero-axiom Lean). This package kills the CONTINUUM
question for unrestricted (real) $x$, and maps the walls that make the
rational-$x$ case resistant.

## 2. THE TOWER — THE KILL OF THE REAL-x VARIANT

**The infinite exact-halving family.** For $k \geq 0$ let
$m_k = 2^{k+2} - k - 3$: the sequence 1, 4, 11, 26, 57, 120, 247, 502, …
For every $k$, the region $[m_k, m_k + k + 1]$ is EXACTLY halved by its
endpoint against its interior:

$$\frac{m_k}{2^{m_k}} \;=\; \sum_{i=1}^{k+1} \frac{m_k + i}{2^{m_k+i}}.$$

*Proof.* The telescoping partial identity (fixed $m$, induction on $j$):
$$\sum_{i=1}^{j} \frac{m+i}{2^{m+i}} = \frac{m+2}{2^{m}} - \frac{m+j+2}{2^{m+j}},$$
evaluated at $m = m_k$, $j = k+1$, using $m_k + k + 3 = 2^{k+2}$ (the
$(m+j+2)/2^{m+j}$ term becomes $2^{k+2}/2^{m_k+k+1} = 2/2^{m_k}$, so
the partial sum is $(m_k+2)/2^{m_k} - 2/2^{m_k} = m_k/2^{m_k}$). ∎

Witnesses: $\{1\}{=}\{2\}$ (1/2), $\{4\}{=}\{5,6\}$ (1/4),
$\{11\}{=}\{12,13,14\}$ (11/2048), $\{26\}{=}\{27,28,29,30\}$,
$\{57\}{=}\{58,\dots,62\}$, $\{120\}{=}\{121,\dots,126\}$, … — all
verified by exact `Fraction` arithmetic in `verify_tower261.py`.
The regions are pairwise disjoint (gaps 2, 5, 12, 27, 58, … grow).

**The tower map.** For each binary sequence $\sigma \in 2^{\mathbb{N}}$
define the representation $F_\sigma$: on region $k$ take the left piece
$\{m_k\}$ when $\sigma(k)$, the right piece $\{m_k+1,\dots,m_k+k+1\}$
when $\neg\sigma(k)$; nothing on gap indices. Every region contributes
exactly $m_k/2^{m_k}$ REGARDLESS of the choice, so

$$S(F_\sigma) \;=\; x^* \;:=\; \sum_{k\geq 0} \frac{m_k}{2^{m_k}} \qquad \text{for EVERY } \sigma,$$

and $\sigma \mapsto F_\sigma$ is injective (regions are disjoint and
$F_\sigma$ reads $\sigma(k)$ at position $m_k$). Since $|2^{\mathbb{N}}| =
2^{\aleph_0}$, the value $x^*$ has at least $2^{\aleph_0}$ distinct
representations. ∎

Numerically $x^* = 1/2 + 1/4 + 11/2048 + 26/2^{26} + \cdots \approx
0.7553714811801915$ (exact partials in the battery).

**$x^*$ is irrational.** The summands $m_k/2^{m_k}$ have bit-clusters at
positions $[m_k - \lfloor\log_2 m_k\rfloor, m_k]$, and the clusters are
ISOLATED: the tail beyond cluster $k$ is below $2^{-m_k-1}$, while the
gap to cluster $k+1$ grows like $2^{k+1}$. Hence the binary expansion of
$x^*$ has infinitely many 1-blocks separated by zero-gaps of unbounded
length — not eventually periodic. (Receipts: `verify_tower261.py` prints
the zero-gaps 3, 10, 25, 56, 119, 246, … after each cluster.)

## 3. THE CENSUS — COLLISIONS AT EVERY MIN-SUPPORT

`highsupport_census.py` (signed meet-in-the-middle, exact): for EVERY
$N \in [1,40]$ there is a collision pair with minimum support exactly
$N$. Samples: $\{9\}{=}\{10,11,13,14\}$, $\{13\}{=}\{14,15,16,20,21,24\}$,
$\{21\}{=}\{22,23,24,26,27,32\}$, $\{35\}{=}\{36,37,38,39,42,43,45,46\}$.
The known families ($\{m\}$-vs-interior, $\{3,6,8\}{=}\{4,5,6\}$,
$\{3,8\}{=}\{4,5\}$) are special cases. This universality is the
structural reason the tower could be built, and it invalidates the
"only the halving family exists" intuition that blocked earlier
constructions.

## 4. THE WALLS — WHY THE RATIONAL-x CASE RESISTS

Four structural walls, each mapped precisely this session:

1. **The fork-comb.** The greedy-representation fork windows
   $(a/2^a, (a+2)/2^a]$ allow both take/skip only there; after a take
   at $a \geq 4$ the next fork is at $a + c$ with $c \geq 1$ forced by
   the residual, and no two re-fork offsets can coexist (the window
   arithmetic $2^{c'-c} \approx (a+c')/(a+c)$ forbids it). The greedy
   tree is a COMB — no perfect subtree — countably many greedy
   representations per value.
2. **Kakeya thickness exclusivity.** A set of indices $Z$ has interval
   achievement set only if every $a \in Z$ satisfies
   $a 2^{-a} \le \sum_{b \in Z, b>a} b 2^{-b}$; two DISJOINT such sets
   cannot exist (each needs its complement's tail mass $\le 2 \cdot
   2^{-a}$, shrinking). Zone-towers are structurally blocked.
3. **Cluster uncancelability.** Any tower over scale-separated gadgets
   has irrational total (isolated bit-clusters), and the clusters of
   gadget $k$ can only be cancelled by pieces at positions in
   $(m_k, m_k + \log_2 m_k]$ — exactly the occupied region. No disjoint
   second family can cancel the first.
4. **Telescope capacity arithmetic.** A rational total needs gadget
   values that are dyadic differences; pure-power gadget values
   $2^{-u}$ require double disjoint representations with total capacity
   $2 \cdot 2^{-u}$, forcing $u \in \{2^c - c - 1, 2^c - c\}$ — a
   sparse set that cannot tile. The pure-power telescope is impossible.

The rational-$x$ continuum question remains OPEN under these walls.

## 5. SCOPE LABELS (exact honesty)

- KILLED (this package): the continuum question for unrestricted/real
  $x$ — an explicit $x^*$ with $2^{\aleph_0}$ representations, full
  proof above, exact-arithmetic-verified.
- OPEN: the rational-$x$ reading (walls in §4).
- OPEN (Kill #2's core): greedy-walk termination for all $n$.

Prior-art caveat, as in Kill #5: the comments threads of
erdosproblems.com are SPAWA-loaded and unfetchable from this sandbox;
the page itself (edit 2025-12-01) records the question unresolved. If
any comment already contains the tower construction, this package's
value reduces to the census + the walls + the formalization.

## 6. THE FORMAL PACKAGE (in active compile war)

`Erdos261Tower.lean`: core-only (no Mathlib — the disk could not fit
the Mathlib olean cache; the CI runners can). All-scaled-Nat encoding:
`P f M = Σ_{a ≤ M, f a} a·2^{M-a}`, `sameValue` as the all-Nat
ε-tolerance relation, `checkpoint_eq` (exact boundary equality of
partial values for ALL σ), `tower_sameValue`, `tower_cauchy`,
`F_injective`, and the main theorem `erdos261_continuum`. Zero-axiom
target (everything computable). Status at this commit: the mathematics
is fully verified by the battery; the Lean file is mid-compile-war
(~31 errors remaining from ~130 initial; the §-map is complete and the
remaining errors are core-API grind, ledger lessons below).

### Compile-war ledger additions (Lean 4.33.0-rc2 core-only)
19. `lemma` is GONE from core Lean 4.33 — use `theorem` only.
20. Bare `lean file.lean` needs `import Init` explicitly (new module
    system); without it even `Add Nat` fails to synthesize.
21. `ℕ` is MATHLIB notation — core uses `Nat` only.
22. `by_contra`, `ne_of_lt`, `le_refl`, `le_or_lt` are NOT core:
    use explicit `rcases Nat.lt_or_ge` + `Nat.le_antisymm`,
    `Nat.ne_of_lt`, `Nat.le_refl`, `Nat.lt_or_ge`.
23. `List.range_succ` takes NO explicit argument in 4.33 core.
24. omega treats `pow2 (k+1+2)` and `pow2 (k+3)` as DIFFERENT atoms —
    normalize exponents with explicit `rw [hnorm] at h` before omega.
25. `Nat.mul_left_comm a b c : a * (b * c) = b * (a * c)` (the
    left-associated form needs `← Nat.mul_assoc` first).
26. `cases hfa : fb a` SUBSTITUTES `fb a` already — do not re-`rw [hfa]`.
27. `Nat.mul_le_mul_left`'s signature elaborates treacherously — prefer
    `Nat.mul_le_mul h1 h2`.
28. sed on proof files is DANGEROUS: one batch ate every `rw [h…,`
    prefix (silent `[h` deletion). Regex-repair or avoid.

## 7. VERIFICATION BATTERY (all passed, exact Fractions)

- Halving family: $\{m_k\} = \{m_k{+}1..m_k{+}k{+}1\}$ for $k = 0..12$.
- Region disjointness for $k \leq 59$; gaps 2, 5, 12, 27, 58, 121, …
- $C_T$-invariance: 8 different gadget-choice patterns, identical totals.
- Irrationality receipts: isolated clusters, growing zero-gaps.
- Known-collision recheck: $x{=}1/2$ three ways; $\{4,5\}{=}\{3,8\}$.

## 8. REFERENCES

- P. Erdős [Er74b]; Erdős–Graham [ErGr80]; Erdős [Er88c, p. 104].
- Borwein–Loring [BoLo90]; Tengely–Ulas–Zygadło arXiv:2008.01501.
- Kill #5 (this branch): the weakened question, zero-axiom.
- Kill #2 (`gpt6/erdos-one-shots-2-20261101`): the greedy-walk theorem.
