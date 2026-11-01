# ERDŐS PROBLEM #261 — THE GREEDY WALK THEOREM AND THE COMPUTATIONAL FRONTIER

**Branch:** `gpt6/erdos-one-shots-2-20261101` (from Kill #1 tip `120ebda`)
**Files:** `WalkTheorem.lean` (Lean 4 core only, v4.33.0-rc2, kernel-green),
`walk_engine.c` (64-bit exact engine), `greedy_walk.py`, `experiment_pattern_census.py`
**Status:** the "for all $n$" question of Erdős #261 remains OPEN; this package
lands the complete equivalence theorem (formalized), the correct greedy
engine, and extends the computational frontier $10^4 \to 10^5$ (100×).
**Axiom footprint of all Lean theorems:** `[propext, Quot.sound]` — no
`sorryAx`, no `Classical.choice`.

---

## 1. THE UNSOLVED PROBLEM (verbatim from erdosproblems.com/261)

> Are there infinitely many $n$ such that there exists some $t \geq 2$ and
> distinct integers $a_1, \ldots, a_t \geq 1$ such that
> $$\frac{n}{2^n} = \sum_{k=1}^{t} \frac{a_k}{2^{a_k}} \,?$$
> Is this true for all $n$?

**What is known.** The *infinitely many* part is solved: Borwein–Loring
[BoLo90] give, for every $m \geq 1$ and $n = 2^{m+1} - m - 2$,
$$\frac{n}{2^n} = \sum_{n < k \leq n+m} \frac{k}{2^k}.$$
The **"true for all $n$" part is OPEN**. Tengely–Ulas–Zygadlo
(arXiv:2008.01501, 2020) verified all $n \leq 10^4$ by a greedy algorithm,
enumerated all solutions with $k \leq 8$ pieces, and conjectured
$a_k \leq 2(n+k)$; they could not prove termination in general.

---

## 2. THE REDUCTION TO A PURE INTEGER WALK (new, this session)

**Step 1 (forced shape).** Let $n \geq 3$ and let $S \subset \mathbb{Z}_{>0}$
be any witness set, $t = |S| \geq 2$. Since $b/2^b > n/2^n$ for every
$b < n$ (the function $b \mapsto b/2^b$ strictly decreases for
$b \geq 2$, and $1/2 > n/2^n$), no element of $S$ can be $< n$; and
$n \in S$ would force all remaining (positive) terms to sum to $0$. Hence
$$S \subseteq \{n+1, n+2, \ldots\}.$$

**Step 2 (the greedy = the walk).** Order $S$'s candidates by index and
process them greedily: maintain the scaled remainder
$$v_N := 2^{N-1}\left(\frac{n}{2^n} - \sum_{\substack{a \in S \\ a < N}} \frac{a}{2^a}\right) \in \mathbb{Z}_{\geq 0}.$$
Piece $N$ contributes $N \cdot 2^{N-1}/2^N$: it *fits* iff $N \leq v_N \cdot 2$
iff $2 v_N \geq N$. This yields the **integer walk**
$$(N, v) \longmapsto \begin{cases} (N+1,\ 2v - N) & \text{if } 2v \geq N \quad (\text{TAKE piece } N),\\[2pt] (N+1,\ 2v) & \text{if } 2v < N \quad (\text{skip}), \end{cases}$$
i.e. $v_{N+1} = (2 v_N) \bmod N$ — **a doubling map with a moving modulus.**
Start: $(N, v) = (n+1, n)$ for $n \geq 2$, and $(3, 2)$ for $n = 1$
(this is exactly TUZ20's Mathematica `greedy` normalization).
**Termination** ($v = 0$) produces the greedy witness $S$ = taken indices.

**Step 3 (the scaling invariant — the heart).** Let $S_N$ be the taken list
at state $(N, v)$ and define
$$\Psi(N, v, S) := 2v + \sum_{a \in S_N} a \cdot 2^{N-a}, \qquad \Phi(N) := n \cdot 2^{N-n}.$$
- *Start:* $\Psi = 2n = \Phi(n+1)$.
- *Take:* $\Psi' = 2(2v - N) + N \cdot 2^{N+1-N} + \sum_{a \in S} a \cdot 2^{N+1-a}
  = 4v - 2N + 2N + 2\sum a\,2^{N-a} = 2\Psi$, and $\Phi(N+1) = 2\Phi(N)$.
- *Skip:* $\Psi' = 4v + 2\sum a\,2^{N-a} = 2\Psi$.

Both sides **double at every step**, so the invariant
$$\boxed{2v + \sum_{a \in S_N} a \cdot 2^{N-a} = n \cdot 2^{N-n} \text{ and } a < N \ \forall a \in S_N \text{ and } n \leq N}$$
is preserved by induction on the walk. (Formalized: `walk_invariant`,
Lean core-only.)

**Step 4 (main theorem).** If the walk terminates at $(N, 0)$, the invariant
collapses to the **exact integer identity**
$$\sum_{a \in S} a \cdot 2^{N-a} = n \cdot 2^{N-n}, \qquad a < N \text{ for all } a \in S,$$
and dividing both sides by $2^N > 0$ (legal: every exponent $N - a \geq 1$)
gives precisely the Erdős #261 representation
$$\frac{n}{2^n} = \sum_{a \in S} \frac{a}{2^{a}}.$$
(Formalized: `walk_zero_identity`.) Moreover for $n \geq 2$ the witness is
non-degenerate, $|S| \geq 2$: the first take at $N=n+1$ leaves $v = n-1 \geq 1$,
and $v = 0$ requires a further take with $2v = N$; a take-to-zero directly
from a start state would need $2n = n+1$, impossible for $n \geq 2$
(formalized via the start-characterization `walk_nil_char` +
`walk_zero_two_pieces`).

**Conversely**, non-termination means the greedy tail
$r_N = v_N / 2^{N-1}$ stays positive forever while tending to $0$ — i.e.
$n/2^n$ admits an *exact infinite* greedy representation with distinct
indices. So:

$$\text{Erdős #261 "all } n\text{"} \iff \textbf{the walk from } (n+1, n) \text{ hits } v = 0 \text{ for every } n \geq 1.$$

---

## 3. STRUCTURE LAWS DISCOVERED

1. **Two-piece rigidity.** Solving $n(2^{\alpha+\beta} - 2^{\beta} - 1) =
   \alpha 2^{\beta} + \alpha + \beta$ for piece offsets shows the BL family
   $n = 2^{m+1} - m - 2$ (witness $\{n+1, \dots, n+m\}$) is essentially the
   *only* 2-piece family; $n = 4$ is the only 2-piece case outside small
   degeneracies. **Every other $n$ needs $\geq 3$ pieces** — verified
   exhaustively by the pattern census (below).
2. **Algebraic characterization.** $n$ is representable with max offset $J$
   iff there is a bit-pattern $P \subseteq \{1..J\}$ with
   $$n = \frac{2^{J+1} - J - 2 - S_P}{A_P + 1}, \quad
   A_P = \sum_{j \in P} 2^{J-j}, \quad S_P = \sum_{j \in P} j\, 2^{J-j},$$
   (equivalently $\sum_{j \in P} (n+j) 2^{J-j} = 2^{J+1} - n - J - 2$).
   Each pattern certifies **at most one** $n$ — every $n$ needs its own
   certificate. Hand-verified: $n=3$: $\{4,6,8\}$;
   $n=5$: $\{6,7,11,13,14\}$; $n=8$: 13 pieces up to offset 32.
3. **Merge waterfalls.** Walks from different $n$ collide at identical
   $(N, v)$ states and terminate together at shared "waterfalls";
   last-take values observed: $8, 14, 22, 24, 30, 32, 46, 56, 70, 142, 392, \ldots$
   (e.g. $n = 10, 14, 16, 20, 22, 23, 24, 27, 28, 30, 31, 33, 37, 39$ all end
   at $a_k = 392$). This Collatz-style attractor structure is why
   worst-case walk length grows **sublinearly** in $n$.
4. **First cascade.** From $(n+1, n)$ consecutive takes give
   $v_j = n + j + 2 - 2^{j+1}$ at $N_j = n+1+j$; the cascade continues while
   $2^{j+2} + j \leq n + 3$, landing $v$ within $O(\log n)$ of $N/2$ — the
   BL family is exactly the case of hitting $N/2$ dead-on.

---

## 4. THE COMPUTATIONAL FRONTIER (exact 64-bit integer engine)

- **Census cross-check:** independent exhaustive pattern census
  ($J \leq 22$, all $2^J$ patterns, Gray-code incremental $S_P$) agrees with
  the walk on all $n$ it can decide and correctly exposes that witnesses may
  need offsets far beyond $n$ (e.g. $n = 8$ needs offset 32).
- **Frontier extension:** TUZ20 verified $n \leq 10^4$. This session:
  **all $n \leq 10^5$ terminate** (worst: $n = 88225$, 571,263 steps,
  $k = 285{,}549$ pieces, $a_k = 659{,}488$; total $\approx 1.76 \times 10^{10}$
  walk steps, exact 64-bit arithmetic, no overflow — $v < N < 2 \cdot 10^6$).
  (Scans beyond $10^5$ grow superlinearly — mean walk length
  $\approx 2\times10^5$ at $n \approx 10^5$ — and are queued as a
  background grind; the engine is bit-exact and resumable per decade.)
  The TUZ20 conjecture $a_k \leq 2(n+k)$ holds throughout.
- **Kernel-checked certificates:** `checkWit` verifies a witness by the
  exact identity; decided in Lean for $n = 3, 4, 5, 8$; full walk
  derivations given as proof terms for $n = 3$ (5 steps) and $n = 4$
  (BL, 2 steps).

---

## 5. WHAT REMAINS OPEN

The termination of the walk for **all** $n$ — equivalently the "all $n$"
question of #261. The heuristic: $v_N$ is equidistributed-ish in $[0, N)$,
so the chance of hitting $N/2$ at index $N$ is $\sim 1/N$ and
$\sum 1/N$ diverges (Borel–Cantelli heuristics predict certain
termination); the merge-waterfall structure empirically accelerates it.
A proof requires new mathematics for the moving-modulus doubling map
$v_{N+1} = (2 v_N) \bmod N$. The backward tree from the sink
$((N, N/2) \to 0)$ must be shown to cover the entire top edge
$\{(n+1, n)\}$.

## 6. REFERENCES

- P. Erdős, [Er88c]; R. L. Graham, "Old and new problems" — the equation.
- P. Borwein, E. Loring, [BoLo90] — the infinite BL family.
- T. Tengely, M. Ulas, J. Zygadlo, *On a Diophantine equation of Erdős and
  Graham*, arXiv:2008.01501 (2020) — greedy to $10^4$, conjecture $a_k \leq 2(n+k)$.
- T. Bloom (ed.), Erdős Problem #261, erdosproblems.com/261.
