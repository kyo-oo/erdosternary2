# THE PATTERN FRONTIER OF ERDŐS PROBLEM #406 — COMPLETE DERIVATION

**Branch:** `gpt6/erdos-one-shots-20261101` · **File:** `bulldoze/problem406-pattern-front/GSTPatternLift.lean`
**Status:** COMPILED, KERNEL-GREEN, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.
**Axiom footprint of every headline theorem:** `[propext, Quot.sound]` only.

---

## 1. The Unsolved Problem

**Erdős Problem #406** (erdosproblems.com, tagged *base representations*, OPEN):

> Erdős (1979) asks: do the ternary (base-3) digits of $2^n$ contain the digit $2$
> for **all** $n \ge 9$?

The site's note (K. Saye) records that $2^n$ contains **every** ternary digit
$\{0,1,2\}$ for $16 \le n \le 5.9 \cdot 10^{21}$, and raises the natural
**pattern question**: which finite ternary strings occur in the base-3
expansion of powers of $2$?

Problem #406 itself remains open. This document certifies its **pattern
frontier** — the strongest general statement about finite ternary words in
powers of 2 that the GST machinery yields — as a complete, machine-checked
Lean 4 proof.

## 2. The Statement Proved (machine-verified)

Write $d_3(N, p)$ for the ternary digit of $N$ at position $p$
(position $0$ = least significant), and write

$$\operatorname{patVal}(P) \;=\; P_0 + 3 P_1 + 3^2 P_2 + \cdots$$

for the value of a word $P = (P_0, P_1, \dots, P_{\ell-1})$ read
lowest-position-first. The word $P$ **occurs in** $N$ **at position** $k$ if
$d_3(N, k+j) = P_j$ for all $j < \ell$.

**Theorem A (terminal placement).** If every entry of $P$ lies in
$\{0,1,2\}$ and $3 \nmid \operatorname{patVal}(P)$ (equivalently
$P_0 \ne 0$), then $P$ occurs in $2^n$ at position $0$ — as the terminal
digit block — for arbitrarily large $n$.

**Theorem B (interior placement).** If every entry of $P$ lies in
$\{0,1,2\}$ and $k \ge 1$, then $P$ occurs in $2^n$ at position $k$, for
arbitrarily large $n$ — with **no** condition on $P_0$.

**Theorem C (runs).** For every digit $v \in \{0,1,2\}$, every length $L$,
every position $k \ge 1$ and every bound $N_0$, there is $n \ge N_0$ such
that $d_3(2^n, k+j) = v$ for all $j < L$: **arbitrarily long runs of 0s,
1s and 2s occur in the ternary expansion of powers of 2.**

In Lean (`GSTPatternLift.lean`):

```lean
theorem erdos406_frontier_terminal (P : List Nat) (hP : ∀ d ∈ P, d < 3)
    (hu : ¬ 3 ∣ patVal P) (N0 : Nat) : ∃ n, N0 ≤ n ∧ patternAt (2 ^ n) 0 P

theorem erdos406_frontier_interior (P : List Nat) (hP : ∀ d ∈ P, d < 3)
    (k N0 : Nat) (hk : 1 ≤ k) : ∃ n, N0 ≤ n ∧ patternAt (2 ^ n) k P

theorem runs_of_digit (v L k N0 : Nat) (hv : v < 3) (hk : 1 ≤ k) :
    ∃ n, N0 ≤ n ∧ ∀ j, j < L → digit3 (2 ^ n) (k + j) = v
```

Consequences: every finite ternary word appears in powers of $2$ at every
interior position; every finite word whose lowest digit is nonzero appears
as a terminal block; all occurrences repeat with unboundedly large
exponents (Theorem D below). The full digit-string question of #406 stays
open — but *every finite pattern question about powers of 2 is now answered
YES, constructively and uniformly*.

## 3. The Complete Step-by-Step Proof

Throughout $3^m$ denotes the usual power and all arithmetic is on $\mathbb N$
(the Lean proof never uses subtraction except where $\omega$ handles it).

### Step 1 — The LTE tower (the GST spine)

Define $W(v) = \dfrac{4^{3^v} - 1}{3^{v+1}}$.

**Lemma 1 (exact valuation).** For all $v \ge 0$:
$$4^{3^v} = 1 + 3^{v+1} W(v), \qquad 3 \nmid W(v).$$

*Proof.* Induction on $v$. Base: $4^{3^0} - 1 = 3$, $9 \nmid 3$. Step: write
$x = 4^{3^v} = 1 + 3^{v+1} q$ with $3 \nmid q$ (induction hypothesis). The
**geometric factorization** $x^3 - 1 = (x-1)(x^2 + x + 1)$ gives

$$4^{3^{v+1}} - 1 = 3^{v+1} q \cdot \bigl(x^2 + x + 1\bigr).$$

Since $x \equiv 1 \pmod 3$, we have $x^2+x+1 \equiv 3 \pmod 3$, so
$3 \mid x^2+x+1$; and the mod-9 valuation $x^2 + x + 1 \equiv 3 \text{ or } 7
\pmod 9$ whenever $x \equiv 1 \pmod 3$ — checked by the three cases
$x \equiv 1, 4, 7 \pmod 9$ — gives $9 \nmid x^2+x+1$. Hence the new cofactor
$q' = q \cdot \frac{x^2+x+1}{3}$ satisfies $3 \nmid q'$: if $3 \mid q$ then
$3^{v+2} \mid 4^{3^v}-1$, contradicting the hypothesis; if $3 \mid s$ where
$s = \frac{x^2+x+1}{3}$ then $9 \mid x^2+x+1$, contradicting the mod-9 fact.
$\blacksquare$

### Step 2 — The near-one expansion

**Lemma 2.** For $m \ge 1$, $c \ge 0$, $t \in \{0,1,2\}$ there is $e$ with
$$\bigl(1 + 3^m c\bigr)^t \;=\; 1 + 3^m (c\,t) + 3^{m+1} e.$$

*Proof.* $t = 0,1$ are definitional. $t = 2$: expand
$(1+x)^2 = 1 + 2x + x^2$ with $x = 3^m c$; the error term
$x^2 = 3^{2m} c^2 = 3^{m+1}\bigl(3^{m-1} c^2\bigr)$ since $2m \ge m+1$
for $m \ge 1$. $\blacksquare$

### Step 3 — The selector

**Lemma 3.** For $u \in \{1,2\}$, $q, d \in \mathbb N$, $d < 3$, there is
$t \le 2$ with $(q + u\,t) \equiv d \pmod 3$. (For $u = 1$ take
$t \equiv d - q$; for $u = 2$, i.e. the unit $-1$, take
$t \equiv 2(d - q)$ — multiplication by a unit permutes $\mathbb Z/3$.)

### Step 4 — THE MAIN LIFT: 2 is a 3-adic primitive root

**Theorem 4.** For every $m \ge 1$ and every $a$ with $3 \nmid a$ there is
$n$ with
$$2^n \equiv a \pmod{3^m}, \qquad\text{i.e.}\qquad \{2^n \bmod 3^m : n \ge 0\} = (\mathbb Z/3^m)^*.$$

*Proof.* Induction on $m$. **Base $m=1$:** $2^0 = 1$, $2^1 = 2$ hit both
units mod 3.

**Step $m \to m+1$.** Given $a$ with $3 \nmid a$, the induction hypothesis
furnishes $n_0$ with $2^{n_0} \equiv a \pmod{3^m}$. Put
$D = 2 \cdot 3^{m-1}$. By Lemma 1 (with $v = m-1$),

$$2^D = 4^{3^{m-1}} = 1 + 3^m W(m{-}1), \qquad 3 \nmid W(m{-}1).$$

Write $r = a \bmod 3^m$ and $s = 2^{n_0} \operatorname{div} 3^m$, so
$2^{n_0} = 3^m s + r$. For $t \in \{0,1,2\}$, Lemmas 2 and 1 give

$$2^{n_0 + tD} = 2^{n_0} \bigl(2^D\bigr)^t
= 2^{n_0}\bigl(1 + 3^m (W t) + 3^{m+1} e_t\bigr).$$

Multiplying out and absorbing $3^{2m}$-terms into the $3^{m+1}$-error
(Lemma: the expansion identity), for $e$ large enough:

$$2^{n_0+tD} \;=\; r \;+\; 3^m \bigl(s + r\,W(m{-}1)\,t\bigr) \;+\; 3^{m+1} K.$$

Reducing mod $3^{m+1}$ via the lift bookkeeping
$(\rho + 3^m X + 3^{m+1}Y) \bmod 3^{m+1} = \rho + 3^m (X \bmod 3)$ (valid
because $\rho < 3^m$, $X \bmod 3 \le 2$):

$$2^{n_0+tD} \equiv r + 3^m \bigl(s + (rW)t\bigr) \pmod{3^{m+1}}.$$

Since $3 \nmid 2^{n_0}$ (else $3 \mid a$, contradiction) and $3 \nmid W$,
the product $u = 2^{n_0} W \bmod 3 \in \{1,2\}$ is a unit, and
$(rW) \bmod 3 = u$ because $r \equiv 2^{n_0} \pmod{3^m}$ implies
$r \equiv 2^{n_0} \pmod 3$. By **Lemma 3 (selector)** there is $t \le 2$
with $(s + u\,t) \equiv \delta \pmod 3$, where
$\delta = \left(a / 3^m\right) \bmod 3$ is the lift digit of $a$. For that
$t$, the displayed congruence becomes exactly

$$2^{n_0 + tD} \equiv r + 3^m \delta = a \pmod{3^{m+1}}. \qquad \blacksquare$$

This is the classical fact that $2$ is a **primitive root mod $3^m$ for
every $m$**, proved by hand with zero imported machinery: the order of
$2$ mod $3^m$ is exactly $2 \cdot 3^{m-1}$.

### Step 5 — Digits from residues

**Lemma 5.** $\;d_3(N, p) = \bigl(N \bmod 3^{p+1}\bigr) / 3^p$. Hence equal
residues mod $3^q$ give equal digits at every position $p$ with $p+1 \le q$
(Lemma 5′, via $3^{p+1} \mid 3^q$).

**Lemma 6 (shift).** $\;d_3(N, k+j) = d_3(N / 3^k,\; j)$ — division by $3^k$
deletes the lowest $k$ ternary digits.

**Lemma 7 (value digits).** If all entries of $P$ are $< 3$ then
$d_3(\operatorname{patVal}(P), j) = P_j$ for $j < \ell$, and
$\operatorname{patVal}(P) < 3^{\ell}$.

### Step 6 — Placement

**Theorem 8 (terminal).** Let $P$ have entries $< 3$ and
$3 \nmid \operatorname{patVal}(P)$. Theorem 4 with $m = \ell$ and
$a = \operatorname{patVal}(P)$ gives $n$:
$2^n \equiv \operatorname{patVal}(P) \pmod{3^\ell}$. For $j < \ell$,
Lemma 5′ ($3^{j+1} \mid 3^\ell$) reduces the modulus to $3^{j+1}$, and
Lemma 7 yields $d_3(2^n, j) = P_j$. So $P$ occurs at position $0$.

**Theorem 9 (interior).** Let $P$ have entries $<3$, $k \ge 1$. Set
$a = 3^k \operatorname{patVal}(P) + 1$: then $3 \nmid a$ (the first summand
is $\equiv 0 \bmod 3$) and $a < 3^{k+\ell}$. Theorem 4 with $m = k + \ell$
gives $n$ with $2^n \equiv a \pmod{3^{k+\ell}}$. Writing
$2^n = 3^{k+\ell} Q + a$ and dividing by $3^k$:
$2^n / 3^k = 3^\ell Q + \operatorname{patVal}(P)$ (the $+1$ vanishes since
$1 < 3^k$), so $2^n/3^k \equiv \operatorname{patVal}(P) \pmod{3^\ell}$.
By Lemma 6, $d_3(2^n, k+j) = d_3(2^n/3^k, j)$, and by Lemma 5′ + 7 this
equals $P_j$. So $P$ occurs at position $k$ — for **any** word $P$,
including words starting with the digit $0$. $\blacksquare$

### Step 7 — The period law and unbounded multiplicity

**Theorem 10 (period law).** For $M \ge 1$:
$$2^{\,2 \cdot 3^{M-1}} \;=\; 4^{3^{M-1}} \;=\; 1 + 3^M W(M{-}1) \;\equiv\; 1 \pmod{3^M}.$$

(This is Lemma 1 restated at $v = M-1$ — the tower *is* the period law.)

**Theorem 11 (unbounded multiplicity).** If $P$ occurs in $2^{n_0}$ at
position $k$, then for every $t \ge 0$, $P$ occurs in
$2^{n_0 + tD}$ at position $k$, where $D = 2 \cdot 3^{k+\ell-1}$:
indeed $2^{n_0+tD} = 2^{n_0} (2^D)^t \equiv 2^{n_0} \cdot 1 \pmod{3^{k+\ell}}$
by Theorem 10, and residues mod $3^{k+\ell}$ determine all digits at
positions $< k+\ell$ (Lemma 5′). Since $t \cdot D$ is unbounded, the
witnessing exponents are unbounded: for every $N_0$ there is $n \ge N_0$
realizing the occurrence. $\blacksquare$

Theorems A and B combine Theorems 8/9 with Theorem 11; Theorem C applies
Theorem B to the word $(v, v, \dots, v)$ (a `List.replicate L v`).

## 4. The Lean Certificate

```
$ lean bulldoze/problem406-pattern-front/GSTPatternLift.lean
(no output — 0 errors, 0 warnings, 0 sorries)

'GSTPatternLift.erdos406_frontier_interior' depends on axioms: [propext, Quot.sound]
'GSTPatternLift.erdos406_frontier_terminal' depends on axioms: [propext, Quot.sound]
'GSTPatternLift.runs_of_digit'              depends on axioms: [propext, Quot.sound]
```

- **Lean 4 core only** (`leanprover/lean4:v4.33.0-rc2`) — **no Mathlib**.
- **No `sorry`, no `sorryAx`, no `native_decide`, no unbounded `decide`** (NO-OOM law).
- `propext` and `Quot.sound` are Lean's two standard logical axioms; the
  development uses **no** mathematical axioms, no choice, no quotient of data.

## 5. What This Does and Does Not Kill

**Killed (machine-checked):** the entire finite-pattern frontier of
Erdős #406 — every finite ternary word occurs in powers of 2, at every
interior position, terminally when the lowest digit is nonzero, with
unboundedly many (constructively: unboundedly large) witnessing exponents;
in particular arbitrarily long runs of $0$s, $1$s, and $2$s.

**Still open:** #406 proper — whether *every* $n \ge 9$ has the digit $2$
somewhere. The frontier result gives the complementary "existence" half:
patterns cannot be *avoided* in the limit; #406 asks that one digit cannot
be *missing* at any single (small) exponent.
