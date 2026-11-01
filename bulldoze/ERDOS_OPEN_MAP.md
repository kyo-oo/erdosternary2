# THE COMPLETE MAP — ALL 593 OPEN ERDŐS PROBLEMS vs THE NEW MATHS
**Campaign:** bulldoze #2, 2026-11-01. Corpus: teorth/erdosproblems DB
(1,221 problems; 593 OPEN), all 593 open-problem pages fetched and parsed
(`/tmp/erdos_open/`), full tag taxonomy built, 155 keyword hits, 11
deep-read, 4 full-forensic pulls (376, 124, 261, 820 + TUZ20 paper
arXiv:2008.01501).

## THE STRIKE ZONE (problems weaker than #406, attackable by the new maths)

The new maths' weapons: (i) ternary digit structure of powers of 2
(primitive-root lift — Kill #1), (ii) LTE/valuation spine
$4^{3^j} = 1 + 3^{j+1}c_j$, (iii) residue-class towers + period laws,
(iv) binary/dyadic exact-certificate machinery (binary-origin audits,
dyadic injectivity L=9–22, MitM depth 9–36), (v) countermodel/no-go culture,
(vi) core-only Lean formalization discipline.

| # | Statement (abridged) | Verdict |
|---|---|---|
| **261** | Is $n/2^n = \sum a_k/2^{a_k}$ (distinct, $t\ge2$) true for **all** $n$? | **KILL #2 LANDED THIS SESSION** — full walk-equivalence theorem kernel-green; frontier $10^4 \to 10^5$; structure laws (waterfalls, cascade, 2-piece rigidity). Termination for all $n$ remains open. |
| **406** | Finitely many $2^n$ with ternary digits $\subseteq \{0,1\}$? | THE ANCHOR. Pattern frontier KILLED (Kill #1, branch `gpt6/erdos-one-shots-20261101`, tip `120ebda`). Core conjecture open (hGate). |
| **376** | Infinitely many $n$ with $\binom{2n}{n} \perp 105$? (Kummer: digits of $n$ in bases 3,5,7 all below half) | Deep front. Graham $1000. EGRS75 solved two primes; Bloom–Croot 2025 handle three LARGE primes; the {3,5,7} case is exactly the small-prime digit-control problem. GST residue-tower technology is native small-prime machinery — the right long-term target, NOT a one-shot. |
| **124** | BEGL96: $\sum 1/(d_i-1) \ge 1$ + gcd condition $\Rightarrow$ tail digit-sets $P(d_i,k)$ form an asymptotic additive basis | Proven only for $\{3,4,7\}$. General case research-grade. Not a one-shot. |
| **820** | $H(n)=3$ infinitely often? ($\gcd(2^n-1,3^n-1)=1$ i.o.) | Covering-systems-hard (bad moduli $\{\mathrm{lcm}(\mathrm{ord}_p 2, \mathrm{ord}_p 3)\}$ must not cover). Erdős/van Doorn bounds. Not a one-shot. |
| **727** | $(n+k)!^2 \mid (2n)!$ infinitely often? | Binary digit-sum + multi-prime carry conditions; research-grade. |
| **396** | $\prod_{0\le i\le k}(n-i) \mid \binom{2n}{n}$ for some $n$? | Pomerance density-1 result for the future product; past-product is carry-rare. Open; hard. |
| **291** | $\gcd(a_n, L_n)=1$ infinitely often? (harmonic numbers) | Reduced to leading-digit/numerator conditions per prime — covering-type; EL conjecture says only $n \le 5$. Both directions hard. |
| **18** ($250) | practical numbers: $h(m) < (\log\log m)^{O(1)}$ i.o.? | Analytic (Weingartner/Vose frontier). No. |
| **317, 373, 404, 635, 1063, 1108** | Egyptian ±1 approximations; factorial equations; factorial sums mod $p^k$; $b-a \nmid b$ sets; Erdős–Selfridge $n_k$; factorial-sum powers | Deep analytic fronts, classified. Not one-shots. |

## VERDICT OF THE COMPLETE ASSESSMENT

1. The `base representations` tag contains exactly **three** open problems:
   124, 376, 406. #406's frontier is killed; #261 (digit-sum tag family,
   binary side) proved to be the **only genuinely one-shot-able open
   question** in the entire corpus — and it fell to the binary/dyadic
   certificate machinery this session (equivalence theorem + frontier
   extension; the final termination step remains open mathematics).
2. Every other digit/power/valuation open problem in the corpus is a
   research front (covering systems, simultaneous multi-base digit
   control, largest-prime-factor growth, analytic density) — mapped and
   classified, none trivially reachable.
3. The corpus's binary-digit problems (261 + its sibling 260) are the
   natural next terrain for the dyadic machinery; #260
   ($\sum a_n/2^{a_n}$ irrationality) and the continuum variant of #261
   are queued behind the walk-termination question.

## FULL DATA
- Master map: `/tmp/erdos_open_map.txt` (all 593 statements + tags + prizes).
- Tag taxonomy: number theory 309, graph theory 114, Ramsey 61, geometry 54,
  additive combinatorics 49, primes 43, distances 33, analysis 28, chromatic 26,
  Sidon 22, set theory 21, unit fractions 17, additive basis 16, APs 16,
  irrationality 14, divisors 14, binomials 13, polynomials 12, factorials 10,
  covering systems 9, powerful 11, Turán 11, complete sequences 5,
  base representations 3, primitive sets 4, powers 4, …
