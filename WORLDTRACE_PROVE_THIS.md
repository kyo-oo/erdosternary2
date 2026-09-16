# ⬢ THE WORLDTRACE ARITHMETIC BRIEF — PROVE THIS OBJECT

**Repository:** `kyo-oo/erdosternary2`, branch `sol/kyo-gate-universe-wire`, HEAD `fd89766` (CI double-green, 0 sorries).
**Axiom base of every theorem quoted below:** `[propext, Classical.choice, Quot.sound]` — nothing else. No `sorry` anywhere in the chain.

**TO THE PROVER.** This document contains: (0) the exact object, (I) the worldtrace-arithmetic transformation, (II) the complete machinery — the most powerful theorems of the campaign, **copied verbatim as actual Lean code**, (III) the full construction protocol of the **GST Graph V2 Ontological Universe Graph**, (IV) the proof demand.

**DELIVERABLE: A FULL MATHEMATICAL DERIVATION IN LATEX — NOT LEAN CODE.**

---

# PART 0 — THE OBJECT

The Erdős ternary conjecture, original form: **every power $2^n$ with $n \geq 9$ contains the digit $2$ somewhere in its base-3 expansion.**

The repo's ground-truth predicate (monolith `ErdosTernary2.lean:148`):

```lean
def noTernaryTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryTwo (n / 3)
termination_by n
decreasing_by
  have hk : 0 < n := by omega
  exact Nat.div_lt_self hk (by decide : 1 < 3)
```

The odd-exponent half is **already proven green**. The remaining content is the even half. Since $4^K = 2^{2K}$ with $2K \ge 16 \ge 9$, the even half is one object (`GSTTheAct.lean:51`):

```lean
/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two.
This is the exact content whose absence is the whole conditionality of
`hTailF` — no more, no less. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false
```

The kernel-certified **terminal identity** (monolith `ErdosTernary2.lean:18425`, both directions machine-proven):

```lean
theorem erdos_even_conjecture_iff_tailF :
    (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
      ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
```

The target definition the whole campaign converges to (`GSTGraphV2OmegaWaveLaw.lean:3015`):

```lean
/-- **THE Ω-SHADOW WAVE TAIL (SECOND OBSERVER FORM)** — the residual
input after both observers: the entire tower AND the entire
sheet-zero row cycle, each collapsed to one all-depths clause. -/
def four_power_omega_shadow_wave_tailF : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTailF K → ∃ p : Nat, digit3 (4^K) p = 2
```

with the shadow package (`GSTGraphV2OmegaWaveLaw.lean:2998`):

```lean
def omegaShadowTailF (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1))
```

**PROVING `the_act` — or ANY ONE of the following four green-equivalent residual statements — CLOSES THE OBJECT.** Each has a named, machine-certified, zero-hypothesis consumer already in the repo:

| # | Residual statement to prove | Green consumer (one line) |
|---|---|---|
| 1 | `∀ K : Nat, 8 ≤ K → ∃ j : Nat, (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2` | `GSTTheActConstruction.hTailF_of_feedback` |
| 2 | `¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K` | `GSTClimbInfiniteFamily.hTailF_of_no_cantorian` |
| 3 | `∀ K : Nat, 8 ≤ K → ¬ GSTDiagonalRead.WindowCleanDust K` | `GSTDiagonalRead.hTailF_of_dust_empty` |
| 4 | `GSTTheAct.the_act` itself | `GSTTheAct.the_act_iff_hTailF.mp` |
| 5 | both `tailF_row_primitive` **and** `tailF_tower_primitive` (Part II §D4) | `GSTTailFFourthDimension.tailF_of_row_and_tower` |

All five are the same object. The identity chain is:

$$\text{the\_act} \;\Longleftrightarrow\; \text{hTailF-target} \;\Longleftrightarrow\; \text{the full Erdős ternary statement},$$

machine-certified in both directions by `the_act_iff_hTailF`, `the_act_iff_full_erdos`, and `erdos_even_conjecture_iff_tailF`.

---

# PART I — THE WORLDTRACE ARITHMETIC TRANSFORMATION

## I.1 What a worldtrace is

Every natural number $R$ **is** its ternary digit stream — its *worldtrace*:
$$R \;=\; \sum_{p \ge 0} d_p\, 3^p, \qquad d_p = \text{trit}_p(R) \in \{0,1,2\}.$$
The reading operators (verbatim, `GSTCanonicalSevenAxisBridge.lean:22`):

```lean
/-- Ternary information coordinate of one exact natural energy. -/
def digit3 (R p : Nat) : Nat := R / 3^p % 3

/-- x4 carry coordinate of one exact natural energy. -/
def carry4 (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
```

`digit3 R p` reads trit $p$ of the worldtrace of $R$; `carry4 R p` is the carry that the multiplication-by-4 automaton holds at depth $p$ when computing $4 \cdot R$ in base 3. These two coordinates are the **state** of the universe graph (Part III).

## I.2 The transformation of the object

The conjecture becomes: **for every $K \ge 8$, the worldtrace of $4^K$ contains a 2.**

The campaign's green laws transform this into five equivalent readings:

1. **The feedback read** (self-read law, Part II §F): trit $j{+}1$ of $\text{wt}(4^K)$ = trit $j{+}1$ of $\text{wt}(4^{K \bmod 3^j})$ + trit $j$ of $\text{wt}(K)$, mod 3. The object = *every $K \ge 8$ fires this sum to 2 at some level $j$*.
2. **The LTE-cut read**: write $K = 3^s \cdot \text{core}$ (3-free core). Then
$$4^{3^s \cdot \text{core}} \;=\; 1 + 3^{s+1} \cdot \underbrace{\omega\mathrm{CutWord}(s,\text{core})}_{\text{the cut word}},$$
and every trit of the power above row $s$ is a trit of the cut word (observer laws, Part II §C). The object = *the cut word of every surviving core fires its top third at some depth*.
3. **The dust read**: the arm $K \equiv 1 \pmod 3$, $K = 1 + 3m$: 
$$4^{1+3m} = 4 \cdot 64^m = 4(1+63)^m,$$
a **binomial sum** — every deep row of the dust power is an **explicit polynomial in $m$** (the blades, Part II §H):
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} \pmod{729},$$
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} + 1000188\binom{m}{3} \pmod{6561},$$
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} + 1000188\binom{m}{3} + 63011844\binom{m}{4} \pmod{19683}.$$
4. **The survivor-tree read**: the Cantorian dust (exponents whose power dodges 2 everywhere) is pinned to $2, 4, 8, 16, 32, 64, 128, \ldots$ residue classes mod $9, 27, 81, 243, 729, 2187, 6561, \ldots$ — a doubling Cantor tree; every node has **exactly one dead child** (`unique_dead_child`). The object = *the infinite intersection of this tree, above 8, is empty*.
5. **The universe-graph read**: a digit 2 at $(t,p)$ is exactly a **Happy cell** (event 8, the $2 \to 2$ transition) of the GST Graph V2 at horizontal stride $t+1$ and vertical depth $p$ (Part III).

## I.3 The constants of the transformation

The **LTE ladder** (`GSTGraphV2HandwrittenExponentialLTE.lean:24`):

```lean
/-- Exact LTE quotient in
`4^(3^r) = 1 + 3^(r+1) * lteCoeff r`. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- Exact power-of-four LTE identity at every ternary scale. -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
```

The **c-tower constant** (`GSTTowerFire.lean:50`) — the same object through the blade-wave factorization:

```lean
/-- The tower coefficients `c n = (4^(3^n) − 1) / 3^(n+1)`,
integral by the green LTE cut. -/
def c (n : Nat) : Nat := (4^(3^n) - 1) / 3^(n+1)

theorem four_pow_three_pow_eq (n : Nat) : 4^(3^n) = 1 + 3^(n+1) * c n

/-- **The cube recursion of the tower.**  Cubing the decomposition of
`4^(3^n)` and matching orders gives `c (n+1)` from `c n` with exactly
the two binomial corrections. -/
theorem c_succ_eq (n : Nat) :
    c (n+1) = c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
```

Its frozen congruences (all green):

```lean
theorem c_mod3  (n : Nat) : c n % 3 = 1
theorem c_mod9  (n : Nat) (hn : 1 ≤ n) : c n % 9 = 7
theorem c_mod81 (n : Nat) (hn : 3 ≤ n) : c n % 81 = 16
```

The **stabilization law** — the tower constant is one 3-adic object (`GSTGraphV2OmegaWaveLaw.lean:395`):

```lean
theorem omega_lteCoeff_stable (L d : Nat) :
    ∀ a : Nat, L ≤ a → (lteCoeff a) % 3^L = d % 3^L → ...
```

(called through `GSTDiagonalRead.lteCoeff_stable`):

```lean
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1)
```

Numerically the frozen 3-adic limit is
$$c_\infty \;=\; \lim_{t} \frac{4^{3^t}-1}{3^{t+1}}, \qquad \text{trits } [1,2,1,0,2,2,0,1,0,2,1,2,1,0,\ldots]$$
and the receipt-verified law (modular checks, 27/27 passes): **below depth $t$, the trits of $\omega\mathrm{CutWord}(t,m)$ are exactly the trits of $c_\infty \cdot m$.**

---

# PART II — THE MACHINERY (verbatim Lean code)

Everything below is **actual code, green in CI**, with file:line locations. This is the arsenal.

## §A. The root identity chain — `GSTTheAct.lean` (147 lines, complete spine)

```lean
/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE IDENTITY.**  Through the repo's own green unconditional iff,
the act and `hTailF`'s target are one object: whatever proves the act
proves `hTailF`, and nothing weaker than the act does. -/
theorem the_act_iff_hTailF :
    the_act ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  erdos_even_conjecture_iff_tailF

/-- The full ternary statement restricted to even exponents yields the act. -/
theorem the_act_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) : the_act

/-- **THE ANSWER.  Erdős closed ⇒ hTailF closed, one green line.** -/
theorem hTailF_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  the_act_iff_hTailF.mp (the_act_of_full_erdos hFull)

/-- **THE ACT AND THE FULL STATEMENT ARE ONE OBJECT** — the odd-exponent
half is already green, so the even half is the whole remaining content. -/
theorem the_act_iff_full_erdos :
    the_act ↔ (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false)

/-- **THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of `4^(3^v * a)`
is exactly `a % 3`: the power-of-four ternary digit stream reads the
reduced exponent trit directly. -/
theorem front_law (v : Nat) : ∀ a : Nat,
    digit3 (4^(3^v * a)) (v + 1) = a % 3
```

## §B. The Ω-cut tower — the omega wave law engine (`GSTGraphV2OmegaWaveLaw.lean`, 3043 lines, 140 declarations)

### B1. The Ω operator and the worldtrace orbit law

```lean
/-- **THE NEW OPERATOR ΩW** — one omega wave-climb transfusion step on a
seeded information word: the origin trit is consumed into the x4 seed while
the remaining origin is divided by three. -/
def omegaWaveStep (D X : Nat) : Nat × Nat :=
  ((D + 4 * (X % 3)) / 3, X / 3)

theorem omegaWaveStep_u_divide (D X : Nat) :
    X = originTrit X + 3 * (omegaWaveStep D X).2

theorem omegaWaveStep_u_multiply (D X : Nat) :
    D + 4 * originTrit X =
      3 * (omegaWaveStep D X).1 + ((D + 4 * originTrit X) % 3)

theorem omegaWaveStep_mass (D X : Nat) :
    3 * (omegaWaveStep D X).1 ≤ D + 4 * originTrit X ∧
      D + 4 * originTrit X < 3 * ((omegaWaveStep D X).1 + 1)

/-- **The worldtrace orbit law.**  The vertical step of the exact carry
stream of any energy `R` is literally one Ω-wave transfusion of the seeded
tail: the operator's orbit *is* the information wave that reads the ternary
digits of `R`. -/
theorem omegaWaveStep_worldtrace (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).1 = carry4 R (p+1)

theorem omegaWaveStep_tail (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).2 = R / 3^(p+1)
```

### B2. The cut words

```lean
/-- The geometric mean factor of the Ω-decomposition: the sum of the first
`core` powers of the base `4^(3^a)`. -/
def omegaGeoSum (a core : Nat) : Nat :=
  Finset.sum (Finset.range core) (fun j => (4^(3^a))^j)

/-- The cut word of the Ω-decomposition: the LTE mean times the geometric
mean. -/
def omegaCutWord (a core : Nat) : Nat :=
  lteCoeff a * omegaGeoSum a core

/-- **The Ω-cut factorization** — the omega handwritten equation of the Law.
For every sheet level `a` and every core mass, the power `4^(3^a * core)`
decomposes exactly as one plus the cut modulus times the cut word. -/
theorem omega_cut_factor (a core : Nat) :
    4^(3^a * core) =
      1 + 3^(a+1) * omegaCutWord a core
```

### B3. The ν-law and the level-one gate

```lean
/-- **THE ν-LAW (level one of the Ω-cut tower).**  The ternary digit of
`4^(3^a * core)` at the cut row `a+1` is literally the first nonzero
ternary trit of the exponent. -/
theorem omega_cut_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+1) = core % 3

theorem omega_cut_prefix_one (a core : Nat) :
    4^(3^a * core) % 3^(a+1) = 1

theorem omega_cut_carry_zero (a core : Nat) (ha : 1 ≤ a) :
    carry4 (4^(3^a * core)) (a+1) = 0

/-- **THE Ω-CUT GATE (level one).**  Every exponent whose core mass is
congruent to two modulo three owns a physical Happy row exactly at its own
LTE cut — digit two with carry zero. -/
theorem omega_cut_happy_gate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    HappyCell
      (carry4 (4^(3^a * core)) (a+1))
      (digit3 (4^(3^a * core)) (a+1))
```

### B4. The controller family, the puncture, the shadow wave

```lean
theorem omega_all_bad_to_controller (K : Nat) (hK : ...)   -- :417
    -- every all-bad horizontal block funnels into the controller column

theorem omega_puncture (a core : Nat) (ha : 2 ≤ a) (hcore : core % 3 = 2)  -- :435
    -- the core-two sheet is punctured at its own cut

theorem omega_why_theorem (K : Nat) ...                     -- :452

def omegaShadow (K : Nat) : Prop := ...                     -- :617
def four_power_omega_shadow_wave : Prop := ...              -- :625

theorem omega_digit_two_cases (K : Nat) (hK : 8 ≤ K) : ...  -- :631
theorem omega_digit_two_coverage (hShadow : four_power_omega_shadow_wave) : ...
```

### B5. The deep cuts — every level, binomial-exact

```lean
theorem omega_cut_word_full (s core : Nat) : ...            -- :800
    -- the FULL cut word identity, binomial corrections to all orders

theorem omega_cut_word_mod_pow2 (s core : Nat) (hcore : core % 3 = 1) : ...  -- :858
    -- omegaCutWord s core ≡ lteCoeff s * core (mod 3^(s+2)):
    -- the cut word IS the scaled diagonal below the squared cut

theorem digit3_window (X j : Nat) : ...                      -- :901
    -- the window-slice law: trit j of X from X mod 3^(j+1)

theorem omega_sheet_digit (s core : Nat) (hcore : core % 3 = 1) : ...  -- :931
theorem omega_sheet_gate_digit_two ...                       -- :953
theorem omega_sheet2_digit (s core : Nat) : ...              -- :1237
theorem omega_sheet2_gate_four ...                           -- :1258
theorem omega_sheet2_gate_seven ...                          -- :1307
```

Per-level level-digit laws (each one green, each a residue test on the core):
`omega_level2_digit_two :335`, `omega_level3_digit_two :746`, `omega_level4_digit_two :1047`, `omega_level5_digit_two :1618`, `omega_level6_digit_two :1697`, `omega_level7_digit_two :1971`; exponent-cycle families `omega_expcycle_row3/4/5/6_digit_two_* :1393-2087`.

### B6. The tripling-cube cascade (§7.10)

```lean
/-- The exponent-tripling descent: the cut word of the cubed power. -/
theorem omega_tripling_cut_word (s core : Nat) : ...        -- :2343
    -- W_{s+1} = W_s + 3^(s+1)·W_s² + 3^(2s+1)·W_s³

theorem omega_tripling_digit_transfer (s core : Nat) (hs : 1 ≤ s) : ...  -- :2401
theorem omega_tripling_gate (s core : Nat) ...              -- :2474
theorem omega_tripling_child_digit_two (s core : Nat) ...   -- :2482
```

### B7. The graph form and the chokehold

```lean
theorem graph_column_digit_exact (E t p : Nat) : ...        -- :2514
theorem graph_pure_power_digit_exact (K p : Nat) : ...      -- :2524
theorem omega_shadow_wave_graph ...                         -- :2537
theorem controller_parent_digit_wave ...                     -- :2557
theorem graph_column_parity_energy (n : Nat) : ...          -- :2580
theorem infinite_graph_ternary_two_chokehold ...            -- :2611
theorem infinite_graph_chokehold_envelope ...               -- :2637
```

## §C. THE OBSERVER LAWS — one law, all levels, all generations

**The single most powerful reading instrument in the repo.** It collapses the entire per-level generation ladder into one identity.

```lean
/-- **THE CUT-WORD LINEARITY LAW.**  The sheet word is the mean rotation of
the core: the cut word of `core` sheets equals the unit-core cut word
times the core, modulo the next cut modulus. -/
theorem omega_cut_word_linear (s core : Nat) :
    ∃ t : Nat, omegaCutWord s core
      = omegaCutWord s 1 * core + 3^(s+1) * t

/-- **THE OBSERVER LAW — one object, all generations, all tower levels.**
For every sheet level `s`, every core, and every tower level `k` with
`1 ≤ k ≤ s+1`: the ternary digit of the power `4^(3^s * core)` at tower
row `s+k` is the `(k-1)`-th trit of the single mean rotation
`omegaCutWord s 1 * core`.  No per-level numeral, no per-level gate
theorem: the whole tower is this one identity. -/
theorem omega_observed_digit (s core k : Nat) (hk : 1 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s + k)
      = ((omegaCutWord s 1 * core) % 3^k) / 3^(k-1)

/-- **THE UNIFORM TOWER GATE — all levels, all generations, one law.**
For every sheet level `s`, every core, and EVERY tower level `k ≥ 3`
inside the sheet's window: whenever the mean rotation's trit at position
`k-1` is two — the top third of the residue window modulo `3^k` — the
power `4^(3^s * core)` owns its ternary digit two at row `s+k`. -/
theorem omega_tower_level_digit_two (s core k : Nat) (hk : 3 ≤ k)
    (hks : k ≤ s+1)
    (hg : 2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k) :
    digit3 (4^(3^s * core)) (s + k) = 2

/-- **THE UNIFORM ROW LAW** — the row-axis twin.  For every core and every
depth `j`, if the row word — the cut word at sheet zero, `omegaCutWord 0 core`,
which is exactly `(4^core - 1)/3` — has its top trit two in the window
modulo `3^(j+1)`, then `4^core` owns its ternary digit two at position
`1 + j`.  Rows three through six and every row beyond are instances at
`j = 2, 3, 4, 5, ...`. -/
theorem omega_row_level_digit_two (core : Nat) (j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2
```

## §D. THE 4TH DIMENSION — the emergent diagonal (`GSTTailFFourthDimension.lean`, 2332 lines)

### D1. The extended observation law (no window bound)

```lean
/-- **THE EXTENDED OBSERVATION LAW.**  For every sheet level `s`, every
core, and EVERY depth `j`: whenever the cut word's own trit at depth `j`
sits in the top third of its residue window modulo `3^(j+1)`, the tower
power `4^(3^s * core)` owns its ternary digit two at position `s+1+j`.
No window bound: the reading works at every depth of the power. -/
theorem tower_observation_digit_two (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2
```

### D2. The descent blade — the 4D emergent laws

```lean
/-- **THE CUBE-LIFT STABILIZATION.**  The cut word of sheet level `s+1` is
the cut word of level `s` plus a multiple of `3^(s+1)`: every trit below
position `s+1` is frozen as the sheet level grows. -/
theorem omega_cut_word_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t

/-- **THE EMERGENT AXIS — the descent to the primitive.**  For every
sheet level `s` at or above `k-1`, the tower word at modulus `3^k` is the
primitive level-`(k-1)` word: the diagonal is the SAME object at every
sheet. -/
theorem emergent_dimension_descent (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k

theorem tower_dodge_is_diagonal_dodge (core s k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k

/-- **THE KILL — one diagonal fire, every sheet.**  One ternary digit two
on the primitive diagonal at level `k-1` kills the tower dodge at EVERY
sheet level `S ≥ k-1` at once. -/
theorem emergent_dimension_kill (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2
```

### D3. The exact cube-lift recursion — the engine

```lean
/-- The whole cascade of sheets as ONE recursion with no existential
remainder: the cut word of the next sheet is this sheet's cut word plus
exactly `3^(s+1) · (W² + 3^s·W³)` where `W` is this sheet's own cut word. -/
theorem omega_cut_word_cube_lift_exact (s core : Nat) :
    omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))

/-- **THE +1 LIFT LAW — the diagonal's advance.**  For every sheet from
one onward and every three-free core, the next sheet's cut word is this
sheet's cut word plus exactly ONE unit of the sheet's own modulus,
modulo `3^(s+2)`. -/
theorem omega_cut_word_lift_one (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    omegaCutWord (s+1) core % 3^(s+2)
      = (omegaCutWord s core + 3^(s+1)) % 3^(s+2)

/-- **THE THREE-WINDOW DICHOTOMY — fire, dodge, or escalate.**  Every
sheet `s ≥ 1` of every three-free core, read through its own window: TOP
third ⇒ the power fires at `2*s+2` outright; BOTTOM third ⇒ the dodge;
MIDDLE third ⇒ the `+1` lift makes the next diagonal trit two and the
descent blade kills EVERY sheet `S ≥ s+1` at once. -/
theorem omega_sheet_window_dichotomy (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
    ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
    ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
      ∧ ∀ S : Nat, s+1 ≤ S → digit3 (4^(3^S * core)) (S + (s+2)) = 2)

/-- **THE ESCALATION LAW.**  If every sheet dodges its own window, then at
every level `k ≥ 3` the scaled diagonal sits at or above the middle of its
window: the window dodge feeds the diagonal; the diagonal cannot hide low. -/
theorem omega_window_dodge_escalates (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k

/-- **THE DUST'S SHAPE.**  A three-free core whose sheets all dodge their
windows AND whose diagonal dodges the fire band parks its scaled diagonal
in the EXACT MIDDLE THIRD of every window: window trit zero at every
sheet, diagonal trit one at every level.  The dust is not a fog — it is a
sharply pinned configuration. -/
theorem omega_dust_shape_middle_third (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
        ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)
```

### D4. The decomposition of the input into two named 3-adic trit statements

```lean
/-- **THE ROW PRIMITIVE** — the sheet-zero family's entire carried content:
the row word of every 3-free class-one core above the kernel base owns its
top-third fire at some depth. -/
def tailF_row_primitive : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    (core % 9 = 1 ∨ core % 9 = 4) →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE TOWER PRIMITIVE** — the tower family's entire carried content:
every diagonal-dodging tower's cut word fires its top third in its deep
tail, at depth at least `s+2` — beyond the package's own dodge band. -/
def tailF_tower_primitive : Prop :=
  ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
    (core % 9 = 4 ∨ core % 9 = 7) →
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∃ i : Nat, s+2 ≤ i ∧
        2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)

/-- **THE DECOMPOSITION OF THE INPUT.**  The two named primitives compose
into the full second-observer input. -/
theorem tailF_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF

/-- **THE EVEN-EXPONENT STATEMENT FROM THE TWO PRIMITIVES.** -/
theorem even_conjecture_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE CROWN FROM THE TWO PRIMITIVES.** -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false
```

Also in this file: the nineteen diagonal-ignition bands — `omega_diagonal_two_of_mod_nine_one :206`, `..._mod27_thirteen :225`, `..._mod27_twentyfive :244`, `..._mod81_four :305`, `..._mod81_thirtyfour :324`, `..._mod81_fortynine :343`, `..._mod81_seventy :362`, `..._mod243_sixteen :382` through `..._mod243_onehundredeightyfour :529` (eight mod-243 bands), and the tower-band kills `omega_tower_kill_of_diagonal_two :186`, `omega_tower_digit_two_of_mod_nine_one :262`, `omega_tower_digit_two_of_mod81_band :549`, `omega_tower_digit_two_of_mod243_band :566`.

## §E. THE 2D EMERGENT LAWS (`GST2DMixedEmergence.lean`, 242 lines — the full microscopic physics)

```lean
/-- One literal x2/base-3 microscopic output. -/
def microOutput (a d : Nat) : Nat := (a + 2*d) % 3

def highBit (C : Nat) : Nat := C / 2
def lowBit (C : Nat) : Nat := C % 2

def midDigit (C d : Nat) : Nat := microOutput (highBit C) d

def finalMicroDigit (C d : Nat) : Nat :=
  microOutput (lowBit C) (midDigit C d)

/-- Exact x4/base-3 cell output digit. -/
def outDigit (C d : Nat) : Nat := (C + 4*d) % 3

/-- Exact x4/base-3 next carry. -/
def nextCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- Handwritten U charge chart. -/
def uCharge (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- Handwritten U jump. -/
def uJump (C d : Nat) : Int :=
  3 * uCharge (nextCarry C d) - uCharge C - 24*(d : Int)

/-- Indicator of information digit BIG2. -/
def twoI (d : Nat) : Int := if d = 2 then 1 else 0

/-- One literal microscopic signed seven-kernel edge. -/
def microSevenKernel (a d : Nat) : Int :=
  14 * (twoI (microOutput a d) - twoI d) +
    7 * (twoI d * twoI (microOutput a d))

/-- The two microscopic x2 layers whose composition is one x4 GST cell. -/
def sevenKernel (C d : Nat) : Int :=
  microSevenKernel (highBit C) d +
    microSevenKernel (lowBit C) (midDigit C d)

/-- Number of microscopic BIG2→BIG2 SURVIVE edges inside the x4 cell.  It is
`0`, `1`, or `2`; unlike a coarse x4 indicator it retains the hidden BIG1
midpoint of the NULL chord `2→1→2`. -/
def surviveI (C d : Nat) : Int :=
  twoI d * twoI (midDigit C d) +
    twoI (midDigit C d) * twoI (finalMicroDigit C d)

/-- Vertical carry potential selected by the exact twelve-cell system. -/
def carryPotential (C : Nat) : Int :=
  if C = 0 then -5 else if C = 1 then -7 else if C = 2 then 1 else 3

/-- Horizontal information potential.  It vanishes on BIG0 and BIG2 and is
`-56` exactly on BIG1. -/
def infoPotential (d : Nat) : Int :=
  112 * twoI d - 56*(d : Int)

/-- Primitive `8:7` mixture of the handwritten seven-kernel and U operator. -/
def mixedDensity (C d : Nat) : Int :=
  8 * sevenKernel C d + 7 * uJump C d
```

The 2D emergent laws:

```lean
/-- Two literal x2 layers reproduce the x4 output trit. -/
theorem finalMicroDigit_eq_outDigit
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    finalMicroDigit C d = outDigit C d

/-- The microscopic seven-kernel telescopes horizontally: only the endpoint
BIG2 charge and the two genuine microscopic SURVIVE incidences remain. -/
theorem sevenKernel_micro_telescope
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sevenKernel C d =
      14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d

/-- The mixed horizontal potential is exactly the BIG1 detector. -/
theorem infoPotential_physical_table (d : Nat) (hd : d < 3) :
    (d = 0 ∧ infoPotential d = 0) ∨
    (d = 1 ∧ infoPotential d = -56) ∨
    (d = 2 ∧ infoPotential d = 0)

/-- The U operator by itself is already a two-direction divergence. -/
theorem uJump_divergence (C d : Nat) (hC : C < 4) (hd : d < 3) :
    uJump C d =
      8 * ((d : Int) - (outDigit C d : Int)) +
      carryPotential C - 3 * carryPotential (nextCarry C d)

/-- **Mixed 2D GST emergence equation.**  The primitive mixture
`8·sevenKernel + 7·U` is forced by the requirement that the horizontal
potential identify BIG0 and BIG2.  What remains is exactly:
a horizontal BIG1-only boundary derivative; a vertical ternary carry
derivative; and positive microscopic SURVIVE incidence in the interior.
Thus the two-dimensional object is an algebraic consequence of the two raw
handwritten operators, not an imposed geometry. -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    mixedDensity C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d

/-- The two x4 Happy realizations separate naturally: NULL is the hidden
BIG1 chord `2→1→2`; GST+ is the all-SURVIVE chord `2→2→2`. -/
theorem happy_chord_dichotomy
    (C : Nat) (hC : C = 0 ∨ C = 3) :
    (C = 0 ∧ midDigit C 2 = 1 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 0) ∨
    (C = 3 ∧ midDigit C 2 = 2 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 2)

/-- One horizontal row of physical x4 cells. -/
theorem mixed_row_emergence (C Cnext d : Nat → Nat) (N : Nat)
    (hcell : ∀ t, t < N →
      C t < 4 ∧ d t < 3 ∧
      outDigit (C t) (d t) = d (t+1) ∧
      nextCarry (C t) (d t) = Cnext t) :
    Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
      infoPotential (d N) - infoPotential (d 0) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t)) -
        3 * Finset.sum (Finset.range N) (fun t => carryPotential (Cnext t))) +
      56 * Finset.sum (Finset.range N) (fun t => surviveI (C t) (d t))

/-- **Full 2D divergence theorem.**  Every finite rectangle cut from the live
Nat×Nat grid has only left/right BIG1 boundary charge, bottom/top carry flux,
and positive microscopic SURVIVE incidence. -/
theorem mixed_rectangle_emergence
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
        mixedDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * (infoPotential (d N p) - infoPotential (d 0 p))) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t 0)) -
        (3 : Int)^K * Finset.sum (Finset.range N) (fun t => carryPotential (C t K))) +
      56 * Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          surviveI (C t p) (d t p)))
```

## §F. THE CAUSALITY LAWS

### F1. Origin-prefix causality (`CanonicalCausalityScratch.lean`, complete)

```lean
/-- A ternary digit is exactly the corresponding one-trit quotient of the
prefix residue through that digit. -/
theorem gstDigitS_eq_prefix_residue_divS (R j : Nat) :
    gstDigitS R j = (R % 3^(j+1)) / 3^j

/-- Equality through ternary depth j+1 preserves the complete GST vertex at j:
both the input digit and the incoming multiply-by-four carry. -/
theorem gst_state_eq_of_prefix_residueS
    (R S j : Nat)
    (hres : R % 3^(j+1) = S % 3^(j+1)) :
    gstDigitS R j = gstDigitS S j ∧
      gstCarryS R j = gstCarryS S j

/-- Canonical origin causality at one exact GST vertex: the state at
position j depends only on n modulo 3^(j+1). -/
theorem gst_canonical_state_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t) :
    let a := n % 3^(j+1)
    gstDigitS (Q t n) j = gstDigitS (Q t a) j ∧
      gstCarryS (Q t n) j = gstCarryS (Q t a) j

/-- A canonical child Happy Gate is already present in the finite origin
prefix that ends exactly at the gate's causal depth. -/
theorem gst_canonical_gate_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t)
    (hgate : gstDigitS (Q t n) j = 2 ∧
      (gstCarryS (Q t n) j = 0 ∨ gstCarryS (Q t n) j = 3)) :
    let a := n % 3^(j+1)
    gstDigitS (Q t a) j = 2 ∧
      (gstCarryS (Q t a) j = 0 ∨ gstCarryS (Q t a) j = 3)
```

### F2. The self-read feedback law — the master causality law of the power stream (`GSTTheActConstruction.lean:79`)

```lean
/-- **THE SELF-READ LAW.**  For every exponent `K` and every level `j`, the
row-`j+1` trit of `4^K` is the row-`j+1` trit of the prefix-power
`4^(K mod 3^j)` plus the `j`-th trit of `K`, modulo three.  The power's
digit stream is the exponent's digit stream fed through the prefix-power's
digit stream — one feedback system, every row, every exponent, no
hypothesis. -/
theorem self_read (K j : Nat) :
    digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3

/-- **THE ROW-ONE READ.**  Row one of `4^K` is exactly `K % 3`. -/
theorem row_one_read (K : Nat) : digit3 (4^K) 1 = K % 3

/-- **THE ROW-ONE KILL.**  Every exponent `K ≡ 2 mod 3` fires its digit
two at row one. -/
theorem row_one_kill (K : Nat) (h : K % 3 = 2) : digit3 (4^K) 1 = 2

/-- **THE CANTORIAN CONSTRAINT SYSTEM.**  `CantorianPower K` holds IF AND
ONLY IF at EVERY level `j` the prefix noise plus the exponent trit never
lands on two: the entire Cantorian core is the set of exponents that
thread the feedback tree at every level. -/
theorem cantorian_iff_feedback (K : Nat) :
    CantorianPower K ↔ ∀ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 ≠ 2

/-- **THE ACT AS TREE-ESCAPE.**  The act holds IF AND ONLY IF every
exponent from eight on fires somewhere in the feedback tree. -/
theorem the_act_iff_feedback :
    GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2
```

### F3. Noise window and the unique dead child — the causality of the feedback noise

```lean
/-- **THE NOISE WINDOW LAW.**  Beyond the diagonal window the prefix
noise vanishes: when the prefix-power stays below the modulus, its
row-`j+1` trit is zero.  The feedback's noise lives in the window
`4^r ≥ 3^(j+1)`. -/
theorem noise_window_law (r j : Nat) (h : 4^r < 3^(j+1)) :
    digit3 (4^r) (j + 1) = 0

/-- **THE UNIQUE DEAD CHILD.**  At every level, every prefix owns
EXACTLY ONE dead child-trit: `(2 - noise) mod 3`.  Every node of the
dust tree has exactly two alive children, forever, by structure. -/
theorem unique_dead_child (r j : Nat) :
    ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j + 1) + t) % 3 = 2
```

### F4. The uniform kill engine — one law, every level

```lean
/-- **PREFIX UNPACKING.**  A class membership `K ≡ r + 3^j·t mod 3^(j+1)`
with `r < 3^j` and `t < 3` unpacks into: `K`'s level-`j` prefix is `r`,
and `K`'s `j`-th trit is `t`. -/
theorem prefix_unpack (K j r t : Nat) (hr : r < 3^j) (ht : t < 3)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    K % 3^j = r ∧ digit3 K j = t

/-- **THE UNIFORM KILL.**  At ANY level `j`, an alive prefix `r` and its
one dead child-trit `t` — certified by the closed noise receipt
`(digit3 (4^r) (j+1) + t) % 3 = 2` — kill the entire congruence class
`K ≡ r + 3^j·t mod 3^(j+1)` at row `j+1`: every member fires its digit
two.  Every cascade level, current and future, is an instance. -/
theorem feedback_fire_of_class (j r t K : Nat)
    (hr : r < 3^j) (ht : t < 3)
    (hnoise : (digit3 (4^r) (j + 1) + t) % 3 = 2)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    digit3 (4^K) (j + 1) = 2
```

## §G. THE INFINITE THEOREM CONTROLLERS

### G1. The main infinite control graph (`GSTGraphV2InfiniteControl.lean`, 260 lines)

```lean
/-- One enriched cell of the main infinite GST V2 graph. -/
structure InfiniteCell where
  seven : GSTCanonicalSevenAxisBridge.Vertex
  eventCode : Nat
  uCharge : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  deriving Repr

/-- Enrich one canonical seven-axis vertex with all green charge observables. -/
def cell (E t p : Nat) : InfiniteCell :=
  let v := GSTCanonicalSevenAxisBridge.vertex E t p
  {
    seven := v
    eventCode := GSTCanonicalSevenAxisBridge.event v.carry v.digit
    uCharge := gstUChargeExact v.carry
    mixedCharge := mixedDensity v.carry v.digit
    crossingCharge := crossDensity v.carry v.digit
    survive := surviveI v.carry v.digit
  }

/-- The main graph is genuinely all-depth in both arithmetic directions. -/
def graph (E : Nat) : Nat → Nat → InfiniteCell :=
  fun t p => cell E t p

/-- Every cell of the enriched graph obeys the exact x4/base3 lattice law. -/
theorem graph_cell_exact (E t p : Nat) :
    outDigit (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E (t+1) p).seven.digit ∧
      nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E t (p+1)).seven.carry

/-- Happy is event eight on the main infinite graph. -/
theorem graph_happy_iff_event_eight (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      (graph E t p).eventCode = 8

/-- Happy is equivalently positive exact crossing charge. -/
theorem graph_happy_iff_crossing_positive (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      0 < (graph E t p).crossingCharge

/-- The event-balance equation is available at every cell. -/
theorem graph_event_balance_exact (E t p : Nat) :
    (graph E t p).eventCode +
        9 * nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
      13 * (graph E t p).seven.digit + 3 * (graph E t p).seven.carry
```

The full-energy prefix-slice projection — the production socket:

```lean
/-- Seeded x4 carry used by a full-energy prefix slice. -/
def seededCarry (seed tail q : Nat) : Nat :=
  (seed + 4 * (tail % 3^q)) / 3^q

theorem prefix_slice_quotient_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    (P + 3^b * tail) / 3^(b+q) = tail / 3^q

/-- The information digit on the full-energy slice is literally the tail digit. -/
theorem prefix_slice_digit_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b+q) = digit3 tail q

/-- Exact seeded carry projection.  The seed is not assumed: it is generated
by the canonical low prefix as `floor(4*P / 3^b)`. -/
theorem prefix_slice_carry_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) =
      seededCarry ((4 * P) / 3^b) tail q

theorem prefix_slice_seed_zero
    (b P tail q : Nat) (hP : P < 3^b) (hseed : 4 * P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 0 tail q

theorem prefix_slice_seed_one
    (b P tail q : Nat) (hP : P < 3^b)
    (hlo : 3^b ≤ 4 * P) (hhi : 4 * P < 2 * 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 1 tail q

/-- Literal graph form of the prefix-slice socket.  Any exact decomposition
of the horizontal full energy gives both the tail trit and the
prefix-generated seeded carry at the corresponding vertical slice. -/
theorem graph_prefix_slice_exact
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    (graph E t (b+q)).seven.digit = digit3 tail q ∧
      (graph E t (b+q)).seven.carry =
        seededCarry ((4 * P) / 3^b) tail q

/-- On a literal full-energy slice, Happy/event-eight is exactly the seeded
Happy predicate of the exposed tail. -/
theorem graph_prefix_slice_happy_iff
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    HappyCell
        (graph E t (b+q)).seven.carry
        (graph E t (b+q)).seven.digit ↔
      digit3 tail q = 2 ∧
        (seededCarry ((4 * P) / 3^b) tail q = 0 ∨
         seededCarry ((4 * P) / 3^b) tail q = 3)
```

### G2. The never-firing tower and the Cantorian core (`GSTClimbInfiniteFamily.lean`)

```lean
/-- **THE CANTORIAN CORE.**  An exponent whose power of four carries no
digit two at any row from one upward — the exact Erdős core. -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- **THE COLLAPSE.**  The act holds IF AND ONLY IF no exponent from
eight on is a Cantorian power. -/
theorem the_act_iff_no_cantorian :
    GSTTheAct.the_act ↔ ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K

/-- **THE FINAL SOCKET.**  No Cantorian exponent from eight on ⇒ the act
⇒ `hTailF`. -/
theorem hTailF_of_no_cantorian
    (h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF

/-- **THE NEVER-FIRING TOWER.**  No sheet of the core's whole
multiplicative-three tower ever owns a ternary digit two. -/
def NeverFiringTower (core : Nat) : Prop :=
  ∀ S p : Nat, digit3 (4^(3^S * core)) (S + 1 + p) ≠ 2

/-- The never-firing tower dodges every sheet window. -/
theorem hwin_of_never_firing {core : Nat} (h : NeverFiringTower core) :
    ∀ s : Nat, 1 ≤ s →
      (GSTGraphV2OmegaWaveLaw.omegaCutWord s core) % 3^(s+2)
        < 2 * 3^(s+1)

/-- The never-firing tower dodges the diagonal fire band at every level
from three upward. -/
theorem hdust_of_never_firing {core : Nat} (h : NeverFiringTower core) :
    ∀ k : Nat, 3 ≤ k →
      (GSTGraphV2OmegaWaveLaw.omegaCutWord (k-1) 1 * core) % 3^k
        < 2 * 3^(k-1)

/-- **THE ALL-ONES DIAGONAL.**  A never-firing three-free core's scaled
diagonal is pinned to the exact middle third at every level from three
upward. -/
theorem never_firing_diagonal_all_ones {core : Nat}
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (h : NeverFiringTower core) :
    ∀ j : Nat, 2 ≤ j →
      digit3 (GSTGraphV2OmegaWaveLaw.omegaCutWord j 1 * core) j = 1

/-- **THE TOWER DUST IS EMPTY.**  No three-free core has a never-firing
tower: every core's multiplicative-three tower meets its ternary digit
two.  The six residue classes of `core % 9` each die — three at the front
row, one in the frozen band, two by the kernel-checked deep cuts. -/
theorem tower_dust_empty (core : Nat) (hfree : ¬ 3 ∣ core) :
    ¬ NeverFiringTower core
```

Also in this file: the climb family (`pair_law :70`, `wave3_deep_member :96`, `climb_witness_eighteen :119`, `wave3_deep_unbounded :135`), the prefaced window laws (`prefaced_window_law/full/sliced :149-203`), `every_row_is_read :215`, and the dust row reads:

```lean
theorem dust_row_two   (w : Nat) : digit3 (4^(3*w+1)) 2 = w % 3
theorem dust_row_three (w : Nat) : digit3 (4^(3*w+1)) 3 = (w/3) % 3
theorem dust_row_four_one (u : Nat) : digit3 (4^(9*u+1)) 4 = (u/3) % 3
theorem dust_row_four_four (u : Nat) : digit3 (4^(9*u+4)) 4 = (u/3) % 3
```

and the trit-slice laws:

```lean
theorem digit3_eq_mod_slice (X p : Nat) :
    digit3 X p = (X % 3^(p+1)) / 3^p

theorem digit3_of_top_third (X p : Nat)
    (h : 2 * 3^p ≤ X % 3^(p+1)) : digit3 X p = 2

theorem digit3_of_mid_range (X p : Nat)
    (h1 : 3^p ≤ X % 3^(p+1)) (h2 : X % 3^(p+1) < 2 * 3^p) :
    digit3 X p = 1
```

### G3. Other controller modules (all green, in the repo)

- `GSTGraphV2InfiniteControllerBridge.lean` — the bridge between the infinite control graph and the tower observers.
- `GSTV2InfiniteCore.lean`, `GSTInfiniteBadTransport.lean`, `GSTInfiniteCollision.lean`, `GSTInfiniteCoupledLedger.lean`, `GSTInfiniteFourPowerNavigation.lean` (the climb: `four_power_happy_climb`), `GSTInfiniteGateTransport.lean`.
- `GSTGraphV2CanonicalInfiniteCycle.lean`, `GSTGraphV2InfiniteBigNDichotomyScratch.lean`, `GSTGraphV2InfiniteControlScratch/Smoke.lean`.

## §H. THE POLYNOMIAL BLADES — worldtrace arithmetic proper (`GSTWorldtraceArithmetic.lean`, 1222 lines)

### H1. The binomial ladder

```lean
theorem wt_choose_one (n : Nat) : Nat.choose n 1 = n

/-- **The three-term binomial ladder.** -/
theorem one_add_pow_three_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x + x*x*x*R

/-- **The four-term binomial ladder.** -/
theorem one_add_pow_four_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + x*x*x*x*R

/-- **The five-term binomial ladder.** -/
theorem one_add_pow_five_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x
      + x*x*x*x*x*R

/-- **THE REBASE.**  Every dust power is a power of sixty-four. -/
theorem wt_rebase (m : Nat) : 4^(1+3*m) = 4 * 64^m
```

### H2. The blades

```lean
/-- **THE QUADRATIC BLADE.**  Row-window congruence of the dust power:
`4^(1+3m)` is the quadratic `4 + 252m + 15876*C(m,2)` mod 729 — the
order-two worldtrace. -/
theorem wt_quad_mod729 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]

/-- **THE CUBIC BLADE.**  One window deeper. -/
theorem wt_cubic_mod6561 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561]

/-- **THE QUARTIC BLADE.**  Two windows deeper. -/
theorem wt_quartic_mod19683 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683]
```

### H3. The reads — deep rows ARE the polynomials

```lean
/-- **ROW FIVE IS THE QUADRATIC.**  For EVERY m. -/
theorem wt_row_five_read (m : Nat) :
    digit3 (4^(1+3*m)) 5 = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5

/-- **ROW SEVEN IS THE CUBIC.** -/
theorem wt_row_seven_read (m : Nat) :
    digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7

/-- **ROW EIGHT IS THE QUARTIC.** -/
theorem wt_row_eight_read (m : Nat) :
    digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8

/-- **THE QUARTIC KILL DEMO.**  The quartic blade kills K = 82 (m = 27)
at row eight WITHOUT EVER COMPUTING `4^82`. -/
theorem wt_quartic_fire_demo : digit3 (4^(1+3*27)) 8 = 2

/-- **THE POLYNOMIAL KILL DEMO.**  The quadratic blade kills K = 85
(m = 28) at row five WITHOUT EVER COMPUTING `4^85`. -/
theorem wt_quad_fire_demo : digit3 (4^(1+3*28)) 5 = 2
```

### H4. The cascade levels — the kill tables

Level-six form (row seven, modulus 2187, 32 dead classes → 64 survivors):

```lean
theorem fire_of_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2

theorem dust_fire_row_seven (K : Nat) (hK : K % 2187 = 31 ∨ K % 2187 = 37 ∨
    K % 2187 = 118 ∨ K % 2187 = 172 ∨ K % 2187 = 253 ∨ K % 2187 = 256 ∨
    K % 2187 = 271 ∨ K % 2187 = 337 ∨ K % 2187 = 352 ∨ K % 2187 = 409 ∨
    K % 2187 = 487 ∨ K % 2187 = 490 ∨ K % 2187 = 526 ∨ K % 2187 = 568 ∨
    K % 2187 = 607 ∨ K % 2187 = 679 ∨ K % 2187 = 685 ∨
    {…16 more classes: 10, 28, 82, 100, 163, 190, 199, 244, 262, 280, 325,
     406, 442, 469, 514, 595, 616, 652…}) :
    digit3 (4^K) 7 = 2

/-- **THE DUST PINNED AT LEVEL SIX** — the 64-survivor map mod 2187. -/
theorem cantorian_dust_mod_2187 (K : Nat) (hd : K % 3 = 1)
    (hc : CantorianPower K) :
    K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 10 ∨ … ∨ K % 2187 = 2005
    -- (all 64 survivors listed in the file, :342)
```

Level-seven form (row eight, modulus 6561, 64 dead classes → 128 survivors): `fire_of_mod6561 :425`, `dust_fire_row_eight :446`, `cantarian_dust_mod_6561 :521`, `no22_of_cascade_seven :658`. Earlier levels in `GSTTheActConstruction.lean`: `fire_of_mod243 :208`, `dust_fire_row_five :230` (8 classes: 85, 91, 112, 118, 163, 175, 190, 202 mod 243), `fire_of_mod729 :367`, `dust_fire_row_six :389` (16 classes: 31, 37, 172, 253, 256, 271, 337, 352, 409, 487, 490, 526, 568, 607, 679, 685 mod 729); survivor maps `cantorian_dust_mod_9/27/81/243/729` (:254-:423).

Cumulative structure: **66 dead classes across 7 levels; the survivor set doubles 2 → 4 → 8 → 16 → 32 → 64 → 128 at every level, by `unique_dead_child`.**

### H5. The pair-read infinite family — GAP-E1

```lean
/-- **THE PAIR-READ FORMULA.**  The two-support tower factorization, read
through the green `prefaced_digit`: for `1 ≤ j` and any trunk `T` with
`4^T < 3^(j+2)`, the row-`(j+4)` digit of `4^(T + 3^(j+1)*u)` is the
row-two digit of the worldtrace product `4^T * u * c (j+1)`. -/
theorem pair_read_formula (T u j : Nat) (hj : 1 ≤ j) (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2

/-- **THE PAIR-READ FIRE.**  Every exponent `K = 4 + 3^(j+1)*u` with `j ≥ 4`
and `u ∈ {1, 4, 7}` fires its digit two at row `j+4`. -/
theorem pair_read_fire (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2

/-- **THE PAIR-READ RESIDUE.**  The worldtrace product's mod-27 residue is
computable without the tower: `c (j+1)` is `16 mod 27`. -/
theorem pair_residue_mod27 (T u j : Nat) (hj : 2 ≤ j) :
    (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27

/-- **THE ROW-TWO READ FROM THE KILL ZONE.** -/
theorem digit3_row_two_of_residue (x : Nat) (hx : 18 ≤ x % 27) :
    digit3 x 2 = 2

/-- **THE GENERAL TRUNK-UNIFORM FIRE.**  ANY trunk `T`, ANY branch `u`:
whenever `(4^T * u * 16) % 27 ≥ 18`, the exponent `T + 3^(j+1)*u` fires
its digit two at row `j+4`.  The kill condition is a mod-27 computation
on the trunk residue and the branch — the Cantor automaton's transition,
uniform across the entire dust tree. -/
theorem pair_read_fire_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2

/-- SECOND FAMILY — trunk-13: fires at row j+4 for every j ≥ 15. -/
theorem pair_read_fire_demo_two (j : Nat) (hj : 15 ≤ j) :
    digit3 (4^(13 + 3^(j+1))) (j+4) = 2

/-- THIRD FAMILY — trunk-10 branch-two: fires at row j+4 for every j ≥ 11. -/
theorem pair_read_fire_demo_three (j : Nat) (hj : 11 ≤ j) :
    digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2
```

### H6. The descent engine — the top split and the addition window

```lean
/-- **THE EXACT TOP SPLIT.**  For an exponent `K` whose top trit sits at
position `H`, the power splits as the trunk power, the branch term, and a
tail dead below row `2H+2`.  The deep rows of `4^K` are a pure base-3
addition of the trunk's digits and the shifted digits of
`X = t * c(H) * 4^trunk`. -/
theorem top_split (K H : Nat) (hK : K < 3^(H+1)) :
    ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)
        + 3^(H+1) * Y)

/-- **THE ADDITION WINDOW.**  Below row `2H+2`, the digits of `4^K` read
the two-term sum `4^trunk + 3^(H+1) * X` — the dead tail of the top
split is invisible. -/
theorem window_congr (K H r : Nat) (hK : K < 3^(H+1)) (hr : r + 1 ≤ 2*H+2) :
    digit3 (4^K) r = digit3 (4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r

/-- **THE ROW-(H+2) WINDOW LAW.**  The digit at row `H+2` of `4^K` is the
trunk's own digit at that row, plus the first trit of the branch factor,
plus the carry from row `H+1` — a pure base-3 addition read. -/
theorem window_row_two (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1)) :
    digit3 (4^K) (H+2)
      = (digit3 (4^(K % 3^H)) (H+2)
          + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
          + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3
```

### H7. The dust window laws — the branch term vanishes mod nine

```lean
/-- **THE PERIOD-NINE LAW.**  `4^r mod 9` depends only on `r mod 3`. -/
theorem four_pow_mod9 (r : Nat) : (4:Nat)^r % 9 = 4^(r % 3) % 9

/-- **THE DUST BRANCH FACTOR.**  For a dust trunk (`trunk mod 3 = 1`) the
branch factor `X = t * c(H) * 4^trunk` satisfies `X mod 9 = t` —
`c(H)` is `7 mod 9`, `4^trunk` is `4 mod 9`, and `7 * 4 = 28 = 1 mod 9`:
the branch factor's first trit VANISHES. -/
theorem dust_branch_mod9 (t trunk H : Nat) (hH : 1 ≤ H) (htr : trunk % 3 = 1)
    (ht : t < 3) :
    (t * GSTTowerFire.c H * 4^trunk) % 9 = t

/-- **THE DUST ROW-(H+2) LAW — the branch term vanishes.**  For a dust
exponent the row-(H+2) digit is JUST the trunk's digit plus the carry. -/
theorem window_row_two_dust (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1))
    (hdust : K % 3 = 1) :
    digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
      + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3

/-- **THE WINDOW REDUCE.**  The digit at row `H+1+s` sees only X's first
`s+1` trits — the consumers' computational handle. -/
theorem window_reduce (A X H s : Nat) : ...   -- :1087
```

## §I. THE TOWER FIRE LAWS (`GSTTowerFire.lean`)

```lean
/-- **Divide-and-mod gluing.** -/
theorem div_add_lt (k q s : Nat) (hs : s < 3^k) : (3^k * q + s) / 3^k = q

/-- **The prefaced read.**  If `s < 3^(n+1)` then row `n+1+k` of the
prefaced object `3^(n+1) * A + s` is row `k` of `A`. -/
theorem prefaced_digit (A s n k : Nat) (hs : s < 3^(n+1)) :
    digit3 (3^(n+1) * A + s) (n+1+k) = digit3 A k

/-- **THE DEEP-HIDER MASTER LEMMA.**  Rows `n+1 .. 2n+1` of `4^(j * 3^n)`
are the digits `0 .. n` of `j * c n`: one tower constant governs every
scaled family at every depth. -/
theorem tower_digit_read (j n k : Nat) (hk : k ≤ n) :
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k

/-- **THE n+2 LAW.**  `3^n` fires at row `n+2` for every `n ≥ 1`. -/
theorem three_pow_fires (n : Nat) (hn : 1 ≤ n) : digit3 (4^(3^n)) (n+2) = 2

/-- **THE n+1 LAW.**  `2 * 3^n` fires at row `n+1` for every `n ≥ 0`. -/
theorem two_mul_three_pow_fires (n : Nat) : digit3 (4^(2 * 3^n)) (n+1) = 2

/-- **THE n+4 LAW.**  `3^n + 1` fires at row `n+4` for every `n ≥ 3`:
the prefaced tower constant `4 * c n ≡ 64 mod 81 = 2101₃` plants the TWO
at offset three. -/
theorem three_pow_plus_one_fires (n : Nat) (hn : 3 ≤ n) :
    digit3 (4^(3^n + 1)) (n+4) = 2
```

The tower-axis covers $s \geq 1$ structurally (`GSTTowerAxis.lean`):

```lean
theorem tower_axis_level_one   (s c : Nat) (hs : 1 ≤ s) (hc : c % 9 = 1) : ...
theorem tower_axis_level_two   (s c : Nat) (hs : 2 ≤ s) (hc : c % 27 = 4 ∨ ...) : ...
theorem tower_axis_level_three (s c : Nat) (hs : 3 ≤ s) (hc : ...) : ...
theorem not_cantarian_of_tower_axis {K s c : Nat} (hK : K = 3^s * c) ... : ¬ CantorianPower K
theorem no22_of_tower_axis {K s c : Nat} (hK : K = 3^s * c) ... : noTernaryTwo (4^K) = false
```

## §J. THE DIAGONAL READ — the triage (`GSTDiagonalRead.lean`)

```lean
/-- Every positive exponent decomposes uniquely as `3^v · u` with
`u` not divisible by three — the valuation cut. -/
theorem valuation_decomp (K : Nat) :
    0 < K → ∃ v u : Nat, K = 3^v * u ∧ u % 3 ≠ 0

/-- **THE DIAGONAL WINDOW LAW** — every exponent's entire readable band,
one law, all scales: for `j ≤ v`, row `v+1+j` of `4^(3^v*u)` is row `j`
of `u * lteCoeff v`. -/
theorem diagonal_window_law (v u j : Nat) (hj : j ≤ v) :
    digit3 (4^(3^v * u)) (v + 1 + j) = digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j

/-- **THE WINDOW-CLEAN DUST.**  The read's exact residual: exponents whose
reduced core is `1 mod 3` and whose readable diagonal never fires. -/
def WindowCleanDust (K : Nat) : Prop :=
  ∃ v u : Nat, K = 3^v * u ∧ u % 3 = 1 ∧
    ∀ j ≤ v, digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j ≠ 2

/-- **THE TRIAGE.**  Every exponent `K ≥ 8` either owns its digit two — by
the front fire or by a window fire, both uniform laws — or is window-clean
dust.  No third case: the whole plane of exponents, one dichotomy. -/
theorem every_exponent_fires (K : Nat) (hK : 8 ≤ K) :
    (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K

/-- **THE SOCKET, COMPLETE.**  Dust empty ⇒ the act ⇒ `hTailF`. -/
theorem hTailF_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
```

Window fire families (uniform, all green): `window_fire_level1` ($u \equiv 1 \bmod 9 \Rightarrow$ row $v{+}2$ fires), `window_fire_level2` ($u \equiv 13, 25 \bmod 27 \Rightarrow$ row $v{+}3$), `window_fire_level3` ($u \equiv 4, 34, 49, 70 \bmod 81 \Rightarrow$ row $v{+}4$).

## §K. THE ONE LANE — the whole construction, one theorem, zero hypotheses (`GSTTailFOneLane.lean`)

```lean
/-- **THE CANONICAL DECOMPOSITION.**  Every positive exponent `M` is a
tower-core pair `M = 3^s * core` with `core` three-free. -/
theorem one_lane_three_free_decomposition (M : Nat) : 0 < M →
    ∃ s core : Nat, M = 3^s * core ∧ ¬ 3 ∣ core

/-- **THE TOWER'S UNIT WORD.**  The cut word of the unit core is the LTE
mean itself: `omegaCutWord s 1 = lteCoeff s`. -/
theorem one_lane_cut_word_one (s : Nat) : omegaCutWord s 1 = lteCoeff s

/-- **FIRE AT THE CUT ROW.**  Every sheet-core pair whose core is congruent
to two modulo three fires at row `s+1`. -/
theorem one_lane_fire_of_mod3_two (s core : Nat) (h : core % 3 = 2) :
    digit3 (4^(3^s * core)) (s+1) = 2

/-- **FIRE ABOVE THE CUT.**  Every tower core congruent to one modulo nine,
above sheet zero, fires at row `s+2`. -/
theorem one_lane_fire_of_tower_mod9_one (s core : Nat) (hs : 1 ≤ s)
    (h : core % 9 = 1) : digit3 (4^(3^s * core)) (s+2) = 2

/-- **FIRE AT ROW TWO OF THE SHEET-ZERO CYCLE.**  Every exponent congruent
to seven modulo nine fires at row two. -/
theorem one_lane_row2_fire (K : Nat) (h : K % 9 = 7) :
    digit3 (4^K) 2 = 2

/-- **THE ONE-LANE CASE MAP.**  For every exponent `K+1`: either `4^(K+1)`
owns a ternary digit two, or the exponent's canonical sheet-core pair
carries the full no-fire certificate — the three-free family clause of the
shadow package together with a cut word whose every depth dodges the top
third.  Unconditional. -/
theorem one_lane_complete (K : Nat) :
    (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i))

/-- **THE CERTIFICATE'S FACES.**  Every exponent carrying the dust
certificate satisfies the shadow package's window clause, diagonal clause,
and row-all-depths clause. -/
theorem one_lane_certificate_faces (s core : Nat)
    (hfam : core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
    (hnever : ∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) :
    (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j)

/-- **THE ONE-LANE RECEIPT — the whole construction, one theorem, zero
hypotheses.**  Every exponent's case map (fire or the complete dust
certificate), the certificate's faces, the engine (the exact cube lift),
the three-window dichotomy, the dust's shape, and the floor identity. -/
theorem one_lane_the_whole_construction :
    (∀ K : Nat, (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i))) ∧
    (∀ s core : Nat,
      (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) →
      (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) →
      ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
        (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
          (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
        (s = 0 → ∀ j : Nat, 2 ≤ j →
          (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j))) ∧
    (∀ s core : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))) ∧
    (∀ s core : Nat, 1 ≤ s → core % 3 = 1 ∨ core % 3 = 2 →
      (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
      ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
      ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
        ∧ ∀ S : Nat, s+1 ≤ S →
          digit3 (4^(3^S * core)) (S + (s+2)) = 2)) ∧
    (∀ core : Nat, core % 3 = 1 ∨ core % 3 = 2 →
      (∀ s : Nat, 1 ≤ s →
        (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) →
      (∀ k : Nat, 3 ≤ k →
        (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∀ k : Nat, 3 ≤ k →
        3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
          ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
```

## §L. The proof-file composition (`GSTTailFProof.lean`, 434 lines)

```lean
/-- **THE ROW EYE.** -/
theorem row_observation_law (core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2

/-- **THE TOWER EYE.** -/
theorem tower_observation_law (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2

/-- **THE WAVE FACE — the GST observation law itself, advanced form.**
A Happy cell on the unit sheet of the power column, with an all-depth bad
boundary three x4 waves to its right, is not erased: it reappears as a
strictly positive coupled-U derivative.  Information propagates, never
dies — the observation law of the universe, stated on the physical graph. -/
theorem observation_law_wave :
    ∀ (K q : Nat),
      (HappyCell (graph (4^K) 0 (3+q)).seven.carry
                 (graph (4^K) 0 (3+q)).seven.digit) →
      (∀ j : Nat, ¬ HappyCell (graph (4^K) 3 (3+j)).seven.carry
                       (graph (4^K) 3 (3+j)).seven.digit) →
      0 < graphPhaseWindow (4^K) 0 3 (q+1) ∧
        graphPhaseWindow (4^K) 3 3 (q+1) ≤ 0 ∧
        64 * (graph (4^K) 0 (3+q)).seven.digit +
            wideCarry 64 (4^K) (3+q) =
          (graph (4^K) 3 (3+q)).seven.digit +
            3 * wideCarry 64 (4^K) ((3+q)+1) ∧
        0 < 3 * potentialWith gstUChargeExact (4^3)
              (unifiedState (4^K) 3 ((3+q)+1)).core -
            potentialWith gstUChargeExact (4^3)
              (unifiedState (4^K) 3 (3+q)).core

/-- **THE CURRENT — the ontological spacetime certificate.**  A physical
cell of the dimensionless graph is Happy exactly when its ontological
current is positive. -/
theorem universe_current_happy_iff (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < GSTGraphV2Ontological.ontDensity C d

/-- **THE NO-ERASURE WINDOW.**  A Happy source on the left edge of any
nonzero-width production window keeps the window's ontological current
strictly positive. -/
theorem universe_window_positive_of_happy (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell (graph E 0 (b+q)).seven.carry
                      (graph E 0 (b+q)).seven.digit) :
    0 < GSTGraphV2Ontological.graphOntWindow E N b (q+1)

/-- **THE PROOF OF hTailF** (climb form — the single named primitive). -/
theorem hTailF
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    four_power_omega_shadow_wave_tailF

/-- **THE TERMINAL IDENTITY, CARRIED INTO THE PROOF FILE.** -/
theorem hTailF_iff_even_conjecture :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE META-VIEW RECEIPT.**  One theorem, four faces: the observation
law uniform over every family; the uniform ignition blade uniform over
every level; the dust boundary; the floor identity. -/
theorem meta_view_all_classes_all_levels :
    (∀ s core j : Nat, 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1) →
        digit3 (4^(3^s * core)) (s+1+j) = 2) ∧
    (∀ k core S : Nat, 1 ≤ k → k ≤ S+1 →
        2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k →
        digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (∀ core : Nat, ¬ omega_diagonal_survivor_dust core →
        ∃ k : Nat, 3 ≤ k ∧ ∀ S : Nat, k-1 ≤ S →
          digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (four_power_omega_shadow_wave_tailF ↔
        ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)

theorem even_conjecture_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false
```

Lattice cycle laws (new laws, deepest levels):

```lean
theorem new_law_four_pow_mod2187 (m : Nat) :
    (4^m) % 2187 = (4^(m % 729)) % 2187
theorem new_law_four_pow_mod6561 (m : Nat) :
    (4^m) % 6561 = (4^(m % 2187)) % 6561
theorem four_pow_mod243 (m : Nat) : (4^m) % 243 = (4^(m % 81)) % 243
theorem four_pow_mod729 (m : Nat) : (4^m) % 729 = (4^(m % 243)) % 729
```

## §M. The exact U-machinery (`GSTGraphV2HandwrittenOmegaUBlock.lean`)

```lean
def originTrit (n : Nat) : Nat := n % 3
def originTail (n : Nat) : Nat := n / 3

theorem origin_split_exact (n : Nat) :
    n = originTrit n + 3 * originTail n

/-- The kernel-grade content of the handwritten simultaneous x/div U symbol:
all perfect-power energy is conserved while one ternary origin trit is
consumed into the left phase factor. -/
theorem perfect_power_u_mul_div_exact (t n : Nat) :
    4^(3^t * n) =
      4^(3^t * originTrit n) * 4^(3^(t+1) * originTail n)

def residualEnergy (s k m : Nat) : Nat := 4^(3^(s+k) * m)
def residualWidth (s : Nat) : Nat := 3^s
def residualChildExponent (s k m : Nat) : Nat := 3^(s+k) * m
def residualParentExponent (s k m : Nat) : Nat := 3^s * (1 + 3^k * m)

theorem residual_parent_energy_exact (s k m : Nat) :
    4^(residualWidth s) * residualEnergy s k m =
      4^(residualParentExponent s k m)

/-- Full Graph-V2 realization: every physical observable at the alleged
all-bad right boundary is literally the absolute perfect-power sheet at
the canonical parent exponent. -/
theorem residual_parent_observables_exact (s k m p : Nat) :
    (graph (residualEnergy s k m) (residualWidth s) p).seven.carry =
        (graph 1 (residualParentExponent s k m) p).seven.carry ∧
    (graph (residualEnergy s k m) (residualWidth s) p).seven.digit =
        (graph 1 (residualParentExponent s k m) p).seven.digit ∧
    … (eventCode, uCharge, mixedCharge, crossingCharge, survive) …

/-- Happy/event-eight transport at the actual residual parent boundary. -/
theorem residual_parent_happy_iff (s k m p : Nat) :
    HappyCell (graph (residualEnergy s k m) (residualWidth s) p).seven.carry
              (graph (residualEnergy s k m) (residualWidth s) p).seven.digit ↔
      HappyCell (graph 1 (residualParentExponent s k m) p).seven.carry
                (graph 1 (residualParentExponent s k m) p).seven.digit
```

## §N. Verified numerical receipts of the worldtrace descent (modular, exact big-int; all 0 failures)

These are machine-verified laws of the machinery (from the derivations, `/tmp` receipts, kept as experimental ground truth):

- **D1**: $W_t(3m) = 3\,W_{t+1}(m)$ where $W_t(m) := (4^{3^t m} - 1)/3^{t+1} = \omega\mathrm{CutWord}(t,m)$ — 8/8 exact passes.
- **D2**: $W_t(3q+1) = 1 + 12\,W_{t+1}(q)$ — 9/9 passes.
- **D3 (transfer)**: $W_t(3^t m + 1) = 1 + 4 \cdot 3^t\, W_t(m)$ — 24/24 passes.
- **D4 (stabilization)**: $\text{trit}_j(W_t(m)) = \text{trit}_j(c_t \cdot m)$ for $j \le t$, where $c_0 = 1, c_1 = 7, c_2 = 9709, c_3 = 222399981598543, \ldots$ ($c_t = \mathrm{lteCoeff}(t)$) — 27/27 passes.
- **D4b**: $\text{trits}(W_t(m)) = \text{trits}(c_\infty \cdot m)$ below depth $t$, with $c_\infty$ the frozen limit (trits $[1,2,1,0,2,2,0,1,0,2,1,2,1,0,\ldots]$) — 27/27 passes.
- **D5 (emit-2 table)**: the carry-digit emit law of $4W$: emit 2 exactly on pairs $(\text{carry},\text{digit}) \in \{(0,2),(1,1),(2,0),(3,2)\}$; carry $\in \{0..3\}$ satisfies $v_j = \text{digit}_j(4R) + \text{carry}$, $\text{carry}_{j+1} = \text{carry4}$ — 0 failures / 31458 steps.
- **D6**: dust-equivalence + shift structure + fire-row tapes for cores 10/28/82/244/100/163 — all confirmed; 444/444 scan agreement, zero 2-free $4W_t(m)$ for $K \equiv 1 \bmod 9$ in $[10,4000]$.
- **C1 (climb law)**: $W_t(3q+r) = W_t(r) + 3 \cdot (4^{3^t})^r \cdot W_{t+1}(q)$ — 60/60 passes.

---

# PART III — THE GST GRAPH V2 ONTOLOGICAL UNIVERSE GRAPH

## III.1 The construction protocol (exact, step by step)

**Step 1 — Choose the energy.** Fix a natural $E \geq 1$ (the "energy" / seed). The graph will describe the worldtrace family of all powers $4^t \cdot E$.

**Step 2 — The coordinate plane.** Coordinates are $(t, p) \in \mathbb{N} \times \mathbb{N}$:
- $t$ = **horizontal axis** = the x4 stride (each step right multiplies the energy by 4),
- $p$ = **vertical axis** = the ternary depth (each step up divides by 3 and reads one more trit).

**Step 3 — The seven-axis vertex** (verbatim, `GSTCanonicalSevenAxisBridge.lean:29`):

```lean
/-- Canonical non-Euclidean seven-axis vertex.  The coordinates are arithmetic
state coordinates, not metric coordinates. -/
structure Vertex where
  horizontal : Nat        -- t
  horizontalNext : Nat    -- t+1
  vertical : Nat          -- p
  carry : Nat             -- carry4 (4^t * E) p        ∈ {0,1,2,3}
  space : Space           -- spaceOfCarry carry         ∈ {null, altMinus, gstPlus}
  digit : Nat             -- digit3 (4^t * E) p        ∈ {0,1,2}
  descent : Nat           -- (4^t * E) / 3^p
  nextDescent : Nat       -- (4^t * E) / 3^(p+1)
  deriving Repr

/-- The three physical GST spaces carried by the seven-axis state. -/
inductive Space
  | null
  | altMinus
  | gstPlus

def spaceOfCarry (C : Nat) : Space :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

/-- The actual perfect-power sheet sampled in x4 horizontal stride. -/
def vertex (E t p : Nat) : Vertex where
  horizontal := t
  horizontalNext := t + 1
  vertical := p
  carry := carry4 (4^t * E) p
  space := spaceOfCarry (carry4 (4^t * E) p)
  digit := digit3 (4^t * E) p
  descent := (4^t * E) / 3^p
  nextDescent := (4^t * E) / 3^(p+1)
```

**Step 4 — The exact lattice law.** The graph is an exact x4/base-3 cellular automaton:

```lean
/-- The x4 carry regenerates exactly in the vertical ternary direction. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = nextCarry (carry4 R p) (digit3 R p)

/-- Multiplication by four exposes the local x4 output trit exactly. -/
theorem digit3_mul_four_exact (R p : Nat) :
    digit3 (4 * R) p = outDigit (carry4 R p) (digit3 R p)

/-- The canonical sheet is an exact x4/base3 cell lattice at every pair of
natural coordinates. -/
theorem canonical_cell_exact (E t p : Nat) :
    outDigit (vertex E t p).carry (vertex E t p).digit =
        (vertex E (t+1) p).digit ∧
      nextCarry (vertex E t p).carry (vertex E t p).digit =
        (vertex E t (p+1)).carry
```

That is: **moving right** (t → t+1) applies the cell $(C,d) \mapsto \text{outDigit}(C,d) = (C + 4d) \bmod 3$; **moving up** (p → p+1) applies $(C,d) \mapsto \text{nextCarry}(C,d) = (C + 4d)/3$. The twelve physical cells are $C \in \{0,1,2,3\} \times d \in \{0,1,2\}$.

**Step 5 — The event coordinate and the Happy predicate.**

```lean
/-- The radix event coordinate of one x4 GST cell.  It records the input and
output trit in one number `0..8`; event eight is exactly `2 -> 2`. -/
def event (C d : Nat) : Nat := d + 3 * outDigit C d

/-- Exact seven-axis event balance: the apparent x4/base3 exponential update
collapses to one linear arithmetic identity with a live upper carry. -/
theorem event_balance_exact (C d : Nat) :
    event C d + 9 * nextCarry C d = 13 * d + 3 * C

/-- Event eight is precisely the two physical Happy/SURVIVE realizations. -/
theorem happy_iff_event_eight (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ event C d = 8
```

`HappyCell C d` (defined in `GSTU2DEventTransport`) is $d = 2 \wedge (C = 0 \vee C = 3)$: **a ternary digit 2 that survives the x4 multiplication with null or GST+ carry.** The object of Part 0 is exactly: *every $K \ge 8$ has a Happy cell somewhere on the column $t=0$ of the graph of $4^K$.* (The bridge: `graph_prefix_slice_happy_iff` + `happy_iff_event_eight` + `hasTernaryTwo_of_digit`.)

**Step 6 — Enrichment (the infinite control graph).** Attach all green charge observables to every vertex (§G1): `eventCode`, `uCharge`, `mixedCharge`, `crossingCharge`, `survive` — giving `InfiniteCell`, and the graph

$$\Gamma_E : \mathbb{N} \times \mathbb{N} \to \text{InfiniteCell}, \qquad \Gamma_E(t,p) = \text{cell}(E,t,p).$$

**The graph is one single function on the full infinite plane — every finite rectangle is an observation of the same object.**

## III.2 The physics on the graph

- **The 2D divergence law** (§E): on every finite rectangle, the mixed density's total mass = BIG1 boundary charge + carry flux + positive SURVIVE incidence — a discrete Gauss law. Happy chords: NULL = hidden $2 \to 1 \to 2$, GST+ = all-SURVIVE $2 \to 2 \to 2$ (`happy_chord_dichotomy`).
- **The U operator** (`uJump_divergence`): the handwritten U jump is *itself* a two-direction divergence — horizontal information transport plus the ternary carry-potential derivative.
- **The wave observation law** (`observation_law_wave`): a Happy cell with an all-depth bad boundary is NOT erased — it reappears as a strictly positive coupled-U derivative three waves to the right. Information propagates, never dies.
- **The ontological current** (below): Happy = positive current, on every cell and every window.

## III.3 The ontological current — reverse base-seven certificate (`GSTGraphV2Ontological.lean`)

```lean
/-- Horizontal information potential for the pure ontological current. -/
def ontDigitPotential (d : Nat) : Int :=
  if d = 0 then 9 else if d = 1 then -35 else -91

/-- Vertical carry potential for the pure ontological current. -/
def ontCarryPotential (C : Nat) : Int :=
  if C = 0 then 0 else if C = 1 then 77 else if C = 2 then 154 else 252

/-- Pure x7/base3 divergence.  Unlike the older crossing densities this has no
interior SURVIVE source term. -/
def ontDensity (C d : Nat) : Int :=
  ontDigitPotential (outDigit C d) - 7 * ontDigitPotential d +
    ontCarryPotential C - 3 * ontCarryPotential (nextCarry C d)

/-- Complete twelve-state certificate.  Exactly the two Happy cells are
positive; every bad physical cell is nonpositive; the global floor is -54. -/
theorem ontDensity_physical_table :
    ontDensity 0 0 = -54 ∧ ontDensity 0 1 = -21 ∧ ontDensity 0 2 = 84 ∧
    ontDensity 1 0 = -21 ∧ ontDensity 1 1 = 0 ∧ ontDensity 1 2 = -33 ∧
    ontDensity 2 0 = 0 ∧ ontDensity 2 1 = -54 ∧ ontDensity 2 2 = 0 ∧
    ontDensity 3 0 = -33 ∧ ontDensity 3 1 = 0 ∧ ontDensity 3 2 = 42

/-- A physical Happy cell injects at least 42 units of ontological current. -/
theorem ontDensity_ge_42_of_happy (C d : Nat) (h : HappyCell C d) :
    (42 : Int) ≤ ontDensity C d

/-- Happy is exactly the positive sector of the pure ontological current. -/
theorem happy_iff_ontDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < ontDensity C d
```

The accumulation and no-erasure laws:

```lean
/-- Reverse-base-seven accumulation of one horizontal graph row. -/
def reverseOntCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCode C d N + ontDensity (C N) (d N)

/-- Exact horizontal telescope of the pure ontological current. -/
theorem reverseOntCode_exact (C Cnext d : Nat → Nat) : ∀ N : Nat, ...

/-- Global floor for an arbitrary physical horizontal row. -/
theorem reverseOntCode_ge_global_floor (C d : Nat → Nat) : ∀ N : Nat, ...

/-- **Pure horizontal no-erasure.**  A leading Happy cell starts with at least
42.  Every later physical cell costs at most 54 while the current is
multiplied by seven: 33*7^N + 63 ≤ 7*code_N. -/
theorem reverseOntCode_ge_scaled_of_leading_happy ... 

/-- **Ontological highest-Happy-row domination.**  The base-seven pure
current has enough margin that a leading Happy row beats the total
worst-case mass of all lower rows under the literal base-three vertical
weighting. -/
theorem weightedOntPrefix_positive_of_top_leading_happy ...

/-- A Happy source on the left edge gives strictly positive ontological
current through every nonzero-width Graph-V2 block. -/
theorem graphOntWindow_positive_of_happy
    (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell (graph E 0 (b+q)).seven.carry
                      (graph E 0 (b+q)).seven.digit) :
    0 < graphOntWindow E N b (q+1)
```

## III.4 The geometry family (all green modules, all constructible the same way)

- `GSTGraphV2SixAdicOntologicalGeometry.lean` + `...GeometryLaws.lean` + `...GeometryTest.lean` — the six-adic ontological geometry of the twelve cells.
- `GSTGraphV2NonEuclidean.lean` + `GSTGraphV2NonEuclideanLaws.lean` — the non-Euclidean (arithmetic-state, not metric) coordinate laws.
- `GSTGraphV2Production.lean` + `GSTGraphV2ProductionLaws.lean` — production windows on the graph.
- `GSTGraphV2CoupledUFlux.lean` / `GSTGraphV2CoupledUPhysicalBridge.lean` — the coupled U-flux potentials.
- `GSTGraphV2UnifiedPowerRectangle.lean` / `GSTGraphV2UnifiedVerticalTelescope.lean` — the unified rectangle and vertical telescope.
- `GSTGraphV2CanonicalDescentOntology.lean` / `GSTGraphV2DescentOntology.lean` — descent ontology layers.
- `GSTGraphV2PerfectPowerAncestry/BlockCollision/BlockProbe.lean` — perfect-power block structure.
- `GSTGraphV2CanonicalRenormalization.lean`, `GSTGraphV2CanonicalSheetTranslation.lean`, `GSTGraphV2CanonicalPhaseSteering.lean`, `GSTGraphV2CanonicalNWave.lean`, `GSTGraphV2CanonicalEscape.lean`.
- The monolith `ErdosTernary2.lean` (18,527 lines) — the kernel: `noTernaryTwo`, the odd-exponent half, the weakening chain (`omegaShadow` → `tail2` → `tail` → `tail3` → `tail4` → `tail5` → `tailE` → `tailF`), the terminal identity, and the crown `erdos_ternary_2_universal_of_tailF`.

---

# PART IV — PROVE THIS

## THE OBJECT

$$\boxed{\;\forall\, K \ge 8 : \quad \text{the worldtrace of } 4^K \text{ contains a digit } 2\;}$$

equivalently (all five green-equivalent forms of Part 0):

$$\textbf{(F)}\;\; \forall K \ge 8\;\; \exists j:\; \big(\mathrm{trit}_{j+1}(4^{K \bmod 3^j}) + \mathrm{trit}_j(K)\big) \bmod 3 = 2$$

$$\textbf{(C)}\;\; \nexists K \ge 8:\; \forall p \ge 1,\; \mathrm{trit}_p(4^K) \ne 2 \quad (\text{no Cantorian power above } 8)$$

$$\textbf{(D)}\;\; \forall K \ge 8:\; \neg\,\mathrm{WindowCleanDust}(K)$$

$$\textbf{(P)}\;\; \text{tailF\_row\_primitive} \;\wedge\; \text{tailF\_tower\_primitive}$$

$$\textbf{(W)}\;\; \forall K > 500:\; \mathrm{omegaShadowTailF}(K) \Rightarrow \exists p:\; \mathrm{trit}_p(4^K) = 2$$

Each form has a named one-line green consumer in the repo; any one of them closes `the_act`, which by the kernel-certified terminal identity closes the even half, which with the green odd half closes the **full Erdős ternary conjecture**.

## THE MACHINERY IS YOURS

Everything in Parts I–III is verified, green, and yours: the Ω operator and its worldtrace orbit law; the LTE cut and the cut words; the observer laws (one law, all levels); the 4th-dimension emergent diagonal and its cube-lift engine; the 2D mixed-emergence divergence theorem; the causality laws (prefix causality, self-read feedback, noise window, unique dead child); the infinite controllers; the polynomial blades (quadratic/cubic/quartic); the pair-read family; the descent engine; the seven cascade levels with their doubling survivor maps; the tower fire laws; the diagonal read triage; the one-lane case map; the middle-third pinning; the GST Graph V2 Ontological Universe Graph with its exact construction protocol, its twelve-cell physics, its ontological current, and its no-erasure laws.

## THE NOTE

> **You can — and should — go into MUCH more depth than this document. Discover NEW laws which we did not notice. Use the machinery in COMPLETELY different ways than anything hinted at here. Compose the observers, the blades, the currents, the causality laws, the controllers, the universe graph — in configurations nobody has tried. The only demand is the object above.**
>
> **DELIVER THE PROOF AS A FULL MATHEMATICAL DERIVATION IN LATEX — NOT LEAN CODE.**

---

*Repo: `kyo-oo/erdosternary2` @ `sol/kyo-gate-universe-wire`, HEAD `fd89766`. Every theorem quoted: CI-green, 0 sorries, axioms `[propext, Classical.choice, Quot.sound]`.*
