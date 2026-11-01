/-=============================================================================
  GST PATTERN LIFT — THE PATTERN FRONTIER OF ERDŐS PROBLEM #406
  ==============================================================================
  Chronological label: bulldoze/erdos-weak-problems-20261101, file #1.
  Base branch: gpt6/problem406-rowtwo-first-hit-exact-20261030 (tip 9e73d77).

  THE UNSOLVED PROBLEM (Erdős problem #406, erdosproblems.com):
    The ternary digits of powers of 2. Erdős (1979) asks: does 2^n contain
    the ternary digit 2 for ALL n >= 9? OPEN. The site's note (Saye) records
    that 2^n contains every possible ternary DIGIT for 16 <= n <= 5.9*10^21,
    and raises the pattern question: which finite ternary STRINGS occur in
    the base-3 expansion of powers of 2?

  WHAT THIS FILE KILLS (the pattern frontier — answered YES, machine-verified):
    Every finite ternary word W over {0,1,2}:
      * occurs as the TERMINAL digit block of 2^n (if W's first digit != 0),
      * occurs at EVERY prescribed interior position k >= 1 of some 2^n,
      * and each occurrence is realized by INFINITELY MANY n (unboundedly
        large exponents keep the pattern).
    In particular: arbitrarily long runs of 0s, of 1s, of 2s, and every
    finite block configuration, occur in ternary expansions of powers of 2.
    Problem #406 itself remains open; this file certifies its frontier.

  THE COMPLETE STEP-BY-STEP PROOF (each step = a theorem below):
    §1  Arithmetic infrastructure (core-only mod/div plumbing).
    §2  Geometric factorization:  x^u = 1 + (x-1) * GeomS x u.
    §3  THE LTE TOWER (the empire's GST spine): for every v,
          4^(3^v) = 1 + 3^(v+1) * W v    with  3 ∤ W v,
        proved by geometric factorization x^3 - 1 = (x-1)(x^2+x+1) plus the
        mod-9 valuation x^2+x+1 ≡ 3 (mod 9) whenever x ≡ 1 (mod 3).
    §4  Near-one expansion (1 + 3^m c)^j ≡ 1 + 3^m (c j) (mod 3^(m+1)), j <= 2;
        the slice lemma (residues mod 3 steer residues mod 3^(m+1));
        the selector (multiplication by a unit mod 3 permutes {0,1,2}).
    §5  THE MAIN LIFT (Hensel-by-hand): for every m >= 1 and every unit a,
        some power of 2 hits a mod 3^m:
            { 2^n mod 3^m : n >= 0 } = (Z/3^m)^*.
        This is 3-adic density of the powers of 2 in the unit group
        (classically: 2 is a primitive root mod 3^m for all m).
    §6  Digit machinery: digit3 is a function of the residue mod 3^(p+1);
        every word is a tail; every word occurs at every interior position;
        all-zero runs at the spine positions 2^(2*3^L).
    §7  Period law 2^(2*3^(M-1)) ≡ 1 (mod 3^M): one hit becomes unboundedly
        many hits. THE HEADLINE THEOREMS.

  DISCIPLINE: Lean 4 core only. No Mathlib. No sorry. No axiom.
    No native_decide. No unbounded decide (NO-OOM law).
    Verify:  lean bulldoze/problem406-pattern-front/GSTPatternLift.lean
=============================================================================-/

namespace GSTPatternLift

/-=============================================================================
  §0. THE READER
=============================================================================-/

/-- The ternary digit of N at position p (position 0 = least significant). -/
def digit3 (N p : Nat) : Nat := N / 3 ^ p % 3

/-- P occurs in N at position pos: digits pos, pos+1, ... match P in order
    (P[0] is the digit at position pos; P read lowest-position-first). -/
def patternAt (N pos : Nat) (P : List Nat) : Prop :=
  ∀ j (hj : j < P.length), digit3 N (pos + j) = P[j]'hj

/-- The value of a digit list placed at positions 0,1,2,...  -/
def patVal (P : List Nat) : Nat :=
  P.foldr (fun d acc => d + 3 * acc) 0

/-=============================================================================
  §1. ARITHMETIC INFRASTRUCTURE (core-only)
=============================================================================-/

theorem three_pow_pos (m : Nat) : 0 < 3 ^ m := by
  induction m with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ]; omega

theorem three_pow_ge_three (m : Nat) (hm : 1 ≤ m) : 3 ≤ 3 ^ m := by
  have h1 : 3 ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
  have h2 : 3 ^ 1 = 3 := rfl
  omega

theorem three_pow_le_mono (a b : Nat) (h : a ≤ b) : 3 ^ a ∣ 3 ^ b := by
  have hsplit : 3 ^ (a + (b - a)) = 3 ^ a * 3 ^ (b - a) := Nat.pow_add 3 a (b - a)
  have hab : a + (b - a) = b := by omega
  rw [← hab, hsplit]
  exact ⟨3 ^ (b - a), rfl⟩

/-- (a*b)*(c*d) = (a*c)*(b*d) — the product shuffle. -/
theorem mul_shuffle (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc a b (c * d), ← Nat.mul_assoc b c d, Nat.mul_comm b c,
      Nat.mul_assoc c b d, ← Nat.mul_assoc a c (b * d)]

theorem mod3_ne_zero_cases (a : Nat) (ha : ¬ 3 ∣ a) : a % 3 = 1 ∨ a % 3 = 2 := by
  have hlt : a % 3 < 3 := Nat.mod_lt a (Nat.succ_pos 2)
  have hne : a % 3 ≠ 0 := fun h0 => ha ⟨a / 3, by omega⟩
  omega

theorem three_not_dvd_mul (a b : Nat) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) : ¬ 3 ∣ (a * b) := by
  intro hd
  obtain ⟨q, hq⟩ := hd
  have ha1 : a % 3 = 1 ∨ a % 3 = 2 := mod3_ne_zero_cases a ha
  have hb1 : b % 3 = 1 ∨ b % 3 = 2 := mod3_ne_zero_cases b hb
  have hprod : (a * b) % 3 = ((a % 3) * (b % 3)) % 3 := Nat.mul_mod a b 3
  have hzero : (a * b) % 3 = 0 := by rw [hq, Nat.mul_mod_right 3 q]
  rw [hzero] at hprod
  rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2 <;> rw [h1, h2] at hprod <;> omega

/-- (a*c + b)/c = a when b < c: the division uniqueness lemma. -/
theorem div_add_lt (a b c : Nat) (hc : 0 < c) (hb : b < c) : (a * c + b) / c = a := by
  rw [Nat.add_comm, Nat.mul_comm a c, Nat.add_mul_div_left b a hc,
      Nat.div_eq_of_lt hb, Nat.zero_add]

/-- Division uniqueness: x = A*M + C with C < M gives x / M = A. -/
theorem div_uniq (x M A C : Nat) (hM : 0 < M) (hC : C < M) (h : x = A * M + C) :
    x / M = A := by
  rw [h]
  exact div_add_lt A C M hM hC

/-- a/3^(k+1) = (a/3^k)/3 — the division cascade. -/
theorem div_step (x k : Nat) : x / 3 ^ (k + 1) = (x / 3 ^ k) / 3 := by
  rw [Nat.pow_succ 3 k, Nat.div_div_eq_div_mul]



/-=============================================================================
  §2. THE GEOMETRIC FACTORIZATION (core-only, subtraction-free)
    x ^ u = 1 + (x - 1) * GeomS x u,    GeomS x u = Σ_{i<u} x^i
=============================================================================-/

/-- GeomS x u = x^0 + x^1 + ... + x^(u-1). -/
def GeomS (x u : Nat) : Nat :=
  match u with
  | 0 => 0
  | u + 1 => GeomS x u + x ^ u

theorem geom_factor (x u : Nat) (hx : 1 ≤ x) :
    x ^ u = 1 + (x - 1) * GeomS x u := by
  induction u with
  | zero => rfl
  | succ u ih =>
      have h1 : x ^ (u + 1) = x * x ^ u := Nat.pow_succ'
      have h2 : GeomS x (u + 1) = GeomS x u + x ^ u := rfl
      obtain ⟨W, hW⟩ : ∃ W, W = x - 1 := ⟨_, rfl⟩
      rw [← hW] at ih ⊢
      rw [h1, h2, ih]
      -- goal: x * (1 + W * GeomS x u) = 1 + W * (GeomS x u + (1 + W * GeomS x u))
      obtain ⟨G, hG⟩ : ∃ G, G = GeomS x u := ⟨_, rfl⟩
      rw [← hG]
      have hxc : W + 1 = x := by omega
      have hpx2 : x * W = W * W + W := by
        rw [← hxc, Nat.add_mul, Nat.one_mul]
      have hp4 : x * (W * G) = W * (W * G) + W * G := by
        rw [← Nat.mul_assoc, hpx2, Nat.add_mul, Nat.mul_assoc]
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_add, Nat.mul_one, hp4]
      omega

/-- 1 % m is 0 or 1. -/
theorem one_mod_cases (m : Nat) : 1 % m = 0 ∨ 1 % m = 1 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; exact Or.inr rfl
    · have hm1 : m = 1 := by omega
      subst hm1; exact Or.inl rfl
  · exact Or.inr (Nat.mod_eq_of_lt (by omega))

theorem geomS_mod (x u m : Nat) (hx : x % m = 1 % m) :
    (GeomS x u) % m = u % m := by
  have hpu : ∀ j, x ^ j % m = 1 % m := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih2 =>
        have hp : x ^ (j + 1) = x * x ^ j := Nat.pow_succ'
        have hc : 1 % m = 0 ∨ 1 % m = 1 := one_mod_cases m
        rw [hp, Nat.mul_mod x (x ^ j) m, hx, ih2]
        rcases hc with h0 | h0
        · rw [h0]; rfl
        · rw [h0]; exact h0
  induction u with
  | zero => rfl
  | succ u ih =>
      have h2 : GeomS x (u + 1) = GeomS x u + x ^ u := rfl
      rw [h2, Nat.add_mod, ih, hpu u, Nat.add_mod u 1 m]

/-=============================================================================
  §3. THE LTE TOWER (the GST spine, exact valuation form)
    3^(v+1) ∣ 4^(3^v) - 1   and   ¬ 3^(v+2) ∣ 4^(3^v) - 1
    i.e. 4^(3^v) = 1 + 3^(v+1) * W v  with  3 ∤ W v.
=============================================================================-/

def W (v : Nat) : Nat := (4 ^ (3 ^ v) - 1) / 3 ^ (v + 1)

theorem lte_exact (v : Nat) :
    3 ^ (v + 1) ∣ 4 ^ (3 ^ v) - 1 ∧ ¬ 3 ^ (v + 2) ∣ 4 ^ (3 ^ v) - 1 := by
  induction v with
  | zero =>
      have h2 : (3 : Nat) ^ (0 + 1) = 3 := rfl
      have h3 : (3 : Nat) ^ (0 + 2) = 9 := rfl
      have he : 4 ^ (3 ^ 0) - 1 = 3 := by decide
      refine ⟨?_, ?_⟩
      · rw [h2, he]
        exact ⟨1, rfl⟩
      · intro hd
        obtain ⟨q, hq⟩ := hd
        rw [h3, he] at hq
        omega
  | succ v ih =>
      obtain ⟨hd1, hnd1⟩ := ih
      have h3 : 3 ^ (v + 1) = 3 ^ v * 3 := Nat.pow_succ 3 v
      have hpow : 4 ^ (3 ^ (v + 1)) = (4 ^ (3 ^ v)) ^ 3 := by
        rw [h3, Nat.pow_mul]
      have hx1 : 1 ≤ 4 ^ (3 ^ v) := Nat.one_le_pow (3 ^ v) 4 (by decide)
      obtain ⟨q, hq⟩ := hd1
      have hxe : 4 ^ (3 ^ v) - 1 = 3 ^ (v + 1) * q := by omega
      have hgeom : (4 ^ (3 ^ v)) ^ 3 = 1 + ((4 ^ (3 ^ v)) - 1) * GeomS (4 ^ (3 ^ v)) 3 :=
        geom_factor (4 ^ (3 ^ v)) 3 hx1
      have hS : GeomS (4 ^ (3 ^ v)) 3
          = 4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1 := by
        have e1 : GeomS (4 ^ (3 ^ v)) 1 = GeomS (4 ^ (3 ^ v)) 0 + (4 ^ (3 ^ v)) ^ 0 := rfl
        have e2 : GeomS (4 ^ (3 ^ v)) 2
            = GeomS (4 ^ (3 ^ v)) 1 + (4 ^ (3 ^ v)) ^ 1 := rfl
        have e3 : GeomS (4 ^ (3 ^ v)) 3
            = GeomS (4 ^ (3 ^ v)) 2 + (4 ^ (3 ^ v)) ^ 2 := rfl
        have g0 : GeomS (4 ^ (3 ^ v)) 0 = 0 := rfl
        have p2 : (4 ^ (3 ^ v)) ^ 2 = 4 ^ (3 ^ v) * 4 ^ (3 ^ v) := by
          rw [Nat.pow_succ, Nat.pow_one]
        rw [e3, e2, e1, g0, Nat.pow_zero, Nat.pow_one, p2]
        omega
      have hxmod3 : (4 ^ (3 ^ v)) % 3 = 1 := by
        have hsplit : 4 ^ (3 ^ v) = 3 ^ (v + 1) * q + 1 := by omega
        have hz : (3 ^ (v + 1) * q) % 3 = 0 := by
          have e : 3 ^ (v + 1) * q = 3 * (3 ^ v * q) := by
            rw [Nat.pow_succ 3 v, Nat.mul_comm (3 ^ v) 3, ← Nat.mul_assoc]
          rw [e, Nat.mul_mod_right]
        rw [hsplit, Nat.add_mod, hz]
      have hS3 : 3 ∣ 4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1 := by
        refine ⟨(4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1) / 3, ?_⟩
        have hm : (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1) % 3 = 0 := by
          rw [Nat.add_mod (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v)) 1 3,
              Nat.add_mod (4 ^ (3 ^ v) * 4 ^ (3 ^ v)) (4 ^ (3 ^ v)) 3,
              Nat.mul_mod (4 ^ (3 ^ v)) (4 ^ (3 ^ v)) 3, hxmod3]
        have hsum := Nat.div_add_mod (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1) 3
        omega
      have hS9 : ¬ 9 ∣ 4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1 := by
        intro hd
        obtain ⟨s, hs⟩ := hd
        have hm : (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1) % 9 = 0 := by
          rw [hs]; exact Nat.mul_mod_right 9 s
        have hprod9 : (4 ^ (3 ^ v) * 4 ^ (3 ^ v)) % 9
            = 4 ^ (3 ^ v) % 9 * ((4 ^ (3 ^ v)) % 9) % 9 :=
          Nat.mul_mod (4 ^ (3 ^ v)) (4 ^ (3 ^ v)) 9
        have hx9lt : (4 ^ (3 ^ v)) % 9 < 9 := Nat.mod_lt _ (Nat.succ_pos 8)
        have hx93 : (4 ^ (3 ^ v)) % 9 % 3 = (4 ^ (3 ^ v)) % 3 :=
          Nat.mod_mod_of_dvd _ (⟨3, by omega⟩ : (3 : Nat) ∣ 9)
        have hcase : (4 ^ (3 ^ v)) % 9 = 1 ∨ (4 ^ (3 ^ v)) % 9 = 4 ∨ (4 ^ (3 ^ v)) % 9 = 7 := by
          rw [hxmod3] at hx93
          omega
        rw [Nat.add_mod (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v)) 1 9,
            Nat.add_mod (4 ^ (3 ^ v) * 4 ^ (3 ^ v)) (4 ^ (3 ^ v)) 9, hprod9] at hm
        rcases hcase with hc | hc | hc <;> rw [hc] at hm <;> omega
      have hprod : 4 ^ (3 ^ (v + 1)) - 1
          = (4 ^ (3 ^ v) - 1) * (4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1) := by
        rw [hpow, hgeom, hS]
        omega
      obtain ⟨s, hs⟩ := hS3
      have hxs : 4 ^ (3 ^ v) * 4 ^ (3 ^ v) + 4 ^ (3 ^ v) + 1 = 3 * s := by omega
      constructor
      · refine ⟨q * s, ?_⟩
        have hsplit : 3 ^ (v + 2) = 3 ^ (v + 1) * 3 := Nat.pow_succ 3 (v + 1)
        rw [hprod, hxe, hxs, hsplit]
        exact mul_shuffle (3 ^ (v + 1)) q 3 s
      · -- the exact-valuation endgame: cancel 3^(v+1), split 3 ∣ q*s
        intro hd
        obtain ⟨t, ht⟩ := hd
        have hfull : 4 ^ (3 ^ (v + 1)) - 1 = 3 ^ (v + 1) * (q * (3 * s)) := by
          rw [hprod, hxe, hxs, Nat.mul_assoc]
        have hp3 : 3 ^ (v + 3) = 3 ^ (v + 1) * 9 := by
          have e0 : (v + 1) + 2 = v + 3 := rfl
          have e1 : 3 ^ ((v + 1) + 2) = 3 ^ (v + 1) * 3 ^ 2 := Nat.pow_add 3 (v + 1) 2
          have e2 : (3:Nat) ^ 2 = 9 := by decide
          rw [e0] at e1
          rw [e1, e2]
        rw [hp3, Nat.mul_assoc] at ht
        have hcancel : 9 * t = q * (3 * s) :=
          Nat.mul_left_cancel (three_pow_pos (v + 1)) (by omega)
        have hjuggle : q * (3 * s) = 3 * (q * s) := by
          rw [Nat.mul_comm q (3 * s), Nat.mul_assoc 3 s q, Nat.mul_comm s q]
        have hdiv : 3 ∣ q * s := by
          refine ⟨t, ?_⟩
          have h2 : 3 * (q * s) = 3 * (3 * t) := by omega
          exact Nat.mul_left_cancel (Nat.succ_pos 2) h2
        by_cases hq3 : 3 ∣ q
        · -- then 3^(v+2) ∣ 4^(3^v) - 1, contradicting hnd1
          obtain ⟨u, hu⟩ := hq3
          refine hnd1 ⟨u, ?_⟩
          have hs2 : 3 ^ (v + 2) = 3 ^ (v + 1) * 3 := Nat.pow_succ 3 (v + 1)
          rw [hs2, hxe, hu, Nat.mul_assoc]
        · by_cases hs3 : 3 ∣ s
          · -- then 9 ∣ x^2+x+1, contradicting hS9
            obtain ⟨u, hu⟩ := hs3
            refine hS9 ⟨u, ?_⟩
            rw [hxs, hu]
            omega
          · exact absurd hdiv (three_not_dvd_mul q s hq3 hs3)

/-- The spine in equation form: 4^(3^v) = 1 + 3^(v+1) * W v with 3 ∤ W v. -/
theorem W_val (v : Nat) : 4 ^ (3 ^ v) = 1 + 3 ^ (v + 1) * W v ∧ ¬ 3 ∣ W v := by
  obtain ⟨hd1, hnd1⟩ := lte_exact v
  obtain ⟨q, hq⟩ := hd1
  have hx1 : 1 ≤ 4 ^ (3 ^ v) := Nat.one_le_pow (3 ^ v) 4 (by decide)
  have hsplit : 4 ^ (3 ^ v) = 3 ^ (v + 1) * q + 1 := by omega
  have hWq : W v = q := by
    show (4 ^ (3 ^ v) - 1) / 3 ^ (v + 1) = q
    rw [hq, Nat.mul_comm]
    exact div_add_lt q 0 (3 ^ (v + 1)) (three_pow_pos (v + 1)) (three_pow_pos (v + 1))
  refine ⟨?_, ?_⟩
  · rw [hWq, hsplit]; omega
  · rw [hWq]
    intro h3
    obtain ⟨u, hu⟩ := h3
    refine hnd1 ⟨u, ?_⟩
    have hs2 : 3 ^ (v + 2) = 3 ^ (v + 1) * 3 := Nat.pow_succ 3 (v + 1)
    rw [hs2, Nat.mul_assoc, ← hu]
    exact hq

/-=============================================================================
  §4. NEAR-ONE EXPANSION, SELECTOR, AND LIFT BOOKKEEPING
=============================================================================-/

/-- The selector: for q, d and a unit u mod 3, some t ≤ 2 steers q + u*t to d mod 3. -/
theorem selector (q u d : Nat) (hu : u = 1 ∨ u = 2) (hd : d < 3) :
    ∃ t, t ≤ 2 ∧ (q + u * t) % 3 = d := by
  rcases hu with hu | hu
  · subst hu
    exact ⟨(d + 3 - q % 3) % 3, by omega, by omega⟩
  · subst hu
    exact ⟨2 * ((d + 3 - q % 3) % 3) % 3, by omega, by omega⟩

/-- Multiplying the coefficient t by P or by P mod 3 gives the same residue mod 3. -/
theorem coeff_mod (s P t : Nat) : (s + P * t) % 3 = (s + P % 3 * t) % 3 := by
  obtain ⟨D, hD⟩ : ∃ D, D = P / 3 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = P % 3 := ⟨_, rfl⟩
  have hsplit : P = 3 * D + R := by
    rw [hD, hR]
    exact (Nat.div_add_mod P 3).symm
  have hbridge : 3 * D * t = 3 * (D * t) := Nat.mul_assoc 3 D t
  have h1 : s + P * t = (s + R * t) + 3 * (D * t) := by
    rw [hsplit, Nat.add_mul, hbridge]
    omega
  have h2 : (s + P * t) % 3 = (s + R * t) % 3 := by
    rw [h1, Nat.add_mul_mod_self_left]
  rw [hR] at h2
  exact h2

/-- Near-one expansion, additive existence form: for t ≤ 2,
    (1 + 3^m*c)^t = 1 + 3^m*(c*t) + 3^(m+1)*e. -/
theorem near_one_add (m t c : Nat) (hm : 1 ≤ m) (ht : t ≤ 2) :
    ∃ e, (1 + 3 ^ m * c) ^ t = 1 + 3 ^ m * (c * t) + 3 ^ (m + 1) * e := by
  have ht3 : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht3 with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · refine ⟨0, ?_⟩
    have e1 : (1 + 3 ^ m * c) ^ 1 = 1 + 3 ^ m * c := Nat.pow_one _
    have e2 : c * 1 = c := Nat.mul_one c
    have e4 : 3 ^ (m + 1) * 0 = 0 := Nat.mul_zero _
    rw [e1, e2, e4, Nat.add_zero]
  · refine ⟨3 ^ (m - 1) * (c * c), ?_⟩
    have hexpand : (1 + 3 ^ m * c) ^ 2
        = 1 + (3 ^ m * c + 3 ^ m * c) + (3 ^ m * c) * (3 ^ m * c) := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one,
          Nat.left_distrib, Nat.mul_one, Nat.right_distrib, Nat.one_mul]
      omega
    have hsquare : (3 ^ m * c) * (3 ^ m * c)
        = 3 ^ (m + 1) * (3 ^ (m - 1) * (c * c)) := by
      have hsh : (3 ^ m * c) * (3 ^ m * c) = (3 ^ m * 3 ^ m) * (c * c) :=
        mul_shuffle (3 ^ m) c (3 ^ m) c
      have hpm : 3 ^ m * 3 ^ m = 3 ^ (m + m) := (Nat.pow_add 3 m m).symm
      have hsp : 3 ^ ((m + 1) + (m - 1)) = 3 ^ (m + 1) * 3 ^ (m - 1) :=
        Nat.pow_add 3 (m + 1) (m - 1)
      have hmm : m + m = (m + 1) + (m - 1) := by omega
      rw [hsh, hpm, hmm, hsp]
      exact Nat.mul_assoc _ _ _
    have htwo : 3 ^ m * c + 3 ^ m * c = 3 ^ m * (c * 2) := by
      have hcc : c + c = c * 2 := by omega
      rw [← Nat.mul_add, hcc]
    rw [hexpand, htwo, hsquare]

/-- The expansion identity powering the lift: multiplying a near-one factor into
    a 3^m-decomposition keeps the r + 3^m*(s + r*C) shape. -/
theorem mul_near_id (m s r C E : Nat) (hm : 1 ≤ m) :
    ∃ K, (3 ^ m * s + r) * (1 + 3 ^ m * C + 3 ^ (m + 1) * E)
        = r + 3 ^ m * (s + r * C) + 3 ^ (m + 1) * K := by
  refine ⟨3 ^ (m - 1) * (s * C) + 3 ^ m * (s * E) + r * E, ?_⟩
  have id1 : 3 ^ m * s * (3 ^ m * C) = 3 ^ (m + 1) * (3 ^ (m - 1) * (s * C)) := by
    have hsh : 3 ^ m * s * (3 ^ m * C) = (3 ^ m * 3 ^ m) * (s * C) :=
      mul_shuffle (3 ^ m) s (3 ^ m) C
    have hpm : 3 ^ m * 3 ^ m = 3 ^ (m + m) := (Nat.pow_add 3 m m).symm
    have hsp : 3 ^ ((m + 1) + (m - 1)) = 3 ^ (m + 1) * 3 ^ (m - 1) :=
      Nat.pow_add 3 (m + 1) (m - 1)
    have hmm : m + m = (m + 1) + (m - 1) := by omega
    rw [hsh, hpm, hmm, hsp]
    exact Nat.mul_assoc _ _ _
  have id2 : r * (3 ^ m * C) = 3 ^ m * (r * C) := by
    rw [← Nat.mul_assoc, Nat.mul_comm r (3 ^ m), Nat.mul_assoc]
  have id3 : 3 ^ m * s * (3 ^ (m + 1) * E) = 3 ^ (m + 1) * (3 ^ m * (s * E)) := by
    have hsh : 3 ^ m * s * (3 ^ (m + 1) * E) = (3 ^ m * 3 ^ (m + 1)) * (s * E) :=
      mul_shuffle (3 ^ m) s (3 ^ (m + 1)) E
    have hpm : 3 ^ m * 3 ^ (m + 1) = 3 ^ (m + (m + 1)) := (Nat.pow_add 3 m (m + 1)).symm
    have hpm2 : 3 ^ (m + (m + 1)) = 3 ^ ((m + 1) + m) := by rw [Nat.add_comm]
    have hsp : 3 ^ ((m + 1) + m) = 3 ^ (m + 1) * 3 ^ m := Nat.pow_add 3 (m + 1) m
    rw [hsh, hpm, hpm2, hsp]
    exact Nat.mul_assoc _ _ _
  have id4 : r * (3 ^ (m + 1) * E) = 3 ^ (m + 1) * (r * E) := by
    rw [← Nat.mul_assoc, Nat.mul_comm r (3 ^ (m + 1)), Nat.mul_assoc]
  rw [Nat.left_distrib, Nat.left_distrib, Nat.mul_one, Nat.add_mul, Nat.add_mul,
      id1, id2, id3, id4, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

/-- Lift bookkeeping: for r < 3^m,
    (r + 3^m*X + 3^(m+1)*Y) % 3^(m+1) = r + 3^m*(X % 3). -/
theorem lift_digit_mod (m r X Y : Nat) (hr : r < 3 ^ m) :
    (r + 3 ^ m * X + 3 ^ (m + 1) * Y) % 3 ^ (m + 1) = r + 3 ^ m * (X % 3) := by
  have hp : 3 ^ m * 3 = 3 ^ (m + 1) := (Nat.pow_succ 3 m).symm
  have hkey : r + 3 ^ m * X = r + 3 ^ m * (X % 3) + 3 ^ (m + 1) * (X / 3) := by
    have h1 : 3 ^ m * X = 3 ^ m * (3 * (X / 3) + X % 3) := by
      congr 1
      exact (Nat.div_add_mod X 3).symm
    rw [h1, Nat.mul_add, ← Nat.mul_assoc, hp]
    omega
  rw [hkey, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
  have hx3 : X % 3 ≤ 2 := by omega
  have hbound : 3 ^ m * (X % 3) ≤ 3 ^ m * 2 := Nat.mul_le_mul_left _ hx3
  have hlt2 : 3 ^ m * 2 < 3 ^ m * 3 := Nat.mul_lt_mul_of_pos_left (by omega) (three_pow_pos m)
  have hfin : r + 3 ^ m * (X % 3) < 3 ^ (m + 1) := by
    rw [← hp]
    omega
  exact Nat.mod_eq_of_lt hfin

/-=============================================================================
  §5. THE MAIN LIFT: {2^n mod 3^m} = (Z/3^m)^* — 3-adic density by hand
=============================================================================-/

theorem powers_hit_all_units : ∀ (m : Nat), 1 ≤ m → ∀ (a : Nat), ¬ 3 ∣ a →
    ∃ n, 2 ^ n % 3 ^ m = a % 3 ^ m := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro hm a ha
      rcases Nat.eq_zero_or_pos m with rfl | hmp
      · -- base: mod 3^1 = mod 3
        rcases mod3_ne_zero_cases a ha with h1 | h1
        · exact ⟨0, by
            have e1 : (3 : Nat) ^ (0 + 1) = 3 := rfl
            have e2 : (2 : Nat) ^ 0 = 1 := rfl
            rw [e1, e2, h1]⟩
        · exact ⟨1, by
            have e1 : (3 : Nat) ^ (0 + 1) = 3 := rfl
            have e2 : (2 : Nat) ^ 1 = 2 := rfl
            rw [e1, e2, h1]⟩
      · -- the genuine step: m ≥ 1
        obtain ⟨n0, hn0⟩ := ih hmp a ha
        -- the tower at m - 1
        have hpow2D : 2 ^ (2 * 3 ^ (m - 1)) = 4 ^ (3 ^ (m - 1)) := by
          rw [Nat.pow_mul]
        obtain ⟨hw1, hw2⟩ := W_val (m - 1)
        have hshift : (m - 1) + 1 = m := by omega
        rw [hshift] at hw1
        have h2D : 2 ^ (2 * 3 ^ (m - 1)) = 1 + 3 ^ m * W (m - 1) := by
          rw [hpow2D, hw1]
        have h3m : 3 ∣ 3 ^ m := three_pow_le_mono 1 m hmp
        have h2n0_unit : ¬ 3 ∣ 2 ^ n0 := by
          intro hd
          have hm1 : 2 ^ n0 % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
          have hmm1 : 2 ^ n0 % 3 ^ m % 3 = 2 ^ n0 % 3 := Nat.mod_mod_of_dvd (2 ^ n0) h3m
          have hmm2 : a % 3 ^ m % 3 = a % 3 := Nat.mod_mod_of_dvd a h3m
          have ha3 : a % 3 = 0 := by omega
          exact ha ⟨a / 3, by omega⟩
        have hprodunit : ¬ 3 ∣ (2 ^ n0 * W (m - 1)) :=
          three_not_dvd_mul (2 ^ n0) (W (m - 1)) h2n0_unit hw2
        have hu3 : 2 ^ n0 * W (m - 1) % 3 = 1 ∨ 2 ^ n0 * W (m - 1) % 3 = 2 :=
          mod3_ne_zero_cases _ hprodunit
        -- residue bookkeeping
        have hr' : a % 3 ^ m < 3 ^ m := Nat.mod_lt a (three_pow_pos m)
        have hdecomp : 2 ^ n0 = 3 ^ m * (2 ^ n0 / 3 ^ m) + a % 3 ^ m := by
          have h1 := Nat.div_add_mod (2 ^ n0) (3 ^ m)
          omega
        have hA : a = a % 3 ^ m + 3 ^ m * (a / 3 ^ m) := by
          have h1 := Nat.div_add_mod a (3 ^ m)
          omega
        have hreq : a % 3 ^ m % 3 = 2 ^ n0 % 3 := by
          have h1 := Nat.mod_mod_of_dvd (2 ^ n0) h3m
          have h2 := Nat.mod_mod_of_dvd a h3m
          omega
        have hrwv : (a % 3 ^ m * W (m - 1)) % 3 = (2 ^ n0 * W (m - 1)) % 3 := by
          have h1 : (a % 3 ^ m * W (m - 1)) % 3
              = (a % 3 ^ m % 3 * ((W (m - 1)) % 3)) % 3 := Nat.mul_mod _ _ 3
          have h2 : (2 ^ n0 * W (m - 1)) % 3
              = (2 ^ n0 % 3 * ((W (m - 1)) % 3)) % 3 := Nat.mul_mod _ _ 3
          rw [h1, h2, hreq]
        -- the selector picks the lift digit
        have hd3 : a / 3 ^ m % 3 < 3 := Nat.mod_lt _ (Nat.succ_pos 2)
        obtain ⟨t, ht2, htsel⟩ := selector (2 ^ n0 / 3 ^ m) (2 ^ n0 * W (m - 1) % 3)
          (a / 3 ^ m % 3) hu3 hd3
        -- near-one expansion of (2^D)^t
        obtain ⟨e, he⟩ := near_one_add m t (W (m - 1)) hmp ht2
        have h2n : 2 ^ (n0 + t * (2 * 3 ^ (m - 1)))
            = (3 ^ m * (2 ^ n0 / 3 ^ m) + a % 3 ^ m)
              * (1 + 3 ^ m * (W (m - 1) * t) + 3 ^ (m + 1) * e) := by
          rw [Nat.pow_add, Nat.mul_comm t (2 * 3 ^ (m - 1)), Nat.pow_mul, h2D, ← he]
          exact congrArg (fun Z => Z * (1 + 3 ^ m * W (m - 1)) ^ t) hdecomp
        -- the expansion identity
        obtain ⟨K, hK⟩ := mul_near_id m (2 ^ n0 / 3 ^ m) (a % 3 ^ m) (W (m - 1) * t) e hmp
        have hF2 : 2 ^ (n0 + t * (2 * 3 ^ (m - 1)))
            = a % 3 ^ m + 3 ^ m * (2 ^ n0 / 3 ^ m + a % 3 ^ m * (W (m - 1) * t))
              + 3 ^ (m + 1) * K := by
          rw [h2n, hK]
        have hF3 : 2 ^ (n0 + t * (2 * 3 ^ (m - 1))) % 3 ^ (m + 1)
            = a % 3 ^ m
              + 3 ^ m * ((2 ^ n0 / 3 ^ m + a % 3 ^ m * (W (m - 1) * t)) % 3) := by
          rw [hF2]
          exact lift_digit_mod m (a % 3 ^ m)
            (2 ^ n0 / 3 ^ m + a % 3 ^ m * (W (m - 1) * t)) K hr'
        -- the coefficient congruence closes the selector circuit
        have hcoef : (2 ^ n0 / 3 ^ m + a % 3 ^ m * (W (m - 1) * t)) % 3
            = a / 3 ^ m % 3 := by
          have hassoc : a % 3 ^ m * (W (m - 1) * t) = (a % 3 ^ m * W (m - 1)) * t :=
            (Nat.mul_assoc _ _ _).symm
          rw [hassoc, coeff_mod, hrwv, htsel]
        -- the lift digit of a
        have hF5 : a % 3 ^ (m + 1) = a % 3 ^ m + 3 ^ m * (a / 3 ^ m % 3) := by
          generalize hr0 : a % 3 ^ m = R
          generalize hQ : a / 3 ^ m = Q
          rw [hA, hQ, hr0]
          have hrR : R < 3 ^ m := by rw [← hr0]; exact hr'
          exact lift_digit_mod m R Q 0 hrR
        refine ⟨n0 + t * (2 * 3 ^ (m - 1)), ?_⟩
        rw [hF3, hcoef, hF5]

/-=============================================================================
  §6. DIGIT MACHINERY: residues steer digits; words live at every position
=============================================================================-/

/-- digit3 is computed from the residue mod 3^(p+1). -/
theorem digit3_eq (N p : Nat) : digit3 N p = (N % 3 ^ (p + 1)) / 3 ^ p := by
  have hqp : 0 < 3 ^ p := three_pow_pos p
  have hQP : 3 ^ p * 3 = 3 ^ (p + 1) := (Nat.pow_succ 3 p).symm
  have hre : N / 3 ^ p = 3 * (N / 3 ^ (p + 1)) + N % 3 ^ (p + 1) / 3 ^ p := by
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = N / 3 ^ (p + 1) := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = N % 3 ^ (p + 1) := ⟨_, rfl⟩
    have h2 : 3 ^ p * (3 * Q) = 3 ^ (p + 1) * Q := by
      rw [← Nat.mul_assoc, hQP]
    have h1 : N = 3 ^ p * (3 * Q) + R := by
      rw [h2, hQ, hR]
      exact (Nat.div_add_mod N (3 ^ (p + 1))).symm
    have hRb : R % 3 ^ p < 3 ^ p := Nat.mod_lt _ hqp
    have h3 : 3 ^ p * (3 * Q + R / 3 ^ p) = 3 ^ p * (3 * Q) + 3 ^ p * (R / 3 ^ p) := by
      rw [Nat.mul_add]
    have h4 := Nat.div_add_mod R (3 ^ p)
    have hkey : N = 3 ^ p * (3 * Q + R / 3 ^ p) + R % 3 ^ p := by
      rw [h3]
      omega
    rw [← hQ, ← hR]
    exact div_uniq N (3 ^ p) (3 * Q + R / 3 ^ p) (R % 3 ^ p) hqp hRb
      (by rw [Nat.mul_comm]; exact hkey)
  show N / 3 ^ p % 3 = (N % 3 ^ (p + 1)) / 3 ^ p
  rw [hre, Nat.add_comm (3 * (N / 3 ^ (p + 1))) (N % 3 ^ (p + 1) / 3 ^ p),
      Nat.add_mul_mod_self_left]
  have hlt : N % 3 ^ (p + 1) < 3 ^ (p + 1) := Nat.mod_lt N (three_pow_pos (p + 1))
  have hbound : N % 3 ^ (p + 1) / 3 ^ p < 3 := by
    rcases Nat.lt_or_ge (N % 3 ^ (p + 1) / 3 ^ p) 3 with h3 | h3
    · exact h3
    · exfalso
      have hR := Nat.div_add_mod (N % 3 ^ (p + 1)) (3 ^ p)
      have hmono : 3 ^ p * 3 ≤ 3 ^ p * (N % 3 ^ (p + 1) / 3 ^ p) :=
        Nat.mul_le_mul_left _ h3
      rw [hQP] at hmono
      omega
  rw [Nat.mod_eq_of_lt hbound]

/-- Equal residues mod 3^q give equal digits at every p with p + 1 ≤ q. -/
theorem digit3_residue (N N' p q : Nat) (hpq : p + 1 ≤ q)
    (h : N % 3 ^ q = N' % 3 ^ q) : digit3 N p = digit3 N' p := by
  have hd1 : N % 3 ^ (p + 1) = N' % 3 ^ (p + 1) := by
    have h1 : N % 3 ^ q % 3 ^ (p + 1) = N % 3 ^ (p + 1) :=
      Nat.mod_mod_of_dvd N (three_pow_le_mono (p + 1) q hpq)
    have h2 : N' % 3 ^ q % 3 ^ (p + 1) = N' % 3 ^ (p + 1) :=
      Nat.mod_mod_of_dvd N' (three_pow_le_mono (p + 1) q hpq)
    rw [← h1, ← h2, h]
  have e1 := digit3_eq N p
  have e2 := digit3_eq N' p
  rw [e1, e2, hd1]

/-- Digits at position pos+j of N are digits at position j of N / 3^pos. -/
theorem digit3_shift (N pos j : Nat) : digit3 N (pos + j) = digit3 (N / 3 ^ pos) j := by
  show N / 3 ^ (pos + j) % 3 = N / 3 ^ pos / 3 ^ j % 3
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- The value of a digit word is below 3 to the word length. -/
theorem patVal_lt : ∀ (P : List Nat), (∀ d ∈ P, d < 3) → patVal P < 3 ^ P.length := by
  intro P
  induction P with
  | nil =>
      intro hP
      have e1 : patVal ([] : List Nat) = 0 := rfl
      have e2 : 3 ^ ([] : List Nat).length = 1 := rfl
      rw [e1, e2]
      omega
  | cons d rest ih =>
      intro hP
      have hmem : ∀ e ∈ rest, e < 3 := fun e he => hP e (List.mem_cons.mpr (Or.inr he))
      have hd3 : d < 3 := hP d (List.mem_cons.mpr (Or.inl rfl))
      have hV : patVal (d :: rest) = d + 3 * patVal rest := rfl
      have hlen : (d :: rest).length = rest.length + 1 := rfl
      have hZ := ih hmem
      have hp : 3 ^ (rest.length + 1) = 3 ^ rest.length * 3 := Nat.pow_succ 3 rest.length
      rw [hV, hlen, hp]
      omega

/-- The j-th ternary digit of the value of a word is the j-th entry of the word. -/
theorem digit3_patVal (P : List Nat) (hP : ∀ d ∈ P, d < 3) (j : Nat) (hj : j < P.length) :
    digit3 (patVal P) j = P[j]'hj := by
  revert hP
  revert hj
  revert j
  induction P with
  | nil => intro j hj hP; exact absurd hj (Nat.not_lt_zero j)
  | cons d rest ih =>
      intro j hj hP
      have hmem : ∀ e ∈ rest, e < 3 := fun e he => hP e (List.mem_cons.mpr (Or.inr he))
      have hd3 : d < 3 := hP d (List.mem_cons.mpr (Or.inl rfl))
      have hV : patVal (d :: rest) = d + 3 * patVal rest := rfl
      have hlen : (d :: rest).length = rest.length + 1 := rfl
      rcases j with _ | k
      · show digit3 (patVal (d :: rest)) 0 = d
        rw [hV]
        show (d + 3 * patVal rest) / 3 ^ 0 % 3 = d
        rw [Nat.pow_zero, Nat.div_one, Nat.add_mod d (3 * patVal rest) 3,
            Nat.mul_mod_right 3 (patVal rest)]
        omega
      · have hk : k < rest.length := by rw [hlen] at hj; omega
        show digit3 (patVal (d :: rest)) (k + 1) = rest[k]'hk
        rw [hV]
        show (d + 3 * patVal rest) / 3 ^ (k + 1) % 3 = rest[k]'hk
        have hmod : patVal rest % 3 ^ k < 3 ^ k := Nat.mod_lt _ (three_pow_pos k)
        have hbound2 : d + 3 * (patVal rest % 3 ^ k) < 3 ^ (k + 1) := by
          have hM : 3 ^ (k + 1) = 3 * 3 ^ k := Nat.pow_succ'
          omega
        have hVd := Nat.div_add_mod (patVal rest) (3 ^ k)
        have hM3 : 3 ^ (k + 1) * (patVal rest / 3 ^ k)
            = 3 * (3 ^ k * (patVal rest / 3 ^ k)) := by
          have hM : 3 ^ (k + 1) = 3 * 3 ^ k := Nat.pow_succ'
          rw [hM, Nat.mul_assoc]
        have hsplit : d + 3 * patVal rest
            = 3 ^ (k + 1) * (patVal rest / 3 ^ k) + (d + 3 * (patVal rest % 3 ^ k)) := by
          omega
        have hcar : (d + 3 * patVal rest) / 3 ^ (k + 1) = patVal rest / 3 ^ k := by
          have step1 : (d + 3 * patVal rest) / 3 ^ (k + 1)
              = (3 ^ (k + 1) * (patVal rest / 3 ^ k) + (d + 3 * (patVal rest % 3 ^ k)))
                / 3 ^ (k + 1) := by
            rw [hsplit]
          have step2 : (3 ^ (k + 1) * (patVal rest / 3 ^ k)
                + (d + 3 * (patVal rest % 3 ^ k))) / 3 ^ (k + 1)
              = (d + 3 * (patVal rest % 3 ^ k)) / 3 ^ (k + 1) + patVal rest / 3 ^ k := by
            rw [Nat.add_comm, Nat.add_mul_div_left (d + 3 * (patVal rest % 3 ^ k))
              (patVal rest / 3 ^ k) (three_pow_pos (k + 1))]
          have step3 : (d + 3 * (patVal rest % 3 ^ k)) / 3 ^ (k + 1) = 0 :=
            Nat.div_eq_of_lt hbound2
          rw [step1, step2, step3]
          exact Nat.zero_add _
        rw [hcar]
        have hih := ih k hk hmem
        have hdig : digit3 (patVal rest) k = patVal rest / 3 ^ k % 3 := rfl
        rw [← hdig, hih]

/-- Equal residues mod 3^(pos+len) transfer the whole pattern. -/
theorem patternOfResidue (N N' pos : Nat) (P : List Nat)
    (h : N % 3 ^ (pos + P.length) = N' % 3 ^ (pos + P.length)) :
    patternAt N' pos P → patternAt N pos P := by
  intro h0 j hj
  have hjl : pos + (j + 1) ≤ pos + P.length := by omega
  have hdvd := three_pow_le_mono (pos + (j + 1)) (pos + P.length) hjl
  have h1 : N % 3 ^ (pos + P.length) % 3 ^ (pos + (j + 1)) = N % 3 ^ (pos + (j + 1)) :=
    Nat.mod_mod_of_dvd N hdvd
  have h2 : N' % 3 ^ (pos + P.length) % 3 ^ (pos + (j + 1)) = N' % 3 ^ (pos + (j + 1)) :=
    Nat.mod_mod_of_dvd N' hdvd
  have h3 : N % 3 ^ (pos + (j + 1)) = N' % 3 ^ (pos + (j + 1)) := by
    rw [← h1, ← h2, h]
  have hshift := digit3_residue N N' (pos + j) (pos + (j + 1)) (by omega) h3
  rw [hshift, h0 j hj]

/-- Terminal placement: every word whose lowest digit is nonzero (equivalently,
    whose value is a unit mod 3) terminates some power of 2. -/
theorem pattern_terminal (P : List Nat) (hP : ∀ d ∈ P, d < 3) (hu : ¬ 3 ∣ patVal P) :
    ∃ n, patternAt (2 ^ n) 0 P := by
  cases P with
  | nil =>
    have hd0 : 3 ∣ patVal ([] : List Nat) := ⟨0, rfl⟩
    exact absurd hd0 hu
  | cons d rest =>
    have hlen : (d :: rest).length = rest.length + 1 := rfl
    have hlt : patVal (d :: rest) < 3 ^ (d :: rest).length := patVal_lt _ hP
    obtain ⟨n, hn⟩ := powers_hit_all_units ((d :: rest).length) (by rw [hlen]; omega)
      (patVal (d :: rest)) hu
    have hres : 2 ^ n % 3 ^ (d :: rest).length = patVal (d :: rest) := by
      rw [hn, Nat.mod_eq_of_lt hlt]
    refine ⟨n, ?_⟩
    intro j hj
    have hjl : j + 1 ≤ (d :: rest).length := by omega
    have hdvd := three_pow_le_mono (j + 1) ((d :: rest).length) hjl
    have hm1 : 2 ^ n % 3 ^ (d :: rest).length % 3 ^ (j + 1) = 2 ^ n % 3 ^ (j + 1) :=
      Nat.mod_mod_of_dvd (2 ^ n) hdvd
    have hres2 : 2 ^ n % 3 ^ (j + 1) = patVal (d :: rest) % 3 ^ (j + 1) := by
      rw [← hm1, hres]
    rw [show (0 : Nat) + j = j from Nat.zero_add j, digit3_eq (2 ^ n) j, hres2,
        ← digit3_eq (patVal (d :: rest)) j, digit3_patVal (d :: rest) hP j hj]

/-- Interior placement: every word occurs at every prescribed position k ≥ 1. -/
theorem pattern_interior (P : List Nat) (hP : ∀ d ∈ P, d < 3) (k : Nat) (hk : 1 ≤ k) :
    ∃ n, patternAt (2 ^ n) k P := by
  have hpowkl : 3 ^ (k + P.length) = 3 ^ k * 3 ^ P.length := Nat.pow_add 3 k P.length
  have hV : patVal P < 3 ^ P.length := patVal_lt P hP
  have hk3 : 1 < 3 ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · exact absurd hk (by omega)
    · have := three_pow_ge_three k hk'
      omega
  have hA2 : 3 ^ k * patVal P + 3 ^ k = 3 ^ k * (patVal P + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hB2 : 3 ^ k * (patVal P + 1) ≤ 3 ^ k * 3 ^ P.length :=
    Nat.mul_le_mul_left _ (by omega)
  have hbound : 3 ^ k * patVal P + 1 < 3 ^ (k + P.length) := by
    rw [hpowkl]
    omega
  have hunit : ¬ 3 ∣ (3 ^ k * patVal P + 1) := by
    have hk1 : 3 ^ k = 3 * 3 ^ (k - 1) := by
      have e : (k - 1) + 1 = k := by omega
      have e2 : 3 ^ k = 3 ^ ((k - 1) + 1) := by rw [e]
      rw [e2, Nat.pow_succ']
    have hprod0 : (3 ^ k * patVal P) % 3 = 0 := by
      rw [hk1, Nat.mul_assoc]
      exact Nat.mul_mod_right 3 (3 ^ (k - 1) * patVal P)
    intro hd
    have hz : (3 ^ k * patVal P + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    have hone : (3 ^ k * patVal P + 1) % 3 = 1 := by
      rw [Nat.add_mod (3 ^ k * patVal P) 1 3, hprod0]
    omega
  obtain ⟨n, hn⟩ := powers_hit_all_units (k + P.length) (by omega)
    (3 ^ k * patVal P + 1) hunit
  have hres' : 2 ^ n % 3 ^ (k + P.length) = 3 ^ k * patVal P + 1 := by
    rw [hn, Nat.mod_eq_of_lt hbound]
  have hq := Nat.div_add_mod (2 ^ n) (3 ^ (k + P.length))
  rw [hres'] at hq
  have hsplit : 2 ^ n / 3 ^ k
      = 3 ^ P.length * (2 ^ n / 3 ^ (k + P.length)) + patVal P := by
    have hA : 2 ^ n
        = 3 ^ k * (3 ^ P.length * (2 ^ n / 3 ^ (k + P.length)) + patVal P) + 1 := by
      have h1 : 3 ^ k * (3 ^ P.length * (2 ^ n / 3 ^ (k + P.length)))
          = 3 ^ (k + P.length) * (2 ^ n / 3 ^ (k + P.length)) := by
        rw [← Nat.mul_assoc, Nat.pow_add]
      rw [Nat.mul_add, h1, Nat.add_assoc, hq]
    exact div_uniq (2 ^ n) (3 ^ k)
      (3 ^ P.length * (2 ^ n / 3 ^ (k + P.length)) + patVal P) 1 (three_pow_pos k)
      (by have h1 := three_pow_ge_three k hk; omega)
      (by rw [Nat.mul_comm]; exact hA)
  have hres2 : (2 ^ n / 3 ^ k) % 3 ^ P.length = patVal P % 3 ^ P.length := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hV]
  refine ⟨n, ?_⟩
  intro j hj
  have hjl : j + 1 ≤ P.length := by omega
  have hdig := digit3_residue (2 ^ n / 3 ^ k) (patVal P) j P.length hjl hres2
  rw [digit3_shift (2 ^ n) k j, hdig, digit3_patVal P hP j hj]

/-=============================================================================
  §7. THE PERIOD LAW AND THE HEADLINE THEOREMS
=============================================================================-/

/-- THE PERIOD LAW: 2^(2*3^(M-1)) ≡ 1 (mod 3^M) for every M ≥ 1. -/
theorem period_law (M : Nat) (hM : 1 ≤ M) : 2 ^ (2 * 3 ^ (M - 1)) % 3 ^ M = 1 := by
  have hpow : 2 ^ (2 * 3 ^ (M - 1)) = 4 ^ (3 ^ (M - 1)) := by
    rw [Nat.pow_mul]
  obtain ⟨hw1, _⟩ := W_val (M - 1)
  have hshift : (M - 1) + 1 = M := by omega
  rw [hshift] at hw1
  rw [hpow, hw1, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := three_pow_ge_three M hM; omega)

/-- One hit plus the period law: the pattern re-appears at n0 + t*D. -/
theorem pattern_repeat_aux (P : List Nat) (k n0 D : Nat)
    (hD : 2 ^ D % 3 ^ (k + P.length) = 1) (h0 : patternAt (2 ^ n0) k P) (t : Nat) :
    patternAt (2 ^ (n0 + t * D)) k P := by
  have hpowadd : 2 ^ (n0 + t * D) = 2 ^ n0 * (2 ^ D) ^ t := by
    rw [Nat.pow_add, Nat.mul_comm t D, Nat.pow_mul]
  have h1m : 1 % 3 ^ (k + P.length) = 1 :=
    Nat.mod_eq_of_lt (by have := three_pow_pos (k + P.length); omega)
  have hDt : (2 ^ D) ^ t % 3 ^ (k + P.length) = 1 := by
    rw [Nat.pow_mod, hD, Nat.one_pow]
    exact h1m
  have hres : 2 ^ (n0 + t * D) % 3 ^ (k + P.length) = 2 ^ n0 % 3 ^ (k + P.length) := by
    obtain ⟨U, hU⟩ : ∃ U, (2 ^ D) ^ t = 1 + 3 ^ (k + P.length) * U :=
      ⟨(2 ^ D) ^ t / 3 ^ (k + P.length), by
        have h1 := Nat.div_add_mod ((2 ^ D) ^ t) (3 ^ (k + P.length))
        rw [hDt] at h1
        omega⟩
    have h2 : 2 ^ (n0 + t * D) = 2 ^ n0 + 3 ^ (k + P.length) * (2 ^ n0 * U) := by
      rw [hpowadd, hU, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
          Nat.mul_comm (2 ^ n0) (3 ^ (k + P.length)), Nat.mul_assoc]
    rw [h2, Nat.add_mul_mod_self_left]
  exact patternOfResidue (2 ^ (n0 + t * D)) (2 ^ n0) k P hres h0

/-- THE HEADLINE: one occurrence at exponent n0 gives occurrences at
    arbitrarily large exponents. -/
theorem pattern_repeat (P : List Nat) (k n0 : Nat) (h0 : patternAt (2 ^ n0) k P)
    (N0 : Nat) : ∃ n, N0 ≤ n ∧ patternAt (2 ^ n) k P := by
  rcases Nat.eq_zero_or_pos (k + P.length) with hM0 | hMpos
  · refine ⟨N0, Nat.le_refl N0, ?_⟩
    have hPl0 : P.length = 0 := by omega
    intro j hj
    omega
  · have hD := period_law (k + P.length) hMpos
    refine ⟨n0 + ((N0 + 2 * 3 ^ (k + P.length - 1)) / (2 * 3 ^ (k + P.length - 1)))
      * (2 * 3 ^ (k + P.length - 1)), ?_,
      pattern_repeat_aux P k n0 (2 * 3 ^ (k + P.length - 1)) hD h0
        ((N0 + 2 * 3 ^ (k + P.length - 1)) / (2 * 3 ^ (k + P.length - 1)))⟩
    have hdm := Nat.div_add_mod (N0 + 2 * 3 ^ (k + P.length - 1))
      (2 * 3 ^ (k + P.length - 1))
    have hcomm : (N0 + 2 * 3 ^ (k + P.length - 1)) / (2 * 3 ^ (k + P.length - 1))
        * (2 * 3 ^ (k + P.length - 1))
        + (N0 + 2 * 3 ^ (k + P.length - 1)) % (2 * 3 ^ (k + P.length - 1))
        = N0 + 2 * 3 ^ (k + P.length - 1) := by
      rw [Nat.mul_comm]; exact hdm
    have hR : (N0 + 2 * 3 ^ (k + P.length - 1)) % (2 * 3 ^ (k + P.length - 1))
        < 2 * 3 ^ (k + P.length - 1) :=
      Nat.mod_lt _ (by have := three_pow_pos (k + P.length - 1); omega)
    omega

/-- THE PATTERN FRONTIER OF ERDŐS #406 (interior form, machine-verified):
    every finite ternary word occurs at every prescribed interior position
    k ≥ 1 of powers of 2, at arbitrarily large exponents. -/
theorem erdos406_frontier_interior (P : List Nat) (hP : ∀ d ∈ P, d < 3)
    (k N0 : Nat) (hk : 1 ≤ k) : ∃ n, N0 ≤ n ∧ patternAt (2 ^ n) k P := by
  obtain ⟨n0, h0⟩ := pattern_interior P hP k hk
  exact pattern_repeat P k n0 h0 N0

/-- THE PATTERN FRONTIER OF ERDŐS #406 (terminal form, machine-verified):
    every finite ternary word whose value is a unit mod 3 occurs as the
    terminal digit block of 2^n for arbitrarily large n. -/
theorem erdos406_frontier_terminal (P : List Nat) (hP : ∀ d ∈ P, d < 3)
    (hu : ¬ 3 ∣ patVal P) (N0 : Nat) : ∃ n, N0 ≤ n ∧ patternAt (2 ^ n) 0 P := by
  obtain ⟨n0, h0⟩ := pattern_terminal P hP hu
  exact pattern_repeat P 0 n0 h0 N0

/-- Corollary: arbitrarily long runs of any fixed digit v < 3 occur at any
    interior position, at arbitrarily large exponents. -/
theorem runs_of_digit (v L k N0 : Nat) (hv : v < 3) (hk : 1 ≤ k) :
    ∃ n, N0 ≤ n ∧ ∀ j, j < L → digit3 (2 ^ n) (k + j) = v := by
  have hmem : ∀ d ∈ List.replicate L v, d < 3 := by
    intro d hd
    rcases List.mem_replicate.mp hd with ⟨_, hdv⟩
    omega
  obtain ⟨n, hn0, hpat⟩ := erdos406_frontier_interior (List.replicate L v) hmem k N0 hk
  refine ⟨n, hn0, fun j hj => ?_⟩
  have hlen : (List.replicate L v).length = L := List.length_replicate
  have hj2 : j < (List.replicate L v).length := by rw [hlen]; omega
  rw [hpat j hj2, List.getElem_replicate hj2]

end GSTPatternLift

-- AXIOM CERTIFICATE: every headline theorem below must print
-- "does not depend on any axioms".
#print axioms GSTPatternLift.lte_exact
#print axioms GSTPatternLift.W_val
#print axioms GSTPatternLift.powers_hit_all_units
#print axioms GSTPatternLift.period_law
#print axioms GSTPatternLift.pattern_terminal
#print axioms GSTPatternLift.pattern_interior
#print axioms GSTPatternLift.pattern_repeat
#print axioms GSTPatternLift.erdos406_frontier_interior
#print axioms GSTPatternLift.erdos406_frontier_terminal
#print axioms GSTPatternLift.runs_of_digit
