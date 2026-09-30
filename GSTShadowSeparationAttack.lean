import GSTShadowGap
import GSTShadowGapReceipt

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE SHADOW SEPARATION ATTACK — the clean-word equation, the bottom-half law,
# the factorization, and the killed classes

The separation — no exponent `m ≥ 5` is eternally shadowed — is one of the two
named finish lines of the campaign (the other is the tail climb), and by
`GSTShadowGapReceipt.THE_REMAINING_CONTENT` it is *equivalent* to the
comparator's unconditional stamp.  By the Shadow Gap's exact count
(`shadow_count_exact`), at every level `L` exactly `2^L` classes survive the
window `L+1` and every surviving class is lived in — so no window, level, or
residue computation can ever prove the separation.  A global argument is
mandatory.  This file builds the global infrastructure for that argument and
drives the attack as far as it honestly goes:

* **THE CLEAN-WORD REDUCTION** (`eternally_shadowed_iff_clean_quotient`): an
  exponent `m` is eternally shadowed exactly when the quotient word
  `z = (4^m − 1)/3` — the geometric sum `1 + 4 + ⋯ + 4^{m−1}` (binary
  `1010…101`), factored as the coprime pair `A·B` on the line `|3A − B| = 2` —
  has all ternary digits in `{0, 1}`.  This is the canonical **clean-word
  equation** form of the remaining content, wired directly into the crown.

* **THE BOTTOM-HALF LAW** (`eternally_shadowed_iff_bottom_half`): an exponent
  is eternally shadowed exactly when **every window of `4^m` lands in the
  bottom half** — `4^m % 3^k ≤ (3^k − 1)/2` for every scale `k`.  The
  separation becomes: for every `m ≥ 5` some window escapes the bottom half.
  Two one-line escape certificates follow: a single dirty digit
  (`separated_of_dirty_digit`), and a leading ternary digit two
  (`separated_of_leading_digit_two`).

* **THE FACTORIZATION** (`cleanQuot_factor_even/odd`, `factor_line_even/odd`,
  `factor_coprime_even/odd`): the clean-word equation factors as `z = A·B`
  with `A = (2^m ∓ 1)/3`, `B = 2^m ± 1` — a coprime pair on the line
  `|3A − B| = 2`.  (Honest reach: the factorization exhibits the arithmetic
  of the equation but yields no digit obstruction — see the remark closing
  Section 3.)

* **THE KILLED CLASSES** (`killed_class_early_digit_two`,
  `separation_level_five`, `survivor_table5_receipt`): for every level `L`,
  every exponent class **outside** the `2^L` surviving classes owns a ternary
  digit two within the first `L+1` rows — one infinite arithmetic family of
  separated exponents per killed class.  At level five the kernel decides the
  full table: exactly `32` of the `243` classes mod `243` survive the
  six-row window; the other **`211` classes are separated with a digit two
  below row six, uniformly for every exponent in the class**.  This is the
  exact reach of the window method — and by the doubling law it is also its
  permanent ceiling: the `32` surviving classes are lived in forever.
-/

namespace GSTShadowSeparationAttack

open GSTShadowGap
open GSTShadowGapReceipt
open GSTFourPowerDirectResidue

/-! ## Section 0 — the quotient word -/

/-- The quotient word of an exponent: `z = (4^m − 1)/3`. -/
def cleanQuot (m : Nat) : Nat := (4^m - 1) / 3

/-- Every power of four splits as one plus three times its quotient word. -/
theorem pow4_eq_succ_three_mul_cleanQuot (m : Nat) :
    4^m = 3 * cleanQuot m + 1 := by
  have h1 : 4^m % 3 = 1 := pow4_mod3_one m
  have h2 : 4^m - 1 = 3 * ((4^m - 1) / 3) + (4^m - 1) % 3 :=
    (Nat.div_add_mod (4^m - 1) 3).symm
  have hE : 4^m % 3 + 3 * (4^m / 3) = 4^m := Nat.mod_add_div (4^m) 3
  rw [h1] at hE
  have hz : (4^m - 1) % 3 = 0 := by omega
  rw [hz, Nat.add_zero] at h2
  unfold cleanQuot
  omega

/-- Row `q + 1` of `4^m` is row `q` of the quotient word. -/
theorem digit3_pow4_succ (m q : Nat) :
    digit3 (4^m) (q + 1) = digit3 (cleanQuot m) q := by
  have h := digit3_shift (cleanQuot m) 1 q (by norm_num)
  rw [← pow4_eq_succ_three_mul_cleanQuot m] at h
  exact h

/-- Row zero of every power of four is one. -/
theorem digit3_pow4_zero (m : Nat) : digit3 (4^m) 0 = 1 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, pow4_mod3_one]

/-! ## Section 1 — the clean-word reduction -/

/-- **THE CLEAN-WORD REDUCTION.**  An exponent is eternally shadowed exactly
when its quotient word `z = (4^m − 1)/3` is a clean word: all ternary digits
in `{0, 1}`.  The separation is the statement that no `m ≥ 5` solves the
clean-word equation. -/
theorem eternally_shadowed_iff_clean_quotient (m : Nat) :
    EternallyShadowed m ↔ (∀ q : Nat, digit3 (cleanQuot m) q ≠ 2) := by
  rw [eternally_shadowed_iff_no_digit_two]
  constructor
  · intro h q
    have hq := h (q + 1)
    rwa [digit3_pow4_succ] at hq
  · intro h p
    cases p with
    | zero =>
        rw [digit3_pow4_zero]
        decide
    | succ q =>
        have hq := h q
        rwa [← digit3_pow4_succ] at hq

/-- **THE SEPARATION, CANONICALIZED.**  The remaining content is the
statement that every exponent `m ≥ 5` owns a dirty row in its quotient word. -/
theorem separation_iff_clean_word_equation :
    (∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) ↔
    (∀ m : Nat, 5 ≤ m → ∃ q : Nat, digit3 (cleanQuot m) q = 2) := by
  constructor
  · intro h m hm
    by_contra hc
    exact h m hm ((eternally_shadowed_iff_clean_quotient m).mpr
      (not_exists.mp hc))
  · intro h m hm hsh
    obtain ⟨q, hq⟩ := h m hm
    exact (eternally_shadowed_iff_clean_quotient m).mp hsh q hq

/-- The clean-word equation, wired into the crown: solving it for all `m ≥ 5`
delivers the comparator's unconditional stamp. -/
theorem crown_of_clean_word_equation
    (h : ∀ m : Nat, 5 ≤ m → ∃ q : Nat, digit3 (cleanQuot m) q = 2) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  THE_REMAINING_CONTENT.mpr (separation_iff_clean_word_equation.mpr h)

/-- The quotient word as a geometric sum: `1 + 4 + ⋯ + 4^{m−1}` — in binary
the alternating word `1010…101` with `m` ones. -/
def geomSum : Nat → Nat
  | 0 => 0
  | m + 1 => geomSum m + 4^m

theorem pow4_eq_succ_three_mul_geomSum (m : Nat) :
    4^m = 3 * geomSum m + 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
      show 4^(m+1) = 3 * (geomSum m + 4^m) + 1
      rw [Nat.pow_succ]
      omega

theorem cleanQuot_eq_geomSum (m : Nat) : cleanQuot m = geomSum m := by
  have h1 := pow4_eq_succ_three_mul_cleanQuot m
  have h2 := pow4_eq_succ_three_mul_geomSum m
  omega

/-! ## Section 2 — the bottom-half law -/

private theorem three_pow_succ_mul' (k : Nat) : 3^(k+1) = 3 * 3^k := by
  rw [Nat.mul_comm]
  exact Nat.pow_succ 3 k

private theorem three_pow_odd (k : Nat) : 3^k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [three_pow_succ_mul', Nat.mul_mod, ih]

private theorem three_pow_half (k : Nat) :
    2 * ((3^k - 1) / 2) = 3^k - 1 := by
  have hmod : (3^k - 1) % 2 = 0 := by
    have hp := Nat.div_add_mod (3^k) 2
    have hodd := three_pow_odd k
    omega
  have hd := Nat.div_add_mod (3^k - 1) 2
  omega

/-- The window split: the window at scale `k+1` is the window at scale `k`
plus `3^k` times row `k`. -/
theorem mod_pow_split (n k : Nat) :
    n % 3^(k+1) = n % 3^k + 3^k * digit3 n k := by
  have h1 : (n / 3^k) / 3 = n / 3^(k+1) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← three_pow_succ_mul']
  have h2 : n / 3^k = 3 * (n / 3^(k+1)) + (n / 3^k) % 3 := by
    have hdm := Nat.div_add_mod (n / 3^k) 3
    rw [h1] at hdm
    exact hdm.symm
  have h3 : 3^k * (n / 3^k) + n % 3^k = n :=
    Nat.div_add_mod n (3^k)
  have h4 : 3^(k+1) * (n / 3^(k+1)) + n % 3^(k+1) = n :=
    Nat.div_add_mod n (3^(k+1))
  have hsplit2 : 3^k * (n / 3^k)
      = 3^k * (3 * (n / 3^(k+1))) + 3^k * ((n / 3^k) % 3) := by
    conv_lhs => rw [h2]
    rw [Nat.mul_add]
  have hassoc : 3^k * (3 * (n / 3^(k+1)))
      = 3^(k+1) * (n / 3^(k+1)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (3^k) (3:Nat), ← three_pow_succ_mul']
  rw [hsplit2, hassoc] at h3
  have hd : digit3 n k = (n / 3^k) % 3 := rfl
  rw [hd]
  omega

theorem digit3_lt_three (n p : Nat) : digit3 n p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (by norm_num)

/-- A clean window lies in the bottom half: if all rows below `k` avoid the
digit two, the window value is at most `(3^k − 1)/2`. -/
theorem clean_window_bottom_half (n k : Nat)
    (hclean : ∀ p : Nat, p < k → digit3 n p ≠ 2) :
    n % 3^k ≤ (3^k - 1) / 2 := by
  induction k with
  | zero =>
      rw [Nat.pow_zero]
      omega
  | succ k ih =>
      have ih' := ih (fun p hp => hclean p (by omega))
      have hd : digit3 n k ≤ 1 := by
        have hne := hclean k (by omega)
        have hlt := digit3_lt_three n k
        omega
      have hsplit := mod_pow_split n k
      have hC := three_pow_half k
      have hD := three_pow_half (k+1)
      have hE := three_pow_succ_mul' k
      rcases Nat.lt_or_ge (digit3 n k) 1 with hlt1 | hge1
      · have hd0 : digit3 n k = 0 := by omega
        have hz : 3^k * digit3 n k = 0 := by rw [hd0]; norm_num
        omega
      · have hd1 : digit3 n k = 1 := by omega
        have ho : 3^k * digit3 n k = 3^k := by rw [hd1]; norm_num
        omega

/-- A dirty row forces its window to escape the bottom half. -/
theorem dirty_digit_top_escape (n p : Nat) (hdirty : digit3 n p = 2) :
    (3^(p+1) - 1) / 2 < n % 3^(p+1) := by
  have hsplit := mod_pow_split n p
  rw [hdirty] at hsplit
  have hC := three_pow_half (p+1)
  have hE := three_pow_succ_mul' p
  omega

/-- **THE BOTTOM-HALF LAW.**  An exponent is eternally shadowed exactly when
every window of its power lands in the bottom half: `4^m % 3^k ≤ (3^k − 1)/2`
for every scale `k`.  The separation is the escape statement: for every
`m ≥ 5` some window escapes. -/
theorem eternally_shadowed_iff_bottom_half (m : Nat) :
    EternallyShadowed m ↔
    (∀ k : Nat, 4^m % 3^k ≤ (3^k - 1) / 2) := by
  constructor
  · intro hsh
    have hdigits := (eternally_shadowed_iff_no_digit_two m).mp hsh
    exact fun k => clean_window_bottom_half (4^m) k
      (fun p _ => hdigits p)
  · intro hbottom
    refine (eternally_shadowed_iff_no_digit_two m).mpr ?_
    intro p hpdirty
    have hesc := dirty_digit_top_escape (4^m) p hpdirty
    have hbot := hbottom (p+1)
    omega

/-- **ESCAPE CERTIFICATE 1 — a single dirty digit.**  Any exponent whose
power has a ternary digit two is separated. -/
theorem separated_of_dirty_digit (m p : Nat) (hdirty : digit3 (4^m) p = 2) :
    ¬ EternallyShadowed m := by
  intro hsh
  have hesc := dirty_digit_top_escape (4^m) p hdirty
  have hbot := (eternally_shadowed_iff_bottom_half m).mp hsh (p+1)
  omega

/-- **ESCAPE CERTIFICATE 2 — a leading ternary digit two.**  If the leading
ternary digit of `4^m` is two (the top window sits above the half line), the
exponent is separated — a global condition on the whole expansion. -/
theorem separated_of_leading_digit_two (m ℓ : Nat)
    (hhi : 4^m < 3^(ℓ+1)) (hlead : 2 * 3^ℓ ≤ 4^m) :
    ¬ EternallyShadowed m := by
  intro hsh
  have hbot := (eternally_shadowed_iff_bottom_half m).mp hsh (ℓ+1)
  have hmod : 4^m % 3^(ℓ+1) = 4^m := Nat.mod_eq_of_lt hhi
  have hC := three_pow_half (ℓ+1)
  have hE := three_pow_succ_mul' ℓ
  omega

/-! ## Section 3 — the factorization of the clean-word equation -/

private theorem div_mul_of_dvd (a b : Nat) (h : 3 ∣ a) :
    (a * b) / 3 = (a / 3) * b := by
  obtain ⟨c, hc⟩ := h
  subst hc
  have h1 : (3 * c) / 3 = c :=
    Nat.mul_div_cancel_left _ (by decide : 0 < 3)
  have h2 : (3 * c) * b = 3 * (c * b) := Nat.mul_assoc 3 c b
  have h3 : (3 * (c * b)) / 3 = c * b :=
    Nat.mul_div_cancel_left _ (by decide : 0 < 3)
  rw [h1, h2, h3]

private theorem mul_div_of_dvd (a b : Nat) (h : 3 ∣ b) :
    (a * b) / 3 = a * (b / 3) := by
  obtain ⟨c, hc⟩ := h
  subst hc
  have h1 : (3 * c) / 3 = c :=
    Nat.mul_div_cancel_left _ (by decide : 0 < 3)
  have h2 : a * (3 * c) = 3 * (a * c) := by ring
  have h3 : (3 * (a * c)) / 3 = a * c :=
    Nat.mul_div_cancel_left _ (by decide : 0 < 3)
  rw [h1, h2, h3]

theorem four_pow_eq_two_pow_sq (m : Nat) : 4^m = 2^m * 2^m := by
  rw [show (4:Nat) = 2^2 from by decide, ← Nat.pow_mul,
    Nat.mul_comm 2 m, Nat.pow_mul, Nat.pow_two]

private theorem two_pow_mod3_even (m : Nat) (hme : m % 2 = 0) :
    2^m % 3 = 1 := by
  have hm : m = 2 * (m / 2) := by omega
  rw [hm, Nat.pow_mul, show (2:Nat)^2 = 4 from by decide]
  exact pow4_mod3_one _

private theorem two_pow_mod3_odd (m : Nat) (hmo : m % 2 = 1) :
    2^m % 3 = 2 := by
  have hm : m = 2 * (m / 2) + 1 := by omega
  rw [hm, Nat.pow_add, Nat.pow_mul, show (2:Nat)^2 = 4 from by decide]
  rw [Nat.mul_mod, pow4_mod3_one]

/-- **THE FACTORIZATION, EVEN ROW.**  For even `m` the quotient word is the
product of the pair `A = (2^m − 1)/3`, `B = 2^m + 1`. -/
theorem cleanQuot_factor_even (m : Nat) (hme : m % 2 = 0) :
    cleanQuot m = ((2^m - 1) / 3) * (2^m + 1) := by
  have h1 := two_pow_mod3_even m hme
  have h2 : 2^m = 3 * (2^m / 3) + 2^m % 3 := (Nat.div_add_mod (2^m) 3).symm
  rw [h1] at h2
  have hdvd : 3 ∣ 2^m - 1 := by
    refine ⟨(2^m - 1) / 3, ?_⟩
    omega
  have h2m : 0 < 2^m := Nat.pow_pos (by decide)
  have hsq : 4^m - 1 = (2^m - 1) * (2^m + 1) := by
    obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero h2m.ne'
    rw [four_pow_eq_two_pow_sq, hy]
    have hring : (y + 1) * (y + 1) = y * (y + 2) + 1 := by ring
    have hs1 : y + 1 - 1 = y := by omega
    have hs2 : y + 1 + 1 = y + 2 := by omega
    rw [hs1, hs2]
    have hP : 0 < (y + 1) * (y + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  unfold cleanQuot
  rw [hsq, div_mul_of_dvd _ _ hdvd]

/-- **THE FACTORIZATION, ODD ROW.**  For odd `m` the quotient word is the
product of the pair `A = (2^m + 1)/3`, `B = 2^m − 1`. -/
theorem cleanQuot_factor_odd (m : Nat) (hmo : m % 2 = 1) :
    cleanQuot m = ((2^m + 1) / 3) * (2^m - 1) := by
  have h1 := two_pow_mod3_odd m hmo
  have h2 : 2^m = 3 * (2^m / 3) + 2^m % 3 := (Nat.div_add_mod (2^m) 3).symm
  rw [h1] at h2
  have hdvd : 3 ∣ 2^m + 1 := by
    refine ⟨(2^m + 1) / 3, ?_⟩
    omega
  have h2m : 0 < 2^m := Nat.pow_pos (by decide)
  have hsq : 4^m - 1 = (2^m - 1) * (2^m + 1) := by
    obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero h2m.ne'
    rw [four_pow_eq_two_pow_sq, hy]
    have hring : (y + 1) * (y + 1) = y * (y + 2) + 1 := by ring
    have hs1 : y + 1 - 1 = y := by omega
    have hs2 : y + 1 + 1 = y + 2 := by omega
    rw [hs1, hs2]
    have hP : 0 < (y + 1) * (y + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  unfold cleanQuot
  rw [hsq, mul_div_of_dvd _ _ hdvd]
  exact Nat.mul_comm _ _

/-- **THE LINE LAW, EVEN ROW.**  The even-row factor pair sits on the line
`B − 3A = 2`. -/
theorem factor_line_even (m : Nat) (hme : m % 2 = 0) :
    (2^m + 1) - 3 * ((2^m - 1) / 3) = 2 := by
  have h1 := two_pow_mod3_even m hme
  have h2 : 2^m = 3 * (2^m / 3) + 2^m % 3 := (Nat.div_add_mod (2^m) 3).symm
  rw [h1] at h2
  have hq : (2^m - 1) / 3 = 2^m / 3 := by omega
  rw [hq]
  omega

/-- **THE LINE LAW, ODD ROW.**  The odd-row factor pair sits on the line
`3A − B = 2`. -/
theorem factor_line_odd (m : Nat) (hmo : m % 2 = 1) :
    3 * ((2^m + 1) / 3) - (2^m - 1) = 2 := by
  have h1 := two_pow_mod3_odd m hmo
  have h2 : 2^m = 3 * (2^m / 3) + 2^m % 3 := (Nat.div_add_mod (2^m) 3).symm
  rw [h1] at h2
  have hq : (2^m + 1) / 3 = 2^m / 3 + 1 := by omega
  rw [hq]
  omega

/-- **COPRIMALITY, EVEN ROW.**  The even-row factors are coprime: any common
divisor divides the line value `2` and the odd factor `2^m + 1`. -/
theorem factor_coprime_even (m : Nat) (hm1 : 1 ≤ m) (hme : m % 2 = 0) :
    Nat.gcd ((2^m - 1) / 3) (2^m + 1) = 1 := by
  have hline := factor_line_even m hme
  have hdA : Nat.gcd ((2^m - 1) / 3) (2^m + 1) ∣ (2^m - 1) / 3 :=
    Nat.gcd_dvd_left _ _
  have hdB : Nat.gcd ((2^m - 1) / 3) (2^m + 1) ∣ 2^m + 1 :=
    Nat.gcd_dvd_right _ _
  have hd3A : Nat.gcd ((2^m - 1) / 3) (2^m + 1) ∣ 3 * ((2^m - 1) / 3) := by
    have key : ∀ g : Nat, g ∣ (2^m - 1) / 3 →
        g ∣ 3 * ((2^m - 1) / 3) := by
      intro g hg
      obtain ⟨k, hk⟩ := hg
      refine ⟨3 * k, ?_⟩
      rw [hk]
      ring
    exact key _ hdA
  have hdsub : Nat.gcd ((2^m - 1) / 3) (2^m + 1) ∣ 2 := by
    obtain ⟨u, hu⟩ := hdB
    obtain ⟨v, hv⟩ := hd3A
    have huv : u = v + (u - v) := by omega
    rw [huv] at hu
    have hexpand : Nat.gcd ((2^m - 1) / 3) (2^m + 1) * (v + (u - v))
        = Nat.gcd ((2^m - 1) / 3) (2^m + 1) * v
          + Nat.gcd ((2^m - 1) / 3) (2^m + 1) * (u - v) :=
      Nat.mul_add _ _ _
    rw [hexpand] at hu
    rw [← hv] at hu
    have hw : Nat.gcd ((2^m - 1) / 3) (2^m + 1) * (u - v) = 2 := by omega
    exact ⟨u - v, hw.symm⟩
  have hBodd : (2^m + 1) % 2 = 1 := by
    have h2m : 2^m = 2^(m - 1) * 2 := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      exact Nat.pow_succ 2 (m - 1)
    omega
  have hge : 1 ≤ Nat.gcd ((2^m - 1) / 3) (2^m + 1) := by
    by_cases hg0 : Nat.gcd ((2^m - 1) / 3) (2^m + 1) = 0
    · obtain ⟨k, hk⟩ := hdB
      rw [hg0] at hk
      have h2m : 0 < 2^m := Nat.pow_pos (by decide)
      omega
    · omega
  have hgle : Nat.gcd ((2^m - 1) / 3) (2^m + 1) ≤ 2 := by
    obtain ⟨c, hc⟩ := hdsub
    cases c with
    | zero => omega
    | succ c' =>
        have hstep : Nat.gcd ((2^m - 1) / 3) (2^m + 1) * 1
            ≤ Nat.gcd ((2^m - 1) / 3) (2^m + 1) * (c' + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
  rcases Nat.eq_or_lt_of_le hgle with hg1 | hg2
  · have hg2' : Nat.gcd ((2^m - 1) / 3) (2^m + 1) = 2 := by omega
    rw [hg2'] at hdB
    obtain ⟨k, hk⟩ := hdB
    omega
  · omega

/-- **COPRIMALITY, ODD ROW.**  The odd-row factors are coprime: any common
divisor divides the line value `2` and the odd factor `2^m − 1`. -/
theorem factor_coprime_odd (m : Nat) (hmo : m % 2 = 1) :
    Nat.gcd ((2^m + 1) / 3) (2^m - 1) = 1 := by
  have hline := factor_line_odd m hmo
  have hdA : Nat.gcd ((2^m + 1) / 3) (2^m - 1) ∣ (2^m + 1) / 3 :=
    Nat.gcd_dvd_left _ _
  have hdB : Nat.gcd ((2^m + 1) / 3) (2^m - 1) ∣ 2^m - 1 :=
    Nat.gcd_dvd_right _ _
  have hd3A : Nat.gcd ((2^m + 1) / 3) (2^m - 1) ∣ 3 * ((2^m + 1) / 3) := by
    have key : ∀ g : Nat, g ∣ (2^m + 1) / 3 →
        g ∣ 3 * ((2^m + 1) / 3) := by
      intro g hg
      obtain ⟨k, hk⟩ := hg
      refine ⟨3 * k, ?_⟩
      rw [hk]
      ring
    exact key _ hdA
  have hdsub : Nat.gcd ((2^m + 1) / 3) (2^m - 1) ∣ 2 := by
    obtain ⟨u, hu⟩ := hdB
    obtain ⟨v, hv⟩ := hd3A
    have hvu : v = u + (v - u) := by omega
    rw [hvu] at hv
    have hexpand : Nat.gcd ((2^m + 1) / 3) (2^m - 1) * (u + (v - u))
        = Nat.gcd ((2^m + 1) / 3) (2^m - 1) * u
          + Nat.gcd ((2^m + 1) / 3) (2^m - 1) * (v - u) :=
      Nat.mul_add _ _ _
    rw [hexpand] at hv
    rw [← hu] at hv
    have hw : Nat.gcd ((2^m + 1) / 3) (2^m - 1) * (v - u) = 2 := by omega
    exact ⟨v - u, hw.symm⟩
  have hBodd : (2^m - 1) % 2 = 1 := by
    have h2m : 2^m = 2^(m - 1) * 2 := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      exact Nat.pow_succ 2 (m - 1)
    have hu : 1 ≤ 2^(m - 1) := Nat.pow_pos (by decide)
    omega
  have hge : 1 ≤ Nat.gcd ((2^m + 1) / 3) (2^m - 1) := by
    by_cases hg0 : Nat.gcd ((2^m + 1) / 3) (2^m - 1) = 0
    · obtain ⟨k, hk⟩ := hdB
      rw [hg0] at hk
      have h2m : 0 < 2^m := Nat.pow_pos (by decide)
      omega
    · omega
  have hgle : Nat.gcd ((2^m + 1) / 3) (2^m - 1) ≤ 2 := by
    obtain ⟨c, hc⟩ := hdsub
    cases c with
    | zero => omega
    | succ c' =>
        have hstep : Nat.gcd ((2^m + 1) / 3) (2^m - 1) * 1
            ≤ Nat.gcd ((2^m + 1) / 3) (2^m - 1) * (c' + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
  rcases Nat.eq_or_lt_of_le hgle with hg1 | hg2
  · have hg2' : Nat.gcd ((2^m + 1) / 3) (2^m - 1) = 2 := by omega
    rw [hg2'] at hdB
    obtain ⟨k, hk⟩ := hdB
    omega
  · omega

/-! ### The honest reach of the factorization

The factorization reduces the clean-word equation to: *can a product of two
coprime factors lying on the line `|3A − B| = 2` — with `A·B = (4^m − 1)/3` —
have all ternary digits in `{0, 1}`?*  No obstruction along these lines is
known: the ternary windows of `A` and `B` are governed by the same doubling
shadow as `4^m` itself, and the digit behavior of a product is not determined
by the digit behavior of its factors.  The factorization is recorded here as
verified structure of the equation, not as a separation certificate. -/

/-! ## Section 4 — the killed classes: the exact reach of the window method -/

/-- The surviving classes at level `L`: the discrete logs of the clean words,
the exhibited list of `shadow_count_exact`. -/
noncomputable def survivorClasses (L : Nat) : List Nat := (cleanList L).map (shadowLog L)

/-- Completeness of the exhibited survivor list: every clean-window class is
on it. -/
theorem survivorClasses_complete (L r : Nat) (hr : r < 3^L)
    (hclean : ∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2) :
    r ∈ survivorClasses L := by
  obtain ⟨z, hmem, hcongr⟩ := (shadow_class_iff L r hr).mp hclean
  have hlog : shadowLog L z = r :=
    shadowLog_eq L z r (cleanList_bound L z hmem).1 hr hcongr
  have hmem' : shadowLog L z ∈ (cleanList L).map (shadowLog L) :=
    List.mem_map_of_mem hmem
  rw [hlog] at hmem'
  exact hmem'

/-- Membership in the exhibited survivor list certifies the clean window. -/
theorem survivorClasses_clean (L r : Nat) (hr : r < 3^L)
    (hmem : r ∈ survivorClasses L) :
    ∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2 := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hmem
  have hspec := shadowLog_spec L z (cleanList_bound L z hz).1
  exact (shadow_class_iff L (shadowLog L z) hspec.1).mpr ⟨z, hz, hspec.2⟩

/-- **THE KILLED-CLASSES THEOREM.**  For every level `L`: any exponent whose
class mod `3^L` is *not* one of the `2^L` surviving classes owns a ternary
digit two within the first `L + 1` rows.  Each killed class is an infinite
arithmetic family of separated exponents. -/
theorem killed_class_early_digit_two (L m : Nat)
    (hkill : ¬ ((m % 3^L) ∈ survivorClasses L)) :
    ∃ p : Nat, p < L + 1 ∧ digit3 (4^m) p = 2 := by
  have h3L : 0 < 3^L := Nat.pow_pos (by decide)
  have hr : m % 3^L < 3^L := Nat.mod_lt _ h3L
  have htrans : ∀ p : Nat, p < L + 1 →
      digit3 (4^m) p = digit3 (4^(m % 3^L)) p := by
    intro p hp
    have hcls : 4^m % 3^(L+1) = 4^(m % 3^L) % 3^(L+1) :=
      pow4_mod_window_class L m
    calc digit3 (4^m) p = digit3 (4^m % 3^(L+1)) p :=
        (digit3_mod_window (4^m) (L+1) p hp).symm
      _ = digit3 (4^(m % 3^L) % 3^(L+1)) p := by rw [hcls]
      _ = digit3 (4^(m % 3^L)) p := digit3_mod_window _ (L+1) p hp
  by_contra hno
  apply hkill
  refine survivorClasses_complete L (m % 3^L) hr ?_
  intro p hp hdirty
  rw [← htrans p hp] at hdirty
  exact hno ⟨p, hp, hdirty⟩

/-! ### The level-five kernel receipt -/

/-- Decidable cleanliness scan of the low `B` rows of a window value. -/
def winClean : Nat → Nat → Bool
  | _, 0 => true
  | w, B + 1 => if w % 3 = 2 then false else winClean (w / 3) B

theorem winClean_iff (w B : Nat) :
    winClean w B = true ↔ ∀ p : Nat, p < B → digit3 w p ≠ 2 := by
  induction B generalizing w with
  | zero =>
      constructor
      · intro _ p hp
        omega
      · intro _
        rfl
  | succ B ih =>
      have h0 : digit3 w 0 = w % 3 := by
        unfold digit3
        rw [Nat.pow_zero, Nat.div_one]
      have hsh : ∀ p : Nat, digit3 w (p + 1) = digit3 (w / 3) p := by
        intro p
        have h := digit3_shift (w / 3) (w % 3) p (Nat.mod_lt _ (by norm_num))
        rw [Nat.div_add_mod w 3] at h
        exact h
      simp only [winClean]
      by_cases hw : w % 3 = 2
      · rw [if_pos hw]
        constructor
        · intro hfalse
          exact Bool.noConfusion hfalse
        · intro hall
          have hd0 := hall 0 (by omega)
          rw [h0, hw] at hd0
          exact absurd rfl hd0
      · rw [if_neg hw]
        constructor
        · intro hall p hp
          cases p with
          | zero => rw [h0]; omega
          | succ q =>
              rw [hsh q]
              exact ih (w / 3) |>.mp hall q (by omega)
        · intro hall
          refine ih (w / 3) |>.mpr ?_
          intro p hp
          rw [← hsh p]
          exact hall (p + 1) (by omega)

/-- The 32 surviving exponent classes modulo `243 = 3^5`, in order. -/
def survivorTable5 : List Nat :=
  [0, 1, 4, 10, 12, 13, 28, 31, 36, 37, 40, 63, 75, 81, 82, 93, 94, 108, 109,
   120, 121, 129, 144, 166, 172, 189, 193, 198, 199, 201, 210, 237]

/-- Decidable membership in the level-five survivor table. -/
def survivor5 (r : Nat) : Bool := survivorTable5.contains r

/-- **THE LEVEL-FIVE KERNEL RECEIPT.**  For every class below `243`, the
six-row window of `4^r` (computed by the monolith's own `powMod`) is clean
exactly on the exhibited 32-class table. -/
theorem survivor_table5_receipt : ∀ r < 243,
    winClean (powMod 4 r (3^6)) 6 = survivor5 r := by
  decide

/-- The level-five survivor count: exactly `32` classes below `243` have a
clean six-row window. -/
theorem survivor5_count_receipt :
    (List.range 243).countP (fun r => survivor5 r) = 32 := by
  decide

/-- The level-five killed count: exactly `211` of the `243` classes mod `243`
fail the six-row window. -/
theorem killed5_count_receipt :
    (List.range 243).countP (fun r => !survivor5 r) = 211 := by
  decide

private theorem digit3_pow_mod_window6 (r p : Nat) (hp : p < 6) :
    digit3 (powMod 4 r (3^6)) p = digit3 (4^r) p := by
  have hpm : powMod 4 r (3^6) = 4^r % 3^6 :=
    powMod_correct 4 r (3^6) (by norm_num)
  rw [hpm]
  exact digit3_mod_window (4^r) 6 p hp

/-- The Bool table agrees with the exhibited survivor list at level five. -/
theorem survivor5_iff_survivorClasses (r : Nat) (hr : r < 243) :
    survivor5 r = true ↔ r ∈ survivorClasses 5 := by
  have h3 : (3:Nat)^5 = 243 := by norm_num
  constructor
  · intro htrue
    have hwin := survivor_table5_receipt r hr
    rw [htrue] at hwin
    have hclean : ∀ p : Nat, p < 6 → digit3 (4^r) p ≠ 2 := by
      intro p hp
      have hdigit := (winClean_iff (powMod 4 r (3^6)) 6).mp hwin p hp
      rw [digit3_pow_mod_window6 r p hp] at hdigit
      exact hdigit
    have hr' : r < 3^5 := by rw [h3]; exact hr
    exact survivorClasses_complete 5 r hr' hclean
  · intro hmem
    have hclean := survivorClasses_clean 5 r (by rw [h3]; exact hr) hmem
    have hwin : winClean (powMod 4 r (3^6)) 6 = true := by
      refine (winClean_iff (powMod 4 r (3^6)) 6).mpr ?_
      intro p hp
      have hdigit := hclean p (by omega)
      rw [digit3_pow_mod_window6 r p hp]
      exact hdigit
    have htable := survivor_table5_receipt r hr
    rw [hwin] at htable
    exact htable.symm

/-- **THE LEVEL-FIVE SEPARATION.**  Any exponent whose class mod `243` is one
of the 211 killed classes owns a ternary digit two within the first six
rows — one infinite arithmetic family of separated exponents per killed
class, unconditionally, above and below the kernel base camp alike. -/
theorem separation_level_five (m : Nat)
    (hkill : survivor5 (m % 243) = false) :
    ∃ p : Nat, p < 6 ∧ digit3 (4^m) p = 2 := by
  have hr : m % 243 < 243 := Nat.mod_lt _ (by norm_num)
  have hne : ¬ ((m % 243) ∈ survivorClasses 5) := by
    intro hmem
    rw [(survivor5_iff_survivorClasses _ hr).mpr hmem] at hkill
    exact Bool.noConfusion hkill
  have hgen := killed_class_early_digit_two 5 m (by
    rw [show (3:Nat)^5 = 243 from by norm_num]
    exact hne)
  obtain ⟨p, hp, hdigit⟩ := hgen
  exact ⟨p, by omega, hdigit⟩

/-- **THE LEVEL-FIVE REACH.**  Every exponent either sits in one of the 32
surviving classes mod `243` (density `32/243 ≈ 13.2%`) or is separated with
an early digit two.  By the doubling law (`shadow_count_exact`) the 32
surviving classes are lived in at every deeper level — this is the exact
boundary of the window method, not a gap that more computation can close. -/
theorem level_five_reach (m : Nat) :
    survivor5 (m % 243) = true ∨
    ∃ p : Nat, p < 6 ∧ digit3 (4^m) p = 2 := by
  cases hb : survivor5 (m % 243) with
  | true => exact Or.inl rfl
  | false => exact Or.inr (separation_level_five m hb)

/-! ## Section 5 — receipts -/

#print axioms eternally_shadowed_iff_clean_quotient
#print axioms separation_iff_clean_word_equation
#print axioms crown_of_clean_word_equation
#print axioms eternally_shadowed_iff_bottom_half
#print axioms separated_of_dirty_digit
#print axioms separated_of_leading_digit_two
#print axioms cleanQuot_factor_even
#print axioms cleanQuot_factor_odd
#print axioms factor_line_even
#print axioms factor_line_odd
#print axioms factor_coprime_even
#print axioms factor_coprime_odd
#print axioms killed_class_early_digit_two
#print axioms survivor_table5_receipt
#print axioms separation_level_five
#print axioms level_five_reach

end GSTShadowSeparationAttack
