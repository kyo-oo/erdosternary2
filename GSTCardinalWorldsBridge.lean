import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# THE CARDINAL WORLDS BRIDGE — 2-world × 3-world × GST

The cardinal-worlds combination module.  The directive: the 2-world
(binary exponentials, the `d`-tower) and the 3-world (ternary sheets,
the `c`-tower / `lteCoeff` cascade) COMBINE through the GST bridges —
**Postulate I (the bridge signature) and the other bridges, NOT
Postulate II** — to convert `hTailF` from hypothesis to theorem.

## §1 THE ×2 BRIDGE — the signature injection law (`C ∩ 2C = {0}`)

A nonzero Cantor-clean window stays clean under NO doubling:
`CantorWindow m k → CantorWindow (2*m) k → m ≡ 0 (mod 3^k)`.  Doubling
a clean ternary word doubles every trit digitwise (no carries:
`0,1 ↦ 0,2`), so a live trit `1` becomes the signature `2`.  This is
the bridge `3 = 1 + 2` in its killing form: the 2-world generator
cannot act on a nonzero Cantor object without injecting the signature.

## §2 THE d-TOWER LAWS — Postulate I machinery

The 2-adic dual tower satisfies the exact square-lift recurrence
`d(j+1) = d(j) + 2^(j+1)·d(j)²` (dual to the c-tower's cube lift), the
parity law, and the mod-9 six-cycle `2 → 1 → 5 → 7 → 8 → 4 → 2`, which
pins Postulate I's face: the signature fires for `j ≡ 0,2,3,4 (mod 6)`;
the classes `j ≡ 1,5 (mod 6)` (values `1,4` mod 9) are the DEEP
classes — the mirror of the Erdős clean tree.

## §3 THE SKEWED MIRROR — the worlds' duality receipt

The c-tower (3-world: cube lift) and the d-tower (2-world: square lift)
are dual cascades across the bridge `3 = 1 + 2`.

## §4 THE FIRE TRANSPORT — the cut-word digit shift

`4^(3^s·core) = 1 + 3^(s+1)·omegaCutWord s core` transports trits
exactly: the power's trit at row `s+1+i` IS the cut word's trit at row
`i`.  A fire in the shadow is a fire in the power.

## §5 THE SHEET DECOMPOSITION — every `K ≥ 1` is `3^s·core`, `3 ∤ core`.

## §6 THE PROMOTION — hTailF as a THEOREM from two transparent slices

`four_power_omega_shadow_wave_tailF` follows from `hWave` (every sheet
`≥ 1` with core `≥ 2` fires in its cut word) and `hS0` (every 3-free
`a ≥ 5` in the deep classes `a ≡ 1,4 (mod 9)` fires).  The s = 0 content
of the tailF premise is exactly full Cantor cleanliness of `4^a` — the
circularity receipt — so `hS0` REFUTES the s = 0 premise rather than
consuming it.

## §7 THE CROWN FORM — `erdos_even_conjecture_of_slices`.

## §8 THE CARDINAL WORLDS LAW-PROMOTION — hTailF as a THEOREM of the
granted laws: **Postulate I** (the 2-world signature law) combined with
the **absorption-mirror bridge** (the worlds' combination law — the chief
of the other bridges).  The green receipts carried along: the 3-world
tower-twin of Postulate I's proven faces (`lteCoeff_has_two`), and the
6-world product bridge `4^a · d(2a−2) = 3^(2^(2a−2)) − 1`.  Postulate II
is nowhere in this promotion.
-/

namespace GSTCardinalWorldsBridge

open GSTFourPowerDirectResidue (digit3 lteCoeff pow4_three_power_lte_exact
  pow4_mod3_one)
open GSTGraphV2OmegaWaveLaw (omegaCutWord omegaGeoSum omega_cut_factor
  omega_lteCoeff_mod9)

/-! ## §0 Micro-lemmas -/

theorem three_pow_succ_mul (i : Nat) : 3^(i+1) = 3 * 3^i := by
  rw [Nat.pow_succ]; ac_rfl

theorem three_pow_pos' (i : Nat) : 0 < 3^i := Nat.pow_pos (by decide)

theorem digit3_zero (n : Nat) : n / 3^0 % 3 = n % 3 := by
  rw [Nat.pow_zero, Nat.div_one]

theorem div_mul_three (m i : Nat) : (3 * m) / 3^(i+1) = m / 3^i := by
  have hp : 3^(i+1) = 3 * 3^i := three_pow_succ_mul i
  have hmodlt : m % 3^i < 3^i := Nat.mod_lt m (three_pow_pos' i)
  have hlt : 3 * (m % 3^i) < 3 * 3^i :=
    Nat.mul_lt_mul_of_pos_left hmodlt (by decide : 0 < 3)
  have hdm := Nat.div_add_mod m (3^i)
  have hdecomp : 3 * m = 3^(i+1) * (m / 3^i) + 3 * (m % 3^i) := by
    calc 3 * m = 3 * (3^i * (m / 3^i) + m % 3^i) := by omega
      _ = 3^(i+1) * (m / 3^i) + 3 * (m % 3^i) := by rw [hp]; ring
  rw [hdecomp, Nat.add_comm, Nat.add_mul_div_left _ _ (three_pow_pos' (i+1)),
    Nat.div_eq_of_lt (by rw [hp]; exact hlt), Nat.zero_add]

theorem digit3_mul3_shift (m i : Nat) :
    (3 * m) / 3^(i+1) % 3 = m / 3^i % 3 := by
  rw [div_mul_three]

theorem div_lt_of_lt_mul' (a b c : Nat) (hb : 0 < b) (h : a < b * c) :
    a / b < c := by
  by_contra hcon
  push_neg at hcon
  have hmul := Nat.div_mul_le_self a b
  have hcb : b * c ≤ a := by
    have h1 : b * c ≤ b * (a / b) := Nat.mul_le_mul_left b hcon
    have h2 : b * (a / b) ≤ a := by
      have := Nat.div_mul_le_self a b
      rw [Nat.mul_comm b (a / b)]
      exact this
    omega
  omega

/-- The trit of `n / d` read through any window of height `3·d`. -/
theorem div_digit_window (n d v : Nat) (hd : 0 < d) (hv : v < 3 * d)
    (hn : n % (3 * d) = v) : n / d % 3 = v / d % 3 := by
  have hdm := Nat.div_add_mod n (3 * d)
  rw [hn] at hdm
  have hvlt : v / d < 3 := div_lt_of_lt_mul' v d 3 hd (by omega)
  have hsplit : n / d = v / d + 3 * (n / (3 * d)) := by
    have h2 : n = d * (3 * (n / (3 * d))) + v := by
      rw [← Nat.mul_assoc, Nat.mul_comm d (3: Nat)]
      exact hdm.symm
    conv_lhs => rw [h2]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd]
  rw [hsplit, Nat.add_mul_mod_self_left]

/-- The period engine: if `b ≡ 1 (mod m)` with `1 < m`, then every
power `b^q ≡ 1 (mod m)`. -/
theorem pow_mod_one_period (b q m : Nat) (hm : 1 < m) (hmod : b % m = 1) :
    b^q % m = 1 := by
  induction q with
  | zero => rw [Nat.pow_zero]; exact Nat.mod_eq_of_lt hm
  | succ q ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, hmod, Nat.one_mul]
    exact Nat.mod_eq_of_lt hm

theorem four_cube_mod9 : (4^3 : Nat) % 9 = 1 := by decide

theorem four_nine_mod27 : (4^9 : Nat) % 27 = 1 := by decide

theorem four_pow_mod9_period (core : Nat) : 4^core % 9 = 4^(core % 3) % 9 := by
  obtain ⟨q, r, hqr, hrlt⟩ : ∃ q r, core = 3 * q + r ∧ r < 3 :=
    ⟨core / 3, core % 3, by omega, Nat.mod_lt _ (by decide : 0 < 3)⟩
  have hr : core % 3 = r := by omega
  rw [show 4^core = 4^(3 * q + r) from by rw [← hqr], hr, Nat.pow_add,
    show 4^(3 * q) = (4^3)^q from by rw [Nat.pow_mul], Nat.mul_mod,
    pow_mod_one_period _ _ _ (by decide : 1 < 9) four_cube_mod9, Nat.one_mul]
  exact Nat.mod_mod_of_dvd (4^r) (Nat.dvd_refl 9)

theorem four_pow_mod27_period (core : Nat) : 4^core % 27 = 4^(core % 9) % 27 := by
  obtain ⟨q, r, hqr, hrlt⟩ : ∃ q r, core = 9 * q + r ∧ r < 9 :=
    ⟨core / 9, core % 9, by omega, Nat.mod_lt _ (by decide : 0 < 9)⟩
  have hr : core % 9 = r := by omega
  rw [show 4^core = 4^(9 * q + r) from by rw [← hqr], hr, Nat.pow_add,
    show 4^(9 * q) = (4^9)^q from by rw [Nat.pow_mul], Nat.mul_mod,
    pow_mod_one_period _ _ _ (by decide : 1 < 27) four_nine_mod27, Nat.one_mul]
  exact Nat.mod_mod_of_dvd (4^r) (Nat.dvd_refl 27)

/-! ## §1 THE ×2 BRIDGE — the signature injection law -/

/-- `n` is Cantor-clean in its first `k` trits. -/
def CantorWindow (n k : Nat) : Prop := ∀ i, i < k → n / 3^i % 3 ≠ 2

theorem cantorWindow_mul3 (m k : Nat) (h : CantorWindow (3 * m) (k+1)) :
    CantorWindow m k := by
  intro i hi
  have h2 : (3 * m) / 3^(i+1) % 3 ≠ 2 := h (i+1) (by omega)
  rw [digit3_mul3_shift] at h2
  exact h2

/-- **THE ×2 BRIDGE LAW (`C ∩ 2C = {0}`).**  A number and its double are
both Cantor-clean in the first `k` trits only if the number is zero in
that window.  Doubling a clean ternary word doubles each trit digitwise
(`0,1 ↦ 0,2` — no carries), so a live trit `1` becomes the bridge
signature `2`.  The 2-world generator cannot act on a nonzero Cantor
object without injecting the signature. -/
theorem two_mul_cantor_kill (m k : Nat)
    (hm : CantorWindow m k) (h2 : CantorWindow (2 * m) k) :
    m % 3^k = 0 := by
  induction k generalizing m with
  | zero => exact Nat.mod_one m
  | succ k ih =>
    have h0m : m % 3 ≠ 2 := by
      have hv := hm 0 (by omega)
      rw [digit3_zero] at hv
      exact hv
    have h02 : (2 * m) % 3 ≠ 2 := by
      have hv := h2 0 (by omega)
      rw [digit3_zero] at hv
      exact hv
    have hm03 : m % 3 = 0 := by
      have hmlt : m % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
      by_cases h0 : m % 3 = 0
      · exact h0
      · by_cases h1 : m % 3 = 1
        · exfalso
          have h2m : (2 * m) % 3 = 2 := by
            rw [Nat.mul_mod, h1]
          exact h02 h2m
        · omega
    have hm3 : m = 3 * (m / 3) := by
      have hdm := Nat.div_add_mod m (3: Nat)
      omega
    have hm' : CantorWindow (m / 3) k := by
      intro i hi
      have hval := hm (i+1) (by omega)
      rw [hm3, digit3_mul3_shift] at hval
      exact hval
    have h2' : CantorWindow (2 * (m / 3)) k := by
      intro i hi
      have hval := h2 (i+1) (by omega)
      rw [show 2 * m = 3 * (2 * (m / 3)) from by omega,
        digit3_mul3_shift] at hval
      exact hval
    have hrec := ih (m / 3) hm' h2'
    obtain ⟨q, hq⟩ : ∃ q, m / 3 = 3^k * q :=
      ⟨(m / 3) / 3^k, by
        have hdm := Nat.div_add_mod (m / 3) (3^k)
        rw [hrec] at hdm
        omega⟩
    have hdvd : 3^(k+1) ∣ m := by
      refine ⟨q, ?_⟩
      rw [hm3, hq, three_pow_succ_mul]
      ring
    exact Nat.mod_eq_zero_of_dvd hdvd

/-- **The ×2 bridge law, all-depths form.** -/
theorem two_mul_cantor_kill_all (m : Nat)
    (hm : ∀ i, m / 3^i % 3 ≠ 2) (h2 : ∀ i, (2 * m) / 3^i % 3 ≠ 2) :
    m = 0 := by
  have hzero : ∀ k, m % 3^k = 0 := fun k =>
    two_mul_cantor_kill m k (fun i _ => hm i) (fun i _ => h2 i)
  have hlt : m < 3^(m+1) := by
    have h3 : 3^m ≤ 3^(m+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3: Nat)) (by omega)
    calc m < 3^m := Nat.lt_pow_self (by decide : 1 < (3: Nat))
      _ ≤ 3^(m+1) := h3
  have hmod := hzero (m+1)
  have hself : m % 3^(m+1) = m := Nat.mod_eq_of_lt hlt
  omega

/-! ## §2 THE d-TOWER LAWS — Postulate I machinery -/

/-- **THE d-TOWER SQUARE-LIFT RECURRENCE** (the 2-world dual of the
c-tower cube lift): `d(j+1) = d(j) + 2^(j+1)·d(j)²`, verbatim from the
dual tower identity by squaring. -/
theorem d_recurrence (j : Nat) (hj : 1 ≤ j) :
    d (j+1) = d j + 2^(j+1) * (d j)^2 := by
  have hA := d_identity j hj
  have hB := d_identity (j+1) (by omega)
  have hpos : 0 < 3^(2^j) := three_pow_pos' (2^j)
  have hpos2 : 0 < 3^(2^(j+1)) := three_pow_pos' (2^(j+1))
  have h3 : 3^(2^j) = 1 + 2^(j+2) * d j := by omega
  have hsq : 3^(2^(j+1)) = (3^(2^j))^2 := by
    rw [show 2^(j+1) = 2^j * 2 from by rw [Nat.pow_succ],
      Nat.pow_mul]
  have hp4 : 2^(j+2) * 2^(j+2) = 2^(j+3) * 2^(j+1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have h2a : 2^(j+3) = 2 * 2^(j+2) := by rw [Nat.pow_succ]; ac_rfl
  have hexpand : (1 + 2^(j+2) * d j)^2
      = 1 + 2^(j+3) * d j + 2^(j+2) * 2^(j+2) * (d j)^2 := by
    rw [h2a]
    ring
  have hBadd : 2^(j+1+2) * d (j+1) + 1 = 3^(2^(j+1)) := by omega
  have h1 : 2^(j+1+2) * d (j+1) + 1 = (3^(2^j))^2 := by
    rw [hBadd]
    exact hsq
  have h2' : (3^(2^j))^2 = (1 + 2^(j+2) * d j)^2 := by rw [h3]
  have h3' : 2^(j+1+2) * d (j+1) + 1
      = 1 + 2^(j+3) * d j + 2^(j+2) * 2^(j+2) * (d j)^2 := by
    rw [h1, h2']
    exact hexpand
  have h4 : 2^(j+1+2) * d (j+1)
      = 2^(j+3) * d j + 2^(j+2) * 2^(j+2) * (d j)^2 := by omega
  have h5 : 2^(j+1+2) * (d j + 2^(j+1) * (d j)^2)
      = 2^(j+3) * d j + 2^(j+3) * 2^(j+1) * (d j)^2 := by
    rw [Nat.mul_add, show 2^(j+1+2) = 2^(j+3) from by rfl]
    ring
  rw [hp4] at h4
  have hcancel : 2^(j+1+2) * d (j+1)
      = 2^(j+1+2) * (d j + 2^(j+1) * (d j)^2) := h4.trans h5.symm
  exact Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2)) hcancel

theorem two_pow_mod3_pair (j : Nat) :
    (2^j % 3 = 1 ∧ j % 2 = 0) ∨ (2^j % 3 = 2 ∧ j % 2 = 1) := by
  induction j with
  | zero => exact Or.inl ⟨by decide, by decide⟩
  | succ j ih =>
    rcases ih with ⟨hv, hp⟩ | ⟨hv, hp⟩
    · refine Or.inr ⟨?_, by omega⟩
      rw [Nat.pow_succ, Nat.mul_mod, hv]
      try decide
    · refine Or.inl ⟨?_, by omega⟩
      rw [Nat.pow_succ, Nat.mul_mod, hv]
      try decide

/-- **THE d-TOWER PARITY LAW.**  `d(j) ≡ 2 (mod 3)` for even `j`, `≡ 1`
for odd `j` (from `j ≥ 1`).  The 2-world tower oscillates across the
bridge. -/
theorem d_mod3_parity (j : Nat) : 1 ≤ j →
    ((j % 2 = 0 → d j % 3 = 2) ∧ (j % 2 = 1 → d j % 3 = 1)) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · omega
    · by_cases hj1 : j = 1
      · subst hj1
        have hb := d_identity 1 (by omega)
        have h31 : (3: Nat)^(2^1) = 9 := by decide
        have h22 : (2: Nat)^(1+2) = 8 := by decide
        rw [h31, h22] at hb
        have hd1 : d 1 = 1 := by omega
        refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
        rw [hd1]
      · have hj2 : 2 ≤ j := by omega
        have hrec : d j = d (j-1) + 2^j * (d (j-1))^2 := by
          have h := d_recurrence (j-1) (by omega)
          rw [show j - 1 + 1 = j from by omega] at h
          exact h
        have hprev := ih (j-1) (by omega) (by omega)
        have hmod : d j % 3
            = (d (j-1) % 3 + (2^j % 3 * ((d (j-1))^2 % 3)) % 3) % 3 := by
          rw [hrec, Nat.add_mod, Nat.mul_mod]
        have hpair := two_pow_mod3_pair j
        by_cases hpar : j % 2 = 0
        · rcases hpair with ⟨h2v, h2p⟩ | ⟨h2v, h2p⟩
          · have hprevodd : (j-1) % 2 = 1 := by omega
            have hdprev := hprev.2 hprevodd
            refine ⟨fun _ => ?_, fun hcon => absurd hcon (by omega)⟩
            rw [hmod, hdprev, h2v, Nat.pow_mod, hdprev]
          · exact absurd h2p (by omega)
        · rcases hpair with ⟨h2v, h2p⟩ | ⟨h2v, h2p⟩
          · exact absurd h2p (by omega)
          · have hpreveven : (j-1) % 2 = 0 := by omega
            have hdprev := hprev.1 hpreveven
            refine ⟨fun hcon => absurd hcon (by omega), fun _ => ?_⟩
            rw [hmod, hdprev, h2v, Nat.pow_mod, hdprev]

theorem two_pow_six_mod9 (q : Nat) : (2^6)^q % 9 = 1 := by
  induction q with
  | zero => rw [Nat.pow_zero]
            try exact Nat.mod_eq_of_lt (by decide : 1 < 9)
  | succ q ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, show (2^6 : Nat) % 9 = 1 from by decide,
      Nat.one_mul]
    try exact Nat.mod_eq_of_lt (by decide : 1 < 9)

theorem two_pow_mod9 (j : Nat) : 2^j % 9 = 2^(j % 6) % 9 := by
  obtain ⟨q, r, hqr, hrlt⟩ : ∃ q r, j = 6 * q + r ∧ r < 6 :=
    ⟨j / 6, j % 6, by omega, Nat.mod_lt _ (by decide : 0 < 6)⟩
  have hr : j % 6 = r := by omega
  rw [show 2^j = 2^(6 * q + r) from by rw [← hqr], hr, Nat.pow_add,
    show 2^(6 * q) = (2^6)^q from by rw [Nat.pow_mul], Nat.mul_mod,
    two_pow_six_mod9, Nat.one_mul]
  exact Nat.mod_mod_of_dvd (2^r) (Nat.dvd_refl 9)

/-- **THE d-TOWER MOD-9 SIX-CYCLE.**  For `j ≥ 3`:
`j mod 6 = 0,1,2,3,4,5 ↦ d(j) mod 9 = 2,1,5,7,8,4`.  The cycle
`2 → 1 → 5 → 7 → 8 → 4 → 2` is closed by the square-lift recurrence
driven by the 2-world period `2^j mod 9`.  Postulate I's face: the
signature fires at trit zero for `j ≡ 0,2,4`, at trit one for
`j ≡ 3`; the classes `j ≡ 1,5` (values `1,4` — clean at trits zero and
one) are the DEEP classes, the exact mirror of the Erdős clean tree. -/
theorem d_mod9_cycle (j : Nat) : 3 ≤ j →
    (j % 6 = 0 → d j % 9 = 2) ∧ (j % 6 = 1 → d j % 9 = 1) ∧
    (j % 6 = 2 → d j % 9 = 5) ∧ (j % 6 = 3 → d j % 9 = 7) ∧
    (j % 6 = 4 → d j % 9 = 8) ∧ (j % 6 = 5 → d j % 9 = 4) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    by_cases hj8 : j ≤ 8
    · by_cases h3 : j = 3
      · subst h3; decide
      · by_cases h4 : j = 4
        · subst h4; decide
        · by_cases h5 : j = 5
          · subst h5; decide
          · by_cases h6 : j = 6
            · subst h6; decide
            · by_cases h7 : j = 7
              · subst h7; decide
              · have h8 : j = 8 := by omega
                subst h8; decide
    · have hj9 : 9 ≤ j := by omega
      have hrec : d j = d (j-1) + 2^j * (d (j-1))^2 := by
        have h := d_recurrence (j-1) (by omega)
        rw [show j - 1 + 1 = j from by omega] at h
        exact h
      have hprev := ih (j-1) (by omega) (by omega)
      by_cases h0 : j % 6 = 0
      · have hF5 : (j-1) % 6 = 5 := by omega
        have hF := hprev.2.2.2.2.2 hF5
        have hmod : d j % 9
            = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
          rw [hrec, Nat.add_mod, Nat.mul_mod]
        have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
        refine ⟨fun _ => ?_, fun h => absurd h (by omega),
          fun h => absurd h (by omega), fun h => absurd h (by omega),
          fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
        rw [hmod, h2mod, h0, show (2:Nat)^0 % 9 = 1 from by decide,
          Nat.pow_mod (d (j-1)) 2 9, hF]
      · by_cases h1 : j % 6 = 1
        · have hF0 : (j-1) % 6 = 0 := by omega
          have hF := hprev.1 hF0
          have hmod : d j % 9
              = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
            rw [hrec, Nat.add_mod, Nat.mul_mod]
          have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
          refine ⟨fun h => absurd h (by omega), fun _ => ?_,
            fun h => absurd h (by omega), fun h => absurd h (by omega),
            fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
          rw [hmod, h2mod, h1, show (2:Nat)^1 % 9 = 2 from by decide,
            Nat.pow_mod (d (j-1)) 2 9, hF]
        · by_cases h2 : j % 6 = 2
          · have hF1 : (j-1) % 6 = 1 := by omega
            have hF := hprev.2.1 hF1
            have hmod : d j % 9
                = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
              rw [hrec, Nat.add_mod, Nat.mul_mod]
            have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
            refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
              fun _ => ?_, fun h => absurd h (by omega),
              fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
            rw [hmod, h2mod, h2, show (2:Nat)^2 % 9 = 4 from by decide,
              Nat.pow_mod (d (j-1)) 2 9, hF]
          · by_cases h3 : j % 6 = 3
            · have hF2 : (j-1) % 6 = 2 := by omega
              have hF := hprev.2.2.1 hF2
              have hmod : d j % 9
                  = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
                rw [hrec, Nat.add_mod, Nat.mul_mod]
              have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
              refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
                fun h => absurd h (by omega), fun _ => ?_,
                fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
              rw [hmod, h2mod, h3, show (2:Nat)^3 % 9 = 8 from by decide,
                Nat.pow_mod (d (j-1)) 2 9, hF]
            · by_cases h4 : j % 6 = 4
              · have hF3 : (j-1) % 6 = 3 := by omega
                have hF := hprev.2.2.2.1 hF3
                have hmod : d j % 9
                    = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
                  rw [hrec, Nat.add_mod, Nat.mul_mod]
                have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
                refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
                  fun h => absurd h (by omega), fun h => absurd h (by omega),
                  fun _ => ?_, fun h => absurd h (by omega)⟩
                rw [hmod, h2mod, h4, show (2:Nat)^4 % 9 = 7 from by decide,
                  Nat.pow_mod (d (j-1)) 2 9, hF]
              · have h5 : j % 6 = 5 := by
                  have : j % 6 < 6 := Nat.mod_lt _ (by decide : 0 < 6)
                  omega
                have hF4 : (j-1) % 6 = 4 := by omega
                have hF := hprev.2.2.2.2.1 hF4
                have hmod : d j % 9
                    = (d (j-1) % 9 + (2^j % 9 * ((d (j-1))^2 % 9)) % 9) % 9 := by
                  rw [hrec, Nat.add_mod, Nat.mul_mod]
                have h2mod : 2^j % 9 = 2^(j % 6) % 9 := two_pow_mod9 j
                refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
                  fun h => absurd h (by omega), fun h => absurd h (by omega),
                  fun h => absurd h (by omega), fun _ => ?_⟩
                rw [hmod, h2mod, h5, show (2:Nat)^5 % 9 = 5 from by decide,
                  Nat.pow_mod (d (j-1)) 2 9, hF]

/-- **POSTULATE I's oscillation face.**  For every `j ≥ 2` outside the
deep classes (`j ≡ 1,5 (mod 6)`), the bridge signature fires. -/
theorem postulate_I_fire_outside_deep (j : Nat) (hj : 2 ≤ j)
    (h : j % 6 ≠ 1 ∧ j % 6 ≠ 5) : hasTernaryTwo (d j) = true := by
  rcases (by omega : j % 2 = 0 ∨ j % 6 = 3) with heven | h3
  · exact bridge_sig_even j hj heven
  · exact bridge_sig_j_mod6_3 j (by omega) h3

/-! ## §3 THE SKEWED MIRROR — the worlds' duality receipt -/

/-- **THE CARDINAL WORLDS MIRROR.**  The 3-world tower (the cascade
cubic, cube lift `+3^(s+1)·c² + 3^(2s+1)·c³`) and the 2-world tower
(the square lift `+2^(j+1)·d²`) are dual cascades across the bridge
`3 = 1 + 2`.  The skew between the worlds — `2·3^s` against `2^j`,
`s+1` against `j+2` — IS the bridge signature. -/
theorem cardinal_worlds_mirror :
    (∀ s : Nat, 1 ≤ s →
       c (s+1) = c s + 3^(s+1) * (c s)^2 + 3^(2*s+1) * (c s)^3) ∧
    (∀ j : Nat, 1 ≤ j → d (j+1) = d j + 2^(j+1) * (d j)^2) ∧
    ((3: Nat) = 1 + 2) :=
  ⟨fun s hs => c_recursion s hs, fun j hj => d_recurrence j hj, rfl⟩

/-! ## §4 THE FIRE TRANSPORT — the cut-word digit shift -/

/-- **THE CUT-WORD DIGIT SHIFT.**  If `4^E = 1 + 3^(s+1)·W` then the
trit of the power at row `s+1+i` IS the trit of `W` at row `i`.  A fire
in the shadow is a fire in the power, displaced by the cut. -/
theorem cut_shift_general (E s W i : Nat) (hE : 4^E = 1 + 3^(s+1) * W) :
    4^E / 3^(s+1+i) % 3 = W / 3^i % 3 := by
  obtain ⟨R, hRdef⟩ : ∃ R, W % 3^(i+1) % 3^i = R := ⟨_, rfl⟩
  have hQ := Nat.div_add_mod W (3^(i+1))
  have hRlt : W % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (three_pow_pos' (i+1))
  have hr0lt : R < 3^i := by
    rw [← hRdef]
    exact Nat.mod_lt _ (three_pow_pos' i)
  have hR2 : 3^i * (W % 3^(i+1) / 3^i) + R = W % 3^(i+1) := by
    have h := Nat.div_add_mod (W % 3^(i+1)) (3^i)
    rw [hRdef] at h
    exact h
  have hpow2 : 3^(s+1) * 3^i = 3^(s+1+i) := by rw [Nat.pow_add]; ring
  have hWsplit : W = 3^(i+1) * (W / 3^(i+1)) + 3^i * (W % 3^(i+1) / 3^i) + R := by
    rw [Nat.add_assoc]
    rw [← hR2] at hQ
    exact hQ.symm
  have hregroup : W = R + 3^i * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i) := by
    have hps : 3^(i+1) = 3 * 3^i := three_pow_succ_mul i
    calc W = 3^(i+1) * (W / 3^(i+1)) + 3^i * (W % 3^(i+1) / 3^i) + R := hWsplit
      _ = 3 * 3^i * (W / 3^(i+1)) + 3^i * (W % 3^(i+1) / 3^i) + R := by
          rw [hps]
      _ = R + 3^i * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i) := by
          ring
  have hEsplit : 4^E = (1 + 3^(s+1) * R)
      + 3^(s+1+i) * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i) := by
    rw [hE]
    have hW : 3^(s+1) * W = 3^(s+1) * R
        + 3^(s+1+i) * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i) := by
      calc 3^(s+1) * W
          = 3^(s+1) * (R + 3^i * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i)) := by
            rw [← hregroup]
        _ = 3^(s+1) * R
            + 3^(s+1) * (3^i * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i)) := by
            rw [Nat.mul_add]
        _ = 3^(s+1) * R
            + 3^(s+1+i) * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i) := by
            rw [← Nat.mul_assoc, hpow2]
    rw [hW]
    ring
  have hsmall : 1 + 3^(s+1) * R < 3^(s+1+i) := by
    have hle : 3^(s+1) * R + 3^(s+1) ≤ 3^(s+1) * 3^i := by
      have h := Nat.mul_le_mul (Nat.le_refl (3^(s+1)))
        (by omega : R + 1 ≤ 3^i)
      rw [Nat.mul_add, Nat.mul_one] at h
      exact h
    have hN : 2 ≤ 3^(s+1) := by
      have h3le := Nat.pow_le_pow_of_le (by decide : 1 < (3: Nat))
        (by omega : 1 ≤ s+1)
      have h31 : (3: Nat)^1 = 3 := rfl
      omega
    have hQ2 : 3^(s+1) * 3^i = 3^(s+1+i) := hpow2
    omega
  have hdivL : 4^E / 3^(s+1+i)
      = 3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i := by
    rw [hEsplit, Nat.add_mul_div_left _ _ (three_pow_pos' (s+1+i)),
      Nat.div_eq_of_lt hsmall, Nat.zero_add]
  have hdivR : W / 3^i = 3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i := by
    have hstep : W / 3^i
        = (R + 3^i * (3 * (W / 3^(i+1)) + W % 3^(i+1) / 3^i)) / 3^i := by
      rw [← hregroup]
    rw [hstep, Nat.add_mul_div_left _ _ (three_pow_pos' i),
      Nat.div_eq_of_lt hr0lt, Nat.zero_add]
  rw [hdivL, hdivR]

/-- **THE SHEET-ZERO SHIFT.**  The trit of `4^core` at row `q+1` is the
trit of its sheet-zero cut word at row `q`. -/
theorem cut_shift_s0 (core q : Nat) :
    4^core / 3^(q+1) % 3 = omegaCutWord 0 core / 3^q % 3 := by
  have hE : 4^(3^0 * core) = 1 + 3^(0+1) * omegaCutWord 0 core :=
    omega_cut_factor 0 core
  have hE' : 4^core = 1 + 3^(0+1) * omegaCutWord 0 core := by
    rw [← hE, Nat.pow_zero, Nat.one_mul]
  have hshift := cut_shift_general core 0 (omegaCutWord 0 core) q hE'
  rw [show 0 + 1 + q = q + 1 from by omega] at hshift
  exact hshift

/-! ## §5 THE SHEET DECOMPOSITION -/

theorem sheet_decompose (K : Nat) (hK : 1 ≤ K) :
    ∃ s core : Nat, K = 3^s * core ∧ ¬ (3 ∣ core) := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    by_cases h3 : 3 ∣ K
    · obtain ⟨q, hq⟩ := h3
      have hq1 : 1 ≤ q := by omega
      obtain ⟨s, core, hs, hc⟩ := ih q (by omega) hq1
      refine ⟨s+1, core, ?_, hc⟩
      rw [hq, hs, Nat.pow_succ]
      ring
    · exact ⟨0, K, by rw [Nat.pow_zero, Nat.one_mul], h3⟩

/-! ## §6 THE PROMOTION — hTailF as a THEOREM from two transparent slices -/

/-- **THE s = 0 CIRCULARITY RECEIPT.**  The s = 0 content of the tailF
premise (the all-depths row observer clause) forces `4^core` to be
Cantor-clean at EVERY position — the premise IS the negation of the
conclusion.  Hence the s = 0 family of `hTailF` can only be satisfied
vacuously: the slice input `hS0` refutes the premise outright. -/
theorem s0_premise_full_clean (core : Nat) (hclass : core % 3 = 1)
    (hW1 : omegaCutWord 0 core % 3^(0+2) < 2 * 3^(0+1))
    (hWall : ∀ j : Nat, 2 ≤ j → omegaCutWord 0 core % 3^(j+1) < 2 * 3^j) :
    ∀ p : Nat, 4^core / 3^p % 3 ≠ 2 := by
  have hW0 : omegaCutWord 0 core / 3^0 % 3 = 1 := by
    have hmod9 : 4^core % 9 = 4 := by
      rw [four_pow_mod9_period core, hclass]
      decide
    have hwin := div_digit_window (4^core) 3 4 (by decide) (by decide)
      (by rw [hmod9])
    rw [show (4: Nat)/3 % 3 = 1 from by decide] at hwin
    have hshift := cut_shift_s0 core 0
    rw [← hshift]
    exact hwin
  have hW1v : omegaCutWord 0 core / 3^1 % 3 ≠ 2 := by
    show omegaCutWord 0 core / 3 % 3 ≠ 2
    have hlt9 : omegaCutWord 0 core % 9 < 6 := by
      rw [show (9: Nat) = 3^(0+2) from by decide,
        show (6: Nat) = 2 * 3^(0+1) from by decide]
      exact hW1
    have hwin := div_digit_window (omegaCutWord 0 core) 3
      (omegaCutWord 0 core % 9) (by decide)
      (Nat.mod_lt _ (by decide : 0 < 9)) rfl
    have hlt2 : omegaCutWord 0 core % 9 / 3 < 2 :=
      div_lt_of_lt_mul' _ 3 2 (by decide) (by omega)
    rw [hwin, Nat.mod_eq_of_lt (by omega : omegaCutWord 0 core % 9 / 3 < 3)]
    exact ne_of_lt hlt2
  intro p
  cases p with
  | zero =>
    rw [digit3_zero, pow4_mod3_one]
    try decide
  | succ q =>
    rw [cut_shift_s0 core q]
    cases q with
    | zero => rw [hW0]; try decide
    | succ j =>
      cases j with
      | zero => exact hW1v
      | succ j' =>
        have hj : 2 ≤ j' + 2 := by omega
        have hlt := hWall (j'+2) hj
        have hwin := div_digit_window (omegaCutWord 0 core) (3^(j'+2))
          (omegaCutWord 0 core % 3^(j'+2+1)) (three_pow_pos' (j'+2))
          (by
            have hmb := Nat.mod_lt (omegaCutWord 0 core) (three_pow_pos' (j'+2+1))
            have hp := three_pow_succ_mul (j'+2)
            omega)
          (by rw [three_pow_succ_mul (j'+2)])
        have hq2 : omegaCutWord 0 core % 3^(j'+2+1) / 3^(j'+2) < 2 :=
          div_lt_of_lt_mul' _ (3^(j'+2)) 2 (three_pow_pos' (j'+2)) (by omega)
        rw [hwin, Nat.mod_eq_of_lt (by omega :
          omegaCutWord 0 core % 3^(j'+2+1) / 3^(j'+2) < 3)]
        exact ne_of_lt hq2

/-- **THE PROMOTION — `hTailF` as a theorem from the two transparent
slices.**  Inputs:

* `hWave` — the Ω-shadow wave over all sheets `s ≥ 1`: every 3-free
  core `≥ 2` fires in its cut word;
* `hS0` — the sheet-zero slice: every 3-free `a ≥ 5` in the deep
  classes `a ≡ 1,4 (mod 9)` fires.

The s = 0 premise of the tailF is the full-Cantor-circularity receipt
(`s0_premise_full_clean`), so `hS0` refutes it; the s ≥ 1 premise is
transported by the cut-word digit shift. -/
theorem four_power_omega_shadow_wave_tailF_of_slices
    (hWave : ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
       hasTernaryTwo (omegaCutWord s core) = true)
    (hS0 : ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
       hasTernaryTwo (4^a) = true) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF := by
  intro K hK hprem
  obtain ⟨s, core, hsc, hc3, hclass, hW1, hL1, hL2, hS0cl, hCl⟩ := hprem
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    have hclass3 : core % 3 = 1 := by
      rcases hclass with h4 | ⟨_, h1⟩ | ⟨hs, h7⟩
      · omega
      · omega
      · omega
    have hclass9 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hclass with h4 | ⟨_, h1⟩ | ⟨hs, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd hs (by omega)
    have hcore5 : 5 ≤ core := by
      rw [Nat.pow_zero, Nat.one_mul] at hsc
      omega
    have hfull := s0_premise_full_clean core hclass3 hW1
      (fun j hj => hS0cl rfl j hj)
    have hfire := hS0 core hcore5 hc3 hclass9
    obtain ⟨p, hp⟩ := hasTernaryTwo_pos (4^core) hfire
    exact absurd hp (hfull p)
  · have hcore2 : 2 ≤ core := by
      rcases Nat.eq_zero_or_pos core with h0 | hp
      · exfalso
        rw [h0] at hc3
        exact hc3 ⟨0, rfl⟩
      · by_cases h1 : core = 1
        · exfalso
          rcases hclass with h4 | ⟨h0s, _⟩ | ⟨h1s, h7⟩
          · rw [h1] at h4
            exact absurd h4 (by decide)
          · exact absurd h0s (by omega)
          · rw [h1] at h7
            exact absurd h7 (by decide)
        · omega
    have hfireW := hWave s core hs1 hcore2 hc3
    obtain ⟨i, hi⟩ := hasTernaryTwo_pos _ hfireW
    refine ⟨s+1+i, ?_⟩
    have hE : 4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core :=
      omega_cut_factor s core
    have hshift := cut_shift_general (3^s * core) s (omegaCutWord s core) i hE
    show 4^K / 3^(s+1+i) % 3 = 2
    rw [hsc]
    exact hshift.trans hi

/-- **THE CROWN — the even Erdős conjecture from the two slices.**  Under
`hWave` and `hS0`, every `4^K` with `K ≥ 8` owns its ternary digit
two.  Coverage: sheets `s ≥ 1` by `hWave` (through the digit shift; the
unit-tail `core = 1` by the `lteCoeff ≡ 7 (mod 9)` window); sheet zero
by the green mod-9/mod-27 windows (`K ≡ 2 (mod 3)` fires at row 1,
`K ≡ 7 (mod 9)` at row 2) and `hS0` for the deep classes. -/
theorem erdos_even_of_slices
    (hWave : ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
       hasTernaryTwo (omegaCutWord s core) = true)
    (hS0 : ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
       hasTernaryTwo (4^a) = true)
    (K : Nat) (hK : 8 ≤ K) :
    hasTernaryTwo (4^K) = true := by
  obtain ⟨s, core, hsc, hc3⟩ := sheet_decompose K (by omega)
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    rw [Nat.pow_zero, Nat.one_mul] at hsc
    subst hsc
    by_cases h71 : K % 9 = 7
    · have hmod27 : 4^K % 27 = 22 := by
        rw [four_pow_mod27_period K, h71]
        decide
      have hwin := div_digit_window (4^K) 9 22 (by decide) (by decide)
        (by rw [hmod27])
      rw [show (22: Nat)/9 % 3 = 2 from by decide] at hwin
      exact hasTernaryTwo_of_digit (4^K) 2 hwin
    · by_cases h32 : K % 3 = 2
      · have hmod9 : 4^K % 9 = 7 := by
          rw [four_pow_mod9_period K, h32]
          decide
        have hwin := div_digit_window (4^K) 3 7 (by decide) (by decide)
          (by rw [hmod9])
        rw [show (7: Nat)/3 % 3 = 2 from by decide] at hwin
        exact hasTernaryTwo_of_digit (4^K) 1 hwin
      · have hc13 : K % 3 = 1 := by
          have : K % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
          omega
        have hclass9 : K % 9 = 1 ∨ K % 9 = 4 := by
          have h9lt : K % 9 < 9 := Nat.mod_lt _ (by decide : 0 < 9)
          by_cases hc1 : K % 9 = 1
          · exact Or.inl hc1
          · by_cases hc4 : K % 9 = 4
            · exact Or.inr hc4
            · exfalso
              omega
        exact hS0 K (by omega) hc3 hclass9
  · by_cases hcore1 : core = 1
    · rw [hcore1, Nat.mul_one] at hsc
      have hE : 4^(3^s) = 1 + 3^(s+1) * lteCoeff s :=
        pow4_three_power_lte_exact s
      have hshift := cut_shift_general (3^s) s (lteCoeff s) 1 hE
      have hlte : lteCoeff s % 9 = 7 := omega_lteCoeff_mod9 s hs1
      have hwin := div_digit_window (lteCoeff s) 3 7 (by decide) (by decide)
        (by rw [hlte])
      rw [show (7: Nat)/3 % 3 = 2 from by decide] at hwin
      rw [hsc]
      refine hasTernaryTwo_of_digit (4^(3^s)) (s+1+1) ?_
      rw [hshift]
      exact hwin
    · have hcore2 : 2 ≤ core := by
        rcases Nat.eq_zero_or_pos core with h0 | hp
        · exfalso
          rw [h0] at hc3
          exact hc3 ⟨0, rfl⟩
        · omega
      have hfireW := hWave s core hs1 hcore2 hc3
      obtain ⟨i, hi⟩ := hasTernaryTwo_pos _ hfireW
      refine hasTernaryTwo_of_digit (4^K) (s+1+i) ?_
      rw [hsc]
      exact (cut_shift_general (3^s * core) s (omegaCutWord s core) i
        (omega_cut_factor s core)).trans hi

/-- **THE CROWN, `noTernaryTwo` form.** -/
theorem erdos_even_conjecture_of_slices
    (hWave : ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
       hasTernaryTwo (omegaCutWord s core) = true)
    (hS0 : ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
       hasTernaryTwo (4^a) = true) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  fun K hK => has_two_imp_not_no_two _ (erdos_even_of_slices hWave hS0 K hK)

/-! ## §8 THE CARDINAL WORLDS LAW-PROMOTION — hTailF as a theorem of the
granted laws -/

/-- **THE 3-WORLD TOWER-TWIN RECEIPT.**  The c-tower (the LTE mean
cascade) fires at every sheet from one on — `lteCoeff s ≡ 7 (mod 9)` is
the ternary word `21`, the signature at row one.  This is the 3-world's
twin of Postulate I's proven faces (`bridge_sig_even`,
`bridge_sig_j_mod6_3`): each world's tower carries the signature in its
own register. -/
theorem lteCoeff_has_two (s : Nat) (hs : 1 ≤ s) :
    hasTernaryTwo (lteCoeff s) = true := by
  have h9 : lteCoeff s % 9 = 7 := omega_lteCoeff_mod9 s hs
  have hd : lteCoeff s = 9 * (lteCoeff s / 9) + 7 := by
    have := Nat.div_add_mod (lteCoeff s) 9
    omega
  have hdiv3 : lteCoeff s / 3 = 3 * (lteCoeff s / 9) + 2 := by
    have h3 := Nat.div_add_mod (lteCoeff s) 3
    omega
  refine hasTernaryTwo_of_digit (lteCoeff s) 1 ?_
  rw [Nat.pow_one, hdiv3]
  omega

/-- **THE 6-WORLD PRODUCT BRIDGE.**  `4^a · d(2a−2) = 3^(2^(2a−2)) − 1`:
the 3-world's power times the 2-world's tower value at the matched index
is the maximal all-twos word of the 6-world — the product world `6^j =
2^j · 3^j` in its killing form.  This is the arithmetic face of the
synchronized shadows: the two cardinal worlds' objects multiply into the
one maximal cascade object. -/
theorem four_pow_mul_d (a : Nat) (ha : 2 ≤ a) :
    4^a * d (2*a - 2) = 3^(2^(2*a - 2)) - 1 := by
  have hne : 2*a - 2 ≠ 0 := by omega
  have hj1 : 1 ≤ 2*a - 2 := by omega
  have hdvd : 2^((2*a-2)+2) ∣ (3^(2^(2*a-2)) - 1) :=
    two_pow_divides (2*a-2) hj1
  obtain ⟨q, hq⟩ := hdvd
  have hexp : (2*a-2)+2 = 2*a := by omega
  rw [hexp] at hq
  have hd : d (2*a-2) = (3^(2^(2*a-2)) - 1) / 2^(2*a) := by
    simp only [d, if_neg hne]
    rw [hexp]
  have h4 : 4^a = 2^(2*a) := by
    rw [← Nat.pow_mul]
    congr 1
    omega
  have hdiv : (3^(2^(2*a-2)) - 1) / 2^(2*a) = q := by
    rw [hq, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : (0:Nat) < 2))]
  rw [h4, hd, hdiv, ← hq]

/-- **THE ABSORPTION-MIRROR BRIDGE** — the worlds' combination law (the
chief of the other bridges).  The 2-world and the 3-world share the one
absorption tree of the 6-world — the synchronized shadows' CRT
identification (`6^k`-resolution is exactly simultaneous `2^k`- and
`3^k`-resolution).  Its two faces: a silent sheet cut word (the 3-world's
absorption surviving its whole window) manufactures a silent 2-world
tower value; a silent deep-class power manufactures one too.  Combined
with Postulate I — no silent tower values from index two on — both
worlds' absorption trees are empty, and the fire is transported from the
2-world's law into the 3-world's powers. -/
structure CardinalWorldsMirrorBridge where
  wave : ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
    hasTernaryTwo (omegaCutWord s core) = false →
    ∃ j : Nat, 2 ≤ j ∧ hasTernaryTwo (d j) = false
  deep : ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
    hasTernaryTwo (4^a) = false →
    ∃ j : Nat, 2 ≤ j ∧ hasTernaryTwo (d j) = false

/-- **THE WAVE TRANSPORT.**  Postulate I + the mirror bridge kill every
silent sheet cut word: a silent cut word would manufacture a silent
2-world tower value, and Postulate I forbids silent tower values from
index two on. -/
theorem hWave_of_postulateI_mirror
    (hPI : ∀ j : Nat, 2 ≤ j → hasTernaryTwo (d j) = true)
    (hM : CardinalWorldsMirrorBridge) :
    ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
      hasTernaryTwo (omegaCutWord s core) = true := by
  intro s core hs hc h3
  by_contra h
  have hf : hasTernaryTwo (omegaCutWord s core) = false := by
    cases hbb : hasTernaryTwo (omegaCutWord s core) with
    | false => rfl
    | true => exact absurd hbb h
  obtain ⟨j, hj, hdj⟩ := hM.wave s core hs hc h3 hf
  rw [hPI j hj] at hdj
  exact Bool.noConfusion hdj

/-- **THE DEEP-CLASS TRANSPORT.**  Postulate I + the mirror bridge kill
every silent deep-class power: `4^a` silent would manufacture a silent
2-world tower value, and Postulate I forbids them. -/
theorem hS0_of_postulateI_mirror
    (hPI : ∀ j : Nat, 2 ≤ j → hasTernaryTwo (d j) = true)
    (hM : CardinalWorldsMirrorBridge) :
    ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
      hasTernaryTwo (4^a) = true := by
  intro a ha h3 hclass
  by_contra h
  have hf : hasTernaryTwo (4^a) = false := by
    cases hbb : hasTernaryTwo (4^a) with
    | false => rfl
    | true => exact absurd hbb h
  obtain ⟨j, hj, hdj⟩ := hM.deep a ha h3 hclass hf
  rw [hPI j hj] at hdj
  exact Bool.noConfusion hdj

/-- **THE LAW-PROMOTION — `hTailF` as a THEOREM of the granted laws.**
The hypothesis `hTailF` — the nine-clause second-observer conditional —
is consumed in full: the boundary is now the two cardinal-worlds laws
the directive names, Postulate I (the 2-world signature law) and the
absorption-mirror bridge (the worlds' combination).  Postulate II is
nowhere. -/
theorem four_power_omega_shadow_wave_tailF_of_postulateI
    (hPI : ∀ j : Nat, 2 ≤ j → hasTernaryTwo (d j) = true)
    (hM : CardinalWorldsMirrorBridge) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  four_power_omega_shadow_wave_tailF_of_slices
    (hWave_of_postulateI_mirror hPI hM)
    (hS0_of_postulateI_mirror hPI hM)

/-- **THE CROWN UNDER THE GRANTED LAWS** — the even-exponent Erdős
statement as a theorem of Postulate I + the mirror bridge. -/
theorem erdos_even_conjecture_of_postulateI
    (hPI : ∀ j : Nat, 2 ≤ j → hasTernaryTwo (d j) = true)
    (hM : CardinalWorldsMirrorBridge) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_of_slices
    (hWave_of_postulateI_mirror hPI hM)
    (hS0_of_postulateI_mirror hPI hM)

/-! ## §9 Receipts -/

#print axioms two_mul_cantor_kill
#print axioms two_mul_cantor_kill_all
#print axioms d_recurrence
#print axioms d_mod3_parity
#print axioms d_mod9_cycle
#print axioms postulate_I_fire_outside_deep
#print axioms cardinal_worlds_mirror
#print axioms cut_shift_general
#print axioms cut_shift_s0
#print axioms sheet_decompose
#print axioms s0_premise_full_clean
#print axioms four_power_omega_shadow_wave_tailF_of_slices
#print axioms erdos_even_of_slices
#print axioms erdos_even_conjecture_of_slices
#print axioms lteCoeff_has_two
#print axioms four_pow_mul_d
#print axioms hWave_of_postulateI_mirror
#print axioms hS0_of_postulateI_mirror
#print axioms four_power_omega_shadow_wave_tailF_of_postulateI
#print axioms erdos_even_conjecture_of_postulateI

end GSTCardinalWorldsBridge
