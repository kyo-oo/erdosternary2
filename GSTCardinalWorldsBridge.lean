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
    rw [show (4:Nat) = 2^2 from by decide, ← Nat.pow_mul]
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

/-! ## §10 THE DEEP AUDIT — the 2-world law's machine frontier

The deep classes `j ≡ 1, 5 (mod 6)` have no fixed mod-`3^k` window
(§11 proves this structurally: two geometric-series obstruction
families stay silent at every scale).  But the window `3^7 = 2187`
kills every deep class outside an explicit list of 64 residue classes
modulo `1458 = 2·3^6` (in `e = j + 2` space).  This is the 2-world
twin of the 3-world's machine audit: the two cardinal worlds' deep
audits now stand side by side — the mirror's empirical face on both
sides. -/

/-- **The window-`3^7` residue of the d-tower.**  For every `j ≥ 3`,
`d j % 2187 = deepRes ((j+2) % 1458)` (theorem `d_mod_deepRes`): the
first seven trits of `d j` are the seven trits of the 3-adic residue
`-2^-(j+2)`. -/
def deepRes (e : Nat) : Nat := (2186 * 2^(1458 - e % 1458)) % 2187

/-- The 64 surviving residue classes of the deep audit, in `e = j+2`
space modulo `1458`.  Every other residue class of every `j ≥ 2`
fires in the `3^7` window. -/
def d7mem : Nat → Bool
  | 1 => true
  | 3 => true
  | 57 => true
  | 79 => true
  | 81 => true
  | 93 => true
  | 117 => true
  | 163 => true
  | 169 => true
  | 181 => true
  | 235 => true
  | 241 => true
  | 243 => true
  | 255 => true
  | 309 => true
  | 331 => true
  | 333 => true
  | 343 => true
  | 351 => true
  | 397 => true
  | 487 => true
  | 489 => true
  | 511 => true
  | 513 => true
  | 541 => true
  | 543 => true
  | 565 => true
  | 603 => true
  | 649 => true
  | 657 => true
  | 673 => true
  | 703 => true
  | 705 => true
  | 709 => true
  | 721 => true
  | 727 => true
  | 729 => true
  | 741 => true
  | 795 => true
  | 813 => true
  | 871 => true
  | 883 => true
  | 927 => true
  | 957 => true
  | 997 => true
  | 999 => true
  | 1027 => true
  | 1053 => true
  | 1065 => true
  | 1141 => true
  | 1143 => true
  | 1153 => true
  | 1159 => true
  | 1189 => true
  | 1191 => true
  | 1195 => true
  | 1299 => true
  | 1303 => true
  | 1305 => true
  | 1315 => true
  | 1323 => true
  | 1357 => true
  | 1413 => true
  | 1443 => true
  | _ => false

/-- The audit cell: a residue passes if it is not deep, or it is a
listed survivor, or its `3^7` window fires. -/
def auditCell (e : Nat) : Bool :=
  if e % 6 = 1 ∨ e % 6 = 3 then
    (if d7mem e then true else hasTernaryTwoStruct (deepRes e) 7)
  else true

theorem audit_chunk0 : (List.range 486).all auditCell = true := by decide
theorem audit_chunk1 : (List.range 486).all (fun e => auditCell (486 + e)) = true := by decide
theorem audit_chunk2 : (List.range 486).all (fun e => auditCell (972 + e)) = true := by decide

theorem audit_all (e : Nat) (he : e < 1458) : auditCell e = true := by
  rcases Nat.lt_or_ge e 486 with h | h
  · exact List.all_eq_true.mp audit_chunk0 e (List.mem_range.mpr h)
  · rcases Nat.lt_or_ge e 972 with h2 | h2
    · have hmem := List.all_eq_true.mp audit_chunk1 (e - 486)
        (List.mem_range.mpr (by omega))
      rw [show e = 486 + (e - 486) from by omega]
      exact hmem
    · have hmem := List.all_eq_true.mp audit_chunk2 (e - 972)
        (List.mem_range.mpr (by omega))
      rw [show e = 972 + (e - 972) from by omega]
      exact hmem

/-- **The fire bridge**: a structural fire at any window depth is a
fire of the real predicate. -/
theorem hasTernaryTwoStruct_fire (n k : Nat)
    (h : hasTernaryTwoStruct n k = true) : hasTernaryTwo n = true := by
  induction k generalizing n with
  | zero => simp [hasTernaryTwoStruct] at h
  | succ k ih =>
    by_cases hn : n = 0
    · simp [hasTernaryTwoStruct, hn] at h
    · by_cases h2 : n % 3 = 2
      · rw [hasTernaryTwo.eq_def n, if_neg hn, if_pos h2]
      · rw [hasTernaryTwo.eq_def n, if_neg hn, if_neg h2]
        simp [hasTernaryTwoStruct, hn, h2] at h
        exact ih (n / 3) h

theorem mod1458_mod6 (a : Nat) : a % 1458 % 6 = a % 6 := by
  have h : (1458 * (a / 1458) + a % 1458) % 6 = a % 6 := by
    rw [Nat.div_add_mod a 1458]
  rw [Nat.add_mod, Nat.mul_mod, show (1458:Nat) % 6 = 0 from by decide,
      Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod] at h
  exact h

theorem audit_fire (e : Nat) (h6 : e % 6 = 1 ∨ e % 6 = 3)
    (hD : d7mem e = false) (ha : auditCell e = true) :
    hasTernaryTwoStruct (deepRes e) 7 = true := by
  unfold auditCell at ha
  rcases h6 with h | h
  · rw [if_pos (Or.inl h),
        if_neg (by intro h'; rw [h'] at hD; exact Bool.noConfusion hD)] at ha
    exact ha
  · rw [if_pos (Or.inr h),
        if_neg (by intro h'; rw [h'] at hD; exact Bool.noConfusion hD)] at ha
    exact ha

/-- **The 2-world period law**: `2^(2·3^k) ≡ 1 (mod 3^(k+1))` — the
engine of every window reduction (Euler's `φ(3^m) = 2·3^(m-1)` in
induction form: the cube of a `1 mod 3^k` unit is `1 mod 3^(k+1)`). -/
theorem two_pow_cycle : ∀ k : Nat, (2^(2 * 3^k)) % (3^(k+1)) = 1 := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have hsplit : 2 * 3^(k+1) = (2 * 3^k) * 3 := by rw [Nat.pow_succ]; ring
    have hexp : 2^(2 * 3^(k+1)) = (2^(2 * 3^k))^3 := by rw [hsplit, Nat.pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, 2^(2 * 3^k) = 3^(k+1) * m + 1 := by
      have hdm := Nat.div_add_mod (2^(2 * 3^k)) (3^(k+1))
      rw [ih] at hdm
      exact ⟨_, hdm.symm⟩
    have hcube : (3^(k+1) * m + 1)^3
        = 1 + 3^(k+2) * (m + 3^(k+1) * m^2 + 3^(2*k+1) * m^3) := by
      rw [show 3^(k+2) = 3^k * 9 from by rw [Nat.pow_add],
          show 3^(k+1) = 3^k * 3 from by rw [Nat.pow_succ],
          show 3^(2*k+1) = (3^k)^2 * 3 from by
            rw [show 2*k+1 = k*2+1 from by ring, Nat.pow_add, Nat.pow_mul,
                Nat.pow_one]]
      ring
    have h1lt2 : 1 < 3^(k+2) := by
      have hp : 0 < 3^k := Nat.pow_pos (by decide : 0 < 3)
      have h9 : (3:Nat)^(k+2) = 3^k * 9 := by rw [Nat.pow_add]
      omega
    rw [hexp, hm, hcube, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd
          ⟨m + 3^(k+1) * m^2 + 3^(2*k+1) * m^3, rfl⟩,
        Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt h1lt2]

theorem two_pow_per_base : 2^1458 % 2187 = 1 := by
  have h := two_pow_cycle 6
  rw [show (2:Nat) * 3^6 = 1458 from by decide,
      show (6:Nat) + 1 = 7 from by decide,
      show (3:Nat)^7 = 2187 from by decide] at h
  exact h

theorem two_pow_per_mod (q : Nat) : (2^(1458 * q)) % 2187 = 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
    have h : 1458 * (q + 1) = 1458 * q + 1458 := by omega
    rw [h, Nat.pow_add, Nat.mul_mod, ih, two_pow_per_base, Nat.one_mul,
        Nat.mod_eq_of_lt (show (1:Nat) < 2187 by decide)]

theorem two_pow_mod_per (n : Nat) : 2^n % 2187 = 2^(n % 1458) % 2187 := by
  have hn : n = 1458 * (n / 1458) + n % 1458 := (Nat.div_add_mod n 1458).symm
  have hmod : (1458 * (n / 1458) + n % 1458) % 1458 = n % 1458 := by omega
  rw [hn, Nat.pow_add, Nat.mul_mod, two_pow_per_mod, Nat.one_mul, Nat.mod_mod,
      hmod]

/-- **The window law**: `2^(j+2)·d j ≡ -1 (mod 3^k)` whenever `k ≤ 2^j`. -/
theorem d_window (j k : Nat) (hj : 1 ≤ j) (hk : k ≤ 2^j) :
    (2^(j+2) * d j) % 3^k = 3^k - 1 := by
  have hid := d_identity j hj
  have hdvd : 3^k ∣ 3^(2^j) := by
    refine ⟨3^(2^j - k), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  obtain ⟨w, hw⟩ := hdvd
  have hpos : 0 < 3^(2^j) := Nat.pow_pos (by decide : 0 < 3)
  rcases w with _ | w'
  · omega
  · rw [hid, hw]
    have hp3 : 0 < 3^k := Nat.pow_pos (by decide : 0 < 3)
    have hexp : 3^k * (w'+1) - 1 = 3^k * w' + (3^k - 1) := by
      have h1 : 3^k * (w'+1) = 3^k * w' + 3^k := by ring
      rw [h1]
      generalize hP : 3^k * w' = P
      omega
    have h0 : 3^k * w' % 3^k = 0 := Nat.mod_eq_zero_of_dvd ⟨w', by ring⟩
    have hlt : 3^k - 1 < 3^k := by
      have hp : 0 < 3^k := Nat.pow_pos (by decide : 0 < 3)
      omega
    rw [hexp, Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]

/-- **The window reduction.**  For every `j ≥ 3` the first seven
trits of `d j` are the trits of `deepRes ((j+2) % 1458)`: the `3^7`
window of the d-tower depends only on `j mod 1458`. -/
theorem d_mod_deepRes (j : Nat) (hj : 3 ≤ j) :
    d j % 2187 = deepRes ((j+2) % 1458) := by
  have h8 : (2:Nat)^3 ≤ 2^j := by
    have hsplit : 2^j = (2:Nat)^3 * 2^(j-3) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hpos : 0 < 2^(j-3) := Nat.pow_pos (by decide : 0 < 2)
    rw [hsplit, show (2:Nat)^3 = 8 from by decide]
    omega
  have hwin : (2^(j+2) * d j) % 2187 = 2186 := by
    have h8v : (2:Nat)^3 = 8 := by decide
    rw [h8v] at h8
    have h := d_window j 7 (by omega) (by omega)
    rw [show (3:Nat)^7 = 2187 from by decide,
        show (2187:Nat) - 1 = 2186 from by decide] at h
    exact h
  have hper := two_pow_mod_per (j+2)
  have htlt : (j+2) % 1458 < 1458 := Nat.mod_lt (j+2) (show 0 < 1458 by decide)
  have hinv : (2^((j+2) % 1458) * 2^(1458 - (j+2) % 1458)) % 2187 = 1 := by
    have hexp : 2^((j+2) % 1458) * 2^(1458 - (j+2) % 1458)
        = 2^(1458 * ((j+2) % 1458 / 1458 + 1)) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hexp, two_pow_per_mod]
  have hstep1 : (2^(j+2) * d j * 2^(1458 - (j+2) % 1458)) % 2187
      = (2186 * 2^(1458 - (j+2) % 1458)) % 2187 := by
    rw [show (2^(j+2) * d j * 2^(1458 - (j+2) % 1458)) % 2187
          = ((2^(j+2) * d j) % 2187 * (2^(1458 - (j+2) % 1458) % 2187)) % 2187
          from Nat.mul_mod _ _ _,
        show (2186 * 2^(1458 - (j+2) % 1458)) % 2187
          = (2186 % 2187 * (2^(1458 - (j+2) % 1458) % 2187)) % 2187
          from Nat.mul_mod _ _ _,
        hwin, Nat.mod_eq_of_lt (show 2186 < 2187 by decide)]
  have hstep2 : (2^(j+2) * d j * 2^(1458 - (j+2) % 1458)) % 2187 = d j % 2187 := by
    have hreg : 2^(j+2) * d j * 2^(1458 - (j+2) % 1458)
        = (2^(j+2) * 2^(1458 - (j+2) % 1458)) * d j := by ring
    rw [hreg,
        show ((2^(j+2) * 2^(1458 - (j+2) % 1458)) * d j) % 2187
          = ((2^(j+2) * 2^(1458 - (j+2) % 1458)) % 2187 * (d j % 2187)) % 2187
          from Nat.mul_mod _ _ _]
    have hprod : (2^(j+2) * 2^(1458 - (j+2) % 1458)) % 2187 = 1 := by
      rw [show (2^(j+2) * 2^(1458 - (j+2) % 1458)) % 2187
            = ((2^(j+2)) % 2187 * (2^(1458 - (j+2) % 1458) % 2187)) % 2187
            from Nat.mul_mod _ _ _,
          hper, ← Nat.mul_mod, hinv]
    rw [hprod, Nat.one_mul, Nat.mod_mod]
  rw [← hstep2, hstep1]
  unfold deepRes
  rw [Nat.mod_mod]

/-- **THE DEEP AUDIT — Postulate I at 95.6%.**  The signature law of
the 2-world holds for every `j ≥ 2` outside the 64 residue classes of
`d7mem` (in `e = j+2` space mod 1458): the `3^7` window kills every
deep class not in the survivor list, and the six-cycle kills every
shallow class.  The 64 survivors are the fractal boundary of §11. -/
theorem postulate_I_outside_D7 (j : Nat) (hj : 2 ≤ j)
    (hD : d7mem ((j+2) % 1458) = false) :
    hasTernaryTwo (d j) = true := by
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · have hj2 : j = 2 := by omega
    have hd2 : d 2 = 5 := by decide
    rw [hj2, hd2]
    exact hasTernaryTwoStruct_fire 5 2 (by decide)
  · by_cases hsix : j % 6 = 1 ∨ j % 6 = 5
    · have hres := d_mod_deepRes j h3
      have ha := audit_all ((j+2) % 1458)
        (Nat.mod_lt (j+2) (show 0 < 1458 by decide))
      have h6 : ((j+2) % 1458) % 6 = 1 ∨ ((j+2) % 1458) % 6 = 3 := by
        rw [mod1458_mod6]
        rcases hsix with h | h
        · omega
        · omega
      have hfire := audit_fire ((j+2) % 1458) h6 hD ha
      have hreal := hasTernaryTwoStruct_fire _ _ hfire
      rw [← hres] at hreal
      exact mod_has_two 7 (d j) (by
        rw [show (3:Nat)^7 = 2187 from by decide]; exact hreal)
    · have hcyc := d_mod9_cycle j h3
      have hfire9 : hasTernaryTwo (d j % 9) = true := by
        by_cases h0 : j % 6 = 0
        · rw [hcyc.1 h0]
          exact hasTernaryTwoStruct_fire 2 2 (by decide)
        · by_cases h2 : j % 6 = 2
          · rw [hcyc.2.2.1 h2]
            exact hasTernaryTwoStruct_fire 5 2 (by decide)
          · by_cases h3' : j % 6 = 3
            · rw [hcyc.2.2.2.1 h3']
              exact hasTernaryTwoStruct_fire 7 2 (by decide)
            · by_cases h4 : j % 6 = 4
              · rw [hcyc.2.2.2.2.1 h4]
                exact hasTernaryTwoStruct_fire 8 2 (by decide)
              · exfalso
                exact hsix (by omega)
      exact mod_has_two 2 (d j) (by
        rw [show (3:Nat)^2 = 9 from by decide]; exact hfire9)

/-! ## §11 THE FRACTAL BOUNDARY — the two geometric-series obstructions

The two obstruction families: the all-ones word `(3^k-1)/2` (the
geometric series `Σ 3^i`, ratio 3) at indices `j = 2·3^(k-1) - 1`,
and the alternating word (ratio 9) at indices `j = 2·3^(k-1) + 1`.
At every window scale `3^k` these two deep-class indices have
PROVABLY silent windows: no fixed window can ever close the law.
The boundary is fractal — this is its shape. -/

theorem three_pow_odd : ∀ k : Nat, 3^k % 2 = 1 := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, show (3:Nat) % 2 = 1 from by decide,
        Nat.mul_one, Nat.mod_mod, ih]

/-- The 2-cancellation (an explicit inverse: `2 · (3^k+1)/2 ≡ 1`). -/
theorem cancel_two_3pow (k X Y : Nat) (hk : 1 ≤ k)
    (h : (2 * X) % 3^k = (2 * Y) % 3^k) : X % 3^k = Y % 3^k := by
  have hOdd : 3^k % 2 = 1 := three_pow_odd k
  have hEven : (3^k + 1) % 2 = 0 := by omega
  have hmul : 2 * ((3^k + 1) / 2) = 3^k + 1 := by
    have hdm := Nat.div_add_mod (3^k + 1) 2
    omega
  have h3k : 3^k = 3^(k-1) * 3 := by
    have h := Nat.pow_succ 3 (k-1)
    rw [show Nat.succ (k-1) = k from by omega] at h
    exact h
  have hpe : 0 < 3^(k-1) := Nat.pow_pos (by decide : 0 < 3)
  have h1lt : 1 < 3^k := by omega
  have hinv : (2 * ((3^k + 1) / 2)) % 3^k = 1 := by
    rw [hmul, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt h1lt]
  have hL : ((2 * X) * ((3^k + 1) / 2)) % 3^k = X % 3^k := by
    rw [show (2 * X) * ((3^k + 1) / 2) = X * (2 * ((3^k + 1) / 2)) from by ring,
        Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod]
  have hR : ((2 * Y) * ((3^k + 1) / 2)) % 3^k = Y % 3^k := by
    rw [show (2 * Y) * ((3^k + 1) / 2) = Y * (2 * ((3^k + 1) / 2)) from by ring,
        Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod]
  have hLX := Nat.mul_mod (2 * X) ((3^k + 1) / 2) (3^k)
  have hLY := Nat.mul_mod (2 * Y) ((3^k + 1) / 2) (3^k)
  rw [← hL, ← hR, hLX, hLY, h]

/-- `hasTernaryTwo 1 = false` — the one-word is silent. -/
theorem hasTernaryTwo_one : hasTernaryTwo 1 = false := by
  rw [hasTernaryTwo.eq_def 1, if_neg (by decide : (1:Nat) ≠ 0),
      if_neg (by decide : ¬((1:Nat) % 3 = 2)),
      show (1:Nat) / 3 = 0 from by decide, hasTernaryTwo_zero_lemma]

/-- **The silent bridge**: a structural silence at window depth `k`
for a value below `3^k` is a silence of the real predicate. -/
theorem hasTernaryTwoStruct_silent (n k : Nat) (hn : n < 3^k)
    (h : hasTernaryTwoStruct n k = false) : hasTernaryTwo n = false := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by rw [Nat.pow_zero] at hn; omega
    rw [hn0, hasTernaryTwo.eq_def 0, if_pos rfl]
  | succ k ih =>
    by_cases hn0 : n = 0
    · rw [hn0, hasTernaryTwo.eq_def 0, if_pos rfl]
    · by_cases h2 : n % 3 = 2
      · exfalso
        simp [hasTernaryTwoStruct, hn0, h2] at h
      · rw [hasTernaryTwo.eq_def n, if_neg hn0, if_neg h2]
        have hs : hasTernaryTwoStruct (n / 3) k = false := by
          simp [hasTernaryTwoStruct, hn0, h2] at h
          exact h
        have hnd : n / 3 < 3^k := by
          have hnp : 3^(k+1) = 3 * 3^k := by rw [Nat.pow_succ]; ring
          rw [hnp] at hn
          omega
        exact ih (n / 3) hnd hs

/-- The all-ones word is silent (the geometric series has trits 1). -/
theorem all_ones_silent : ∀ k : Nat, hasTernaryTwo ((3^(k+1) - 1) / 2) = false := by
  intro k
  induction k with
  | zero =>
    rw [show ((3:Nat)^(0+1) - 1) / 2 = 1 from by decide]
    exact hasTernaryTwo_one
  | succ k ih =>
    have hOdd : 3^(k+1) % 2 = 1 := three_pow_odd (k+1)
    have hp : (3:Nat)^(k+2) = 3 * 3^(k+1) := by
      rw [show k+2 = (k+1)+1 from by omega, Nat.pow_succ]; ring
    have hid : (3^(k+2) - 1) / 2 = 3^(k+1) + (3^(k+1) - 1) / 2 := by
      omega
    rw [hid]
    have hX3 : ((3^(k+1) - 1) / 2) % 3 = 1 := by
      have h2X : 2 * ((3^(k+1) - 1) / 2) = 3^(k+1) - 1 := by
        have hdm := Nat.div_add_mod (3^(k+1) - 1) 2
        have hOdd' : (3^(k+1) - 1) % 2 = 0 := by omega
        omega
      have hmod : (3^(k+1) - 1) % 3 = 2 := by
        have h3m : 3^(k+1) % 3 = 0 := by
          rw [show (3:Nat)^(k+1) = 3^k * 3 from by rw [Nat.pow_succ],
              Nat.mod_eq_zero_of_dvd ⟨3^k, by ring⟩]
        have hdm := Nat.div_add_mod (3^(k+1) - 1) 3
        have hpos : 0 < 3^(k+1) := Nat.pow_pos (by decide : 0 < 3)
        omega
      have hmulmod : (2 * ((3^(k+1) - 1) / 2)) % 3
          = (2 % 3 * (((3^(k+1) - 1) / 2) % 3)) % 3 := Nat.mul_mod _ _ _
      rw [h2X, hmod] at hmulmod
      omega
    have h3m : 3^(k+1) % 3 = 0 := by
      rw [show (3:Nat)^(k+1) = 3^k * 3 from by rw [Nat.pow_succ],
          Nat.mod_eq_zero_of_dvd ⟨3^k, by ring⟩]
    rw [hasTernaryTwo.eq_def (3^(k+1) + (3^(k+1) - 1) / 2),
        if_neg (by
          have hpos : 0 < 3^(k+1) := Nat.pow_pos (by decide : 0 < 3)
          omega),
        if_neg (by rw [Nat.add_mod, h3m, Nat.zero_add]; omega)]
    rw [show (3^(k+1) + (3^(k+1) - 1) / 2) / 3 = (3^(k+1) - 1) / 2 from by
      have hOdd' : 3^(k+1) % 2 = 1 := three_pow_odd (k+1)
      omega]
    exact ih

theorem two_pow_self_ge : ∀ n : Nat, n < 2^n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
    rw [Nat.pow_succ]
    omega

theorem three_pow_ge_self : ∀ k : Nat, 1 ≤ k → k ≤ 3^(k-1) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    by_cases hk1 : k = 0
    · rw [hk1]; decide
    · have hk1' : 1 ≤ k := by omega
      have ih' := ih hk1'
      have h3k : 3^k = 3^(k-1) * 3 := by
        have h := Nat.pow_succ 3 (k-1)
        rw [show Nat.succ (k-1) = k from by omega] at h
        exact h
      rw [show k + 1 - 1 = k from by omega]
      omega

/-- **The all-ones obstruction family.**  At index `j = 2·3^(k-1) - 1`
the window `3^k` of `d j` is the all-ones word — silent at every
scale. -/
theorem gp_ones_window (k : Nat) (hk : 1 ≤ k) :
    d (2*3^(k-1) - 1) % 3^k = (3^k - 1) / 2 := by
  have hge : 1 ≤ 2*3^(k-1) - 1 := by
    have h : 0 < 3^(k-1) := Nat.pow_pos (by decide : 0 < 3)
    omega
  have hkb : k ≤ 2^(2*3^(k-1) - 1) := by
    have hle : k ≤ 2*3^(k-1) - 1 := by
      have h3 := three_pow_ge_self k hk
      have hpe : 0 < 3^(k-1) := Nat.pow_pos (by decide : 0 < 3)
      omega
    have hlt := two_pow_self_ge (2*3^(k-1) - 1)
    omega
  have hwin := d_window (2*3^(k-1) - 1) k hge hkb
  have h3k : 3^k = 3^(k-1) * 3 := by
    have h := Nat.pow_succ 3 (k-1)
    rw [show Nat.succ (k-1) = k from by omega] at h
    exact h
  have hpe : 0 < 3^(k-1) := Nat.pow_pos (by decide : 0 < 3)
  have h2lt : 2 < 3^k := by omega
  have h2mod : 2^(2*3^(k-1) - 1 + 2) % 3^k = 2 := by
    have hcyc := two_pow_cycle (k-1)
    rw [show (k:Nat) - 1 + 1 = k from by omega] at hcyc
    have hexp : 2^(2*3^(k-1) - 1 + 2) = 2 * 2^(2*3^(k-1)) := by
      have h1 : 2^(2*3^(k-1) - 1 + 2) = 2^((2*3^(k-1)) + 1) := by
        congr 1; omega
      have h2 : 2^((2*3^(k-1)) + 1) = 2 * 2^(2*3^(k-1)) := by
        rw [Nat.pow_succ]; ring
      rw [h1, h2]
    rw [hexp, Nat.mul_mod, hcyc, Nat.mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt h2lt]
  -- (2 · d j) ≡ 3^k - 1 (mod 3^k), by the periodicity of 2^(j+2)
  have hL : (2 * d (2*3^(k-1) - 1)) % 3^k = 3^k - 1 := by
    have hsplit2 := Nat.mul_mod (2^(2*3^(k-1) - 1 + 2)) (d (2*3^(k-1) - 1)) (3^k)
    rw [hsplit2, h2mod] at hwin
    have hsplit := Nat.mul_mod (2) (d (2*3^(k-1) - 1)) (3^k)
    rw [hsplit, Nat.mod_eq_of_lt h2lt]
    exact hwin
  have hR : (2 * ((3^k - 1) / 2)) % 3^k = 3^k - 1 := by
    have hOdd : 3^k % 2 = 1 := three_pow_odd k
    have h2X : 2 * ((3^k - 1) / 2) = 3^k - 1 := by
      have hdm := Nat.div_add_mod (3^k - 1) 2
      have hOdd' : (3^k - 1) % 2 = 0 := by omega
      omega
    rw [h2X, Nat.mod_eq_of_lt (show 3^k - 1 < 3^k by
      have hp : 0 < 3^k := Nat.pow_pos (by decide : 0 < 3)
      omega)]
  have hlt2 : (3^k - 1) / 2 < 3^k := by
    have hdm := Nat.div_add_mod (3^k - 1) 2
    have hOdd : 3^k % 2 = 1 := three_pow_odd k
    have hOdd' : (3^k - 1) % 2 = 0 := by omega
    have hp : 0 < 3^k := Nat.pow_pos (by decide : 0 < 3)
    omega
  have hcancel := cancel_two_3pow k (d (2*3^(k-1) - 1)) ((3^k - 1) / 2) hk
    (hL.trans hR.symm)
  rw [Nat.mod_eq_of_lt hlt2] at hcancel
  exact hcancel

/-- The all-ones word `(3^k - 1) / 2` is silent — every trit is 1. -/
theorem gp_ones_silent (k : Nat) (hk : 1 ≤ k) :
    hasTernaryTwo ((3^k - 1) / 2) = false := by
  have h := all_ones_silent (k-1)
  rw [show (3:Nat)^((k-1)+1) = 3^k from by congr 1; omega] at h
  exact h

/-- **The alternating witness at the audit's own scale.**  The residue
`e = 489` (the class of `j = 487`, the `+1` side of the obstruction
pair at window `3^7`) is the alternating word `010101₃` — silent. -/
theorem gp_alt_residue_silent : hasTernaryTwo (deepRes 489) = false := by
  have hlt : deepRes 489 < 3^7 := by
    rw [show (3:Nat)^7 = 2187 from by decide]
    unfold deepRes
    exact Nat.mod_lt _ (show 0 < 2187 by decide)
  exact hasTernaryTwoStruct_silent (deepRes 489) 7 hlt (by decide)

/-- **NO FIXED WINDOW CLOSES THE LAW.**  At every window scale `3^k`
there is a deep-class index whose window is the silent all-ones word.
The boundary is fractal: window audits thin it — 64 survivors at
`3^7`, shrinking at every scale — but never empty it. -/
theorem no_fixed_window (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, 2 ≤ j ∧ hasTernaryTwo (d j % 3^k) = false := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk1 : k = 1 := by omega
    refine ⟨5, by decide, ?_⟩
    rw [hk1]
    have hd5 : d 5 % (3:Nat)^1 = 1 := by decide
    rw [hd5]
    exact hasTernaryTwo_one
  · refine ⟨2*3^(k-1) - 1, ?_, ?_⟩
    · have h3 := three_pow_ge_self k hk
      omega
    · rw [gp_ones_window k hk]
      exact gp_ones_silent k hk

/-! ## §12 Receipts — the deep audit and the fractal boundary -/

#print axioms audit_chunk0
#print axioms audit_chunk1
#print axioms audit_chunk2
#print axioms audit_all
#print axioms hasTernaryTwoStruct_fire
#print axioms audit_fire
#print axioms two_pow_cycle
#print axioms two_pow_mod_per
#print axioms d_window
#print axioms d_mod_deepRes
#print axioms postulate_I_outside_D7
#print axioms cancel_two_3pow
#print axioms all_ones_silent
#print axioms gp_ones_window
#print axioms gp_ones_silent
#print axioms gp_alt_residue_silent
#print axioms no_fixed_window

/-! ## §13 THE HALF-TURN COMPLEMENT ROTATION — LAW 1 CLOSED

The signature law of the 2-world, promoted from grant to THEOREM.  For
`j ≥ 2` write `N := 2^j`, `Q := 2^(j+2)`, `M := 3^N - 1`, so
`Q * d j = M` (`d_identity`), and let `H := N/2 = 2^(j-1)` be the
half-turn.  Two descriptions of the same transformation:

* ARITHMETIC: `3^H ≡ 1 + Q/2 (mod Q)` (2-adic LTE at exact valuation
  `j+1`), so `(3^H * d j) % M = d j + M/2` — the digitwise complement.
* GEOMETRY: mod `M`, multiplication by `3^H` rotates the `N`-trit
  cylinder by half a turn — a `{0,1}`-word stays a `{0,1}`-word.

A silent `d j` would make the SAME integer both `{0,1}`-only and
signature-carrying.  Contradiction.  No finite window audit, no
surviving phase set, no additional postulate. -/

/-- Bounded-coefficient ternary sums stay below the next power. -/
theorem htc_sum_lt (c : Nat → Nat) : ∀ k : Nat, (∀ i, i < k → c i < 3) →
    Finset.sum (Finset.range k) (fun i => c i * 3^i) < 3^k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hc
    rw [Finset.sum_range_succ, Nat.pow_succ]
    have hck : c k < 3 := hc k (by omega)
    have hle : c k * 3^k ≤ 2 * 3^k := Nat.mul_le_mul (by omega : c k ≤ 2) (Nat.le_refl _)
    have hlt := ih (fun i hi => hc i (by omega))
    have h3 : (0:Nat) < 3^k := three_pow_pos' k
    omega

/-- Digit extraction from bounded-coefficient ternary sums. -/
theorem htc_digit_of_sum (c : Nat → Nat) : ∀ k : Nat, (∀ i, i < k → c i < 3) →
    ∀ p, p < k → (Finset.sum (Finset.range k) (fun i => c i * 3^i) / 3^p) % 3 = c p := by
  intro k
  induction k with
  | zero => intro _ p hp; omega
  | succ k ih =>
    intro hc p hp
    have hck : c k < 3 := hc k (by omega)
    have h3p : (0:Nat) < 3^p := three_pow_pos' p
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge p k with hlt | hge
    · have hsh : c k * 3^k = 3^p * (c k * 3^(k - p)) := by
        have hpow : 3^k = 3^p * 3^(k - p) := by rw [← Nat.pow_add]; congr 1; omega
        rw [hpow]; ring
      rw [hsh, Nat.add_mul_div_left _ _ h3p, Nat.add_mod]
      have hih := ih (fun i hi => hc i (by omega)) p hlt
      rw [hih]
      have hz : (c k * 3^(k - p)) % 3 = 0 := by
        rw [show 3^(k - p) = 3^(k - p - 1) * 3 from by rw [← Nat.pow_succ]; congr 1; omega,
            show c k * (3^(k - p - 1) * 3) = (c k * 3^(k - p - 1)) * 3 from by ring,
            Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
      have hcp : c p < 3 := hc p hp
      rw [hz, Nat.add_zero, Nat.mod_eq_of_lt hcp]
    · have hpk : p = k := by omega
      rw [hpk]
      have hsltv : Finset.sum (Finset.range k) (fun i => c i * 3^i) < 3^k :=
        htc_sum_lt c k (fun i hi => hc i (by omega))
      have h3k : (0:Nat) < 3^k := three_pow_pos' k
      rw [Nat.add_mul_div_left _ _ h3k, Nat.div_eq_of_lt hsltv, Nat.zero_add,
          Nat.mod_eq_of_lt hck]

/-- The all-ones word as a sum: `∑_{i<k} 3^i = (3^k - 1) / 2`. -/
theorem htc_geom_sum (k : Nat) :
    Finset.sum (Finset.range k) (fun i => 3^i) = (3^k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hOdd : 3^(k+1) % 2 = 1 := three_pow_odd (k+1)
    have hp : 3^(k+1) = 3 * 3^k := three_pow_succ_mul k
    rw [ih]
    omega

/-- Digits of a residue below the modulus's power: for `i < N`, the
`i`-th trit of `x % 3^N` is the `i`-th trit of `x`. -/
theorem htc_mod_div_digit (x N i : Nat) (hi : i < N) :
    ((x % 3^N) / 3^i) % 3 = (x / 3^i) % 3 := by
  have hz : (3^(N - i) * (x / 3^N)) % 3 = 0 := by
    have hmul : 3^(N - i) * (x / 3^N) = (x / 3^N) * 3^(N - i - 1) * 3 := by
      rw [show 3^(N - i) = 3^(N - i - 1) * 3 from by rw [← Nat.pow_succ]; congr 1; omega]; ring
    rw [hmul, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
  have hsplit : x / 3^i = 3^(N - i) * (x / 3^N) + (x % 3^N) / 3^i := by
    have hxe : x = (x % 3^N) + 3^i * (3^(N - i) * (x / 3^N)) := by
      have hp : 3^N = 3^i * 3^(N - i) := by rw [← Nat.pow_add]; congr 1; omega
      calc x = 3^N * (x / 3^N) + x % 3^N := (Nat.div_add_mod x (3^N)).symm
        _ = (3^i * 3^(N - i)) * (x / 3^N) + x % 3^N := by rw [hp]
        _ = (x % 3^N) + 3^i * (3^(N - i) * (x / 3^N)) := by ring
    conv_lhs => rw [hxe]
    rw [Nat.add_mul_div_left _ _ (three_pow_pos' i)]
    ring
  conv_rhs => rw [hsplit, Nat.add_mod]
  rw [hz, Nat.zero_add, Nat.mod_mod]

/-- Every number below `3^k` is the sum of its trits. -/
theorem htc_digit_reconstruction (x k : Nat) : x < 3^k →
    x = Finset.sum (Finset.range k) (fun i => (x / 3^i) % 3 * 3^i) := by
  induction k generalizing x with
  | zero =>
    intro hx
    have h1 : (3:Nat)^0 = 1 := by decide
    have hx0 : x = 0 := by omega
    rw [hx0, Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    intro hx
    have h3k : (0:Nat) < 3^k := three_pow_pos' k
    have hq : x / 3^k < 3 :=
      div_lt_of_lt_mul' x (3^k) 3 h3k
        (show x < 3^k * 3 from by rw [show 3^k * 3 = 3^(k+1) from by rw [Nat.mul_comm, ← three_pow_succ_mul k]]; exact hx)
    have hr : x % 3^k < 3^k := Nat.mod_lt _ h3k
    have ihr := ih (x % 3^k) hr
    have hdigeq : ∀ i, i < k → ((x % 3^k) / 3^i) % 3 = (x / 3^i) % 3 :=
      fun i hi => htc_mod_div_digit x k i hi
    have hcongr : Finset.sum (Finset.range k) (fun i => ((x % 3^k) / 3^i) % 3 * 3^i)
        = Finset.sum (Finset.range k) (fun i => (x / 3^i) % 3 * 3^i) :=
      Finset.sum_congr rfl (fun i hi => by rw [hdigeq i (Finset.mem_range.mp hi)])
    rw [Finset.sum_range_succ]
    have hdm := Nat.div_add_mod x (3^k)
    calc x = 3^k * (x / 3^k) + x % 3^k := hdm.symm
      _ = 3^k * ((x / 3^k) % 3) + Finset.sum (Finset.range k) (fun i => ((x % 3^k) / 3^i) % 3 * 3^i) := by
          rw [Nat.mod_eq_of_lt hq, ← ihr]
      _ = Finset.sum (Finset.range k) (fun i => (x / 3^i) % 3 * 3^i) + (x / 3^k) % 3 * 3^k := by
          rw [hcongr]
          ring

/-- **THE HALF-TURN SPLIT LEMMA** — the geometric engine.  If `U` and
`V` are `{0,1}`-words below `3^H`, then `3^H * U + V` (the half-turn
rotation of the combined word) is again a `{0,1}`-word: silent. -/
theorem htc_half_turn_silent (H U V : Nat)
    (hUdig : ∀ p, p < H → (U / 3^p) % 3 ≠ 2)
    (hVdig : ∀ p, p < H → (V / 3^p) % 3 ≠ 2)
    (hUlt : U < 3^H) (hVlt : V < 3^H) :
    ∀ p, ((3^H * U + V) / 3^p) % 3 ≠ 2 := by
  intro p
  rcases Nat.lt_or_ge p H with hplt | hpge
  · have hv : (3^H * U + V) % 3^(p+1) = V % 3^(p+1) := by
      have hz : (3^H * U) % 3^(p+1) = 0 := by
        have hsplit : 3^H * U = 3^(p+1) * (3^(H - p - 1) * U) := by
          rw [show 3^H = 3^(p+1) * 3^(H - p - 1) from by rw [← Nat.pow_add]; congr 1; omega]
          ring
        rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [Nat.add_mod, hz, Nat.zero_add, Nat.mod_mod]
    have h1 : ((3^H * U + V) / 3^p) % 3 = ((3^H * U + V) % 3^(p+1)) / 3^p % 3 :=
      div_digit_window (3^H * U + V) (3^p) ((3^H * U + V) % 3^(p+1)) (three_pow_pos' p)
        (show (3^H * U + V) % 3^(p+1) < 3 * 3^p from by
          rw [show 3 * 3^p = 3^(p+1) from (three_pow_succ_mul p).symm]
          exact Nat.mod_lt _ (three_pow_pos' (p+1)))
        (show (3^H * U + V) % (3 * 3^p) = (3^H * U + V) % 3^(p+1) from by rw [three_pow_succ_mul p])
    have h2 : (V % 3^(p+1)) / 3^p % 3 = (V / 3^p) % 3 :=
      (div_digit_window V (3^p) (V % 3^(p+1)) (three_pow_pos' p)
        (show V % 3^(p+1) < 3 * 3^p from by
          rw [show 3 * 3^p = 3^(p+1) from (three_pow_succ_mul p).symm]
          exact Nat.mod_lt _ (three_pow_pos' (p+1)))
        (show V % (3 * 3^p) = V % 3^(p+1) from by rw [three_pow_succ_mul p])).symm
    rw [h1, hv, h2]
    exact hVdig p hplt
  · have hWH : (3^H * U + V) / 3^H = U := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (three_pow_pos' H), Nat.div_eq_of_lt hVlt,
          Nat.zero_add]
    have hsplit : (3^H * U + V) / 3^p = U / 3^(p - H) := by
      rw [show 3^p = 3^H * 3^(p - H) from by rw [← Nat.pow_add]; congr 1; omega,
          ← Nat.div_div_eq_div_mul, hWH]
    rw [hsplit]
    rcases Nat.lt_or_ge (p - H) H with h2 | h2
    · exact hUdig (p - H) h2
    · rw [Nat.div_eq_of_lt (by have hle := Nat.pow_le_pow_of_le (by decide : 1 < 3) h2; omega)]
      decide

/-- The 2-adic half-turn congruence, one square-lift step: LTE at the
exact valuation `v₂(3^(2^(j-1)) - 1) = j + 1`. -/
theorem half_turn_step (j : Nat) (hj : 2 ≤ j)
    (h : 3^(2^(j-1)) % 2^(j+2) = 1 + 2^(j+1)) :
    3^(2^(j+1-1)) % 2^(j+1+2) = 1 + 2^(j+1+1) := by
  have hpow : 3^(2^j) = 3^(2^(j-1)) * 3^(2^(j-1)) := by
    rw [show 2^j = 2^(j-1) + 2^(j-1) from by have := two_pow_factored j (by omega : 1 <= j); omega,
        Nat.pow_add]
  obtain ⟨q, hq⟩ : ∃ q : Nat, 3^(2^(j-1)) = 2^(j+2) * q + (1 + 2^(j+1)) :=
    ⟨3^(2^(j-1)) / 2^(j+2), by
      exact (Nat.div_add_mod (3^(2^(j-1))) (2^(j+2))).symm.trans (by rw [h])⟩
  have hlt : 1 + 2^(j+1+1) < 2^(j+1+2) := by
    have hd : 2^(j+1+2) = 2 * 2^(j+1+1) := by
      rw [show j+1+2 = (j+1+1)+1 from by omega, Nat.pow_succ]; ring
    have hpos := two_pow_pos (j+1+1)
    omega
  have ea : 2^(j+1) = 2 * 2 * 2^(j-1) := by
    rw [show j+1 = (j-1)+2 from by omega, Nat.pow_succ, Nat.pow_succ]
    ring
  have eb : 2^(j+2) = 2 * 2 * 2 * 2^(j-1) := by
    rw [show j+2 = (j-1)+3 from by omega, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
    ring
  have ec : 2^(j+1+2) = 2 * 2 * 2 * 2 * 2^(j-1) := by
    rw [show j+1+2 = (j-1)+4 from by omega, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
    ring
  have ed : 2^(j+1+1) = 2 * 2 * 2 * 2^(j-1) := by
    rw [show j+1+1 = j+2 from by omega]
    exact eb
  have hsq : 3^(2^j) = 2^(j+1+2) * (2^(j+1) * q * q + q * (1 + 2^(j+1)) + 2^(j-1))
      + (1 + 2^(j+1+1)) := by
    rw [hpow, hq, ec, ed, eb, ea]
    ring
  rw [show j + 1 - 1 = j from by omega, hsq, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]

/-- **The 2-adic half-turn congruence** — `3^(2^(j-1)) ≡ 1 + 2^(j+1)
(mod 2^(j+2))` for every `j ≥ 2`. -/
theorem half_turn_cong (j : Nat) (hj : 2 ≤ j) :
    3^(2^(j-1)) % 2^(j+2) = 1 + 2^(j+1) := by
  have key : ∀ m : Nat, ∀ jj : Nat, jj = m + 2 →
      3^(2^(jj-1)) % 2^(jj+2) = 1 + 2^(jj+1) := by
    intro m
    induction m with
    | zero =>
      intro jj hjj
      rw [hjj]
      decide
    | succ m ih =>
      intro jj hjj
      have hprev := ih (m + 2) rfl
      rw [show jj = m + 2 + 1 from by omega]
      exact half_turn_step (m + 2) (by omega) hprev
  exact key (j - 2) j (by omega)

/-- **THE ROTATION EXPANSION** — the algebraic heart of the geometric
half, with the tower power `T` held opaque so the truncated subtraction
`(T - 1)` never pollutes the ring normal form. -/
theorem htc_rot_expand (H U V T : Nat) (htt : 3^H * 3^H = T) (hT : 1 ≤ T) :
    3^H * (U + 3^H * V) = (T - 1) * V + (3^H * U + V) := by
  have key2 : ∀ v : Nat, T * v = (T - 1) * v + v := by
    intro v
    have htk : T - 1 + 1 = T := by omega
    calc T * v = ((T - 1) + 1) * v := by rw [htk]
      _ = (T - 1) * v + v := by ring
  calc 3^H * (U + 3^H * V) = 3^H * U + (3^H * 3^H) * V := by ring
    _ = 3^H * U + T * V := by rw [htt]
    _ = 3^H * U + ((T - 1) * V + V) := by rw [key2 V]
    _ = (T - 1) * V + (3^H * U + V) := by ring

/-- **POSTULATE I — THE 2-WORLD SIGNATURE LAW, CLOSED.**  For every
`j ≥ 2` the d-tower value `d j = (3^(2^j) - 1) / 2^(j+2)` carries the
ternary signature: `hasTernaryTwo (d j) = true`.  The half-turn
complement rotation: multiplication by `3^H` is simultaneously a cyclic
half-rotation (preserving `{0,1}`-words) and the arithmetic complement
`+ M/2` (turning the live trit `1` of any nonzero `{0,1}`-word into
the signature `2`). -/
theorem postulate_I (j : Nat) (hj : 2 ≤ j) : hasTernaryTwo (d j) = true := by
  by_contra hne
  have hf : hasTernaryTwo (d j) = false := by
    cases hbb : hasTernaryTwo (d j) with
    | false => rfl
    | true => exact absurd hbb hne
  have hQd := d_identity j (by omega : 1 <= j)
  have hle2 : 2 ≤ 2^j := two_pow_ge2 j (by omega)
  have h9 : 9 ≤ 3^(2^j) := by
    rw [show (9:Nat) = 3^2 from by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hle2
  have hdpos : 0 < d j := by
    by_contra h0
    push_neg at h0
    have hd0 : d j = 0 := by omega
    rw [hd0, Nat.mul_zero] at hQd
    omega
  have hdlt : d j < 3^(2^j) := by
    have hle : d j ≤ 2^(j+2) * d j := by
      calc d j = 1 * d j := (Nat.one_mul _).symm
        _ ≤ 2^(j+2) * d j := Nat.mul_le_mul_right _ (by have := two_pow_pos (j+2); omega)
    rw [hQd] at hle
    omega
  have hdig : ∀ i, (d j / 3^i) % 3 ≠ 2 := by
    intro i hi
    have hfire := hasTernaryTwo_of_digit (d j) i hi
    rw [hf] at hfire
    exact Bool.noConfusion hfire
  have hdig1 : ∀ i, (d j / 3^i) % 3 ≤ 1 := by
    intro i
    have h3 : (d j / 3^i) % 3 < 3 := Nat.mod_lt _ (show 0 < 3 by decide)
    have := hdig i
    omega
  have hrecon : d j = Finset.sum (Finset.range (2^j)) (fun i => (d j / 3^i) % 3 * 3^i) :=
    htc_digit_reconstruction (d j) (2^j) hdlt
  have hHH : 2^(j-1) + 2^(j-1) = 2^j := by
    have := two_pow_factored j (by omega : 1 <= j)
    omega
  -- THE HALF-TURN SPLIT: d j = U + 3^H · V
  have hV2 : Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^(2^(j-1) + i))
      = 3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) := by
    have hstep : Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^(2^(j-1) + i))
      = Finset.sum (Finset.range (2^(j-1)))
        (fun i => 3^(2^(j-1)) * ((d j / 3^(2^(j-1) + i)) % 3 * 3^i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.pow_add]
      ring
    rw [hstep, ← Finset.mul_sum]
  have hsplitD : d j = Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + 3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) := by
    conv_lhs => rw [hrecon, ← hHH]
    rw [Finset.sum_range_add (fun i => (d j / 3^i) % 3 * 3^i) (2^(j-1)) (2^(j-1))]
    try beta_reduce
    rw [hV2]
  -- the U/V digit facts
  have hUdig : ∀ p, p < 2^(j-1) →
      ((Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)) / 3^p) % 3 ≠ 2 := by
    intro p hp
    rw [htc_digit_of_sum (fun i => (d j / 3^i) % 3) (2^(j-1))
      (fun i hi => Nat.mod_lt _ (show 0 < 3 by decide)) p hp]
    exact hdig p
  have hVdig : ∀ p, p < 2^(j-1) →
      ((Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)) / 3^p) % 3 ≠ 2 := by
    intro p hp
    rw [htc_digit_of_sum (fun i => (d j / 3^(2^(j-1) + i)) % 3) (2^(j-1))
      (fun i hi => Nat.mod_lt _ (show 0 < 3 by decide)) p hp]
    exact hdig (2^(j-1) + p)
  have hUlt : Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i) < 3^(2^(j-1)) :=
    htc_sum_lt _ _ (fun i hi => Nat.mod_lt _ (show 0 < 3 by decide))
  have hVlt : Finset.sum (Finset.range (2^(j-1)))
      (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) < 3^(2^(j-1)) :=
    htc_sum_lt _ _ (fun i hi => Nat.mod_lt _ (show 0 < 3 by decide))
  -- THE ROTATION: 3^H · d j = M · V + (3^H · U + V)
  have htt : 3^(2^(j-1)) * 3^(2^(j-1)) = 3^(2^j) := by
    rw [← Nat.pow_add, hHH]
  have hrot : 3^(2^(j-1)) * d j = (3^(2^j) - 1) * Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)
      + (3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)) := by
    conv_lhs => rw [hsplitD]
    exact htc_rot_expand (2^(j-1))
      (Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i))
      (Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i))
      (3^(2^j)) htt (by have := three_pow_pos' (2^j); omega)
  -- W < M via 2W ≤ M
  have hlesumU : Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      ≤ Finset.sum (Finset.range (2^(j-1))) (fun i => 3^i) :=
    Finset.sum_le_sum (fun i _ =>
      Nat.le_trans (Nat.mul_le_mul (hdig1 i) (Nat.le_refl _)) (by rw [Nat.one_mul]))
  have hUle : Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      ≤ (3^(2^(j-1)) - 1) / 2 := by
    rw [← htc_geom_sum (2^(j-1))]
    exact hlesumU
  have hlesumV : Finset.sum (Finset.range (2^(j-1)))
        (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)
      ≤ Finset.sum (Finset.range (2^(j-1))) (fun i => 3^i) :=
    Finset.sum_le_sum (fun i _ =>
      Nat.le_trans (Nat.mul_le_mul (hdig1 _) (Nat.le_refl _)) (by rw [Nat.one_mul]))
  have hVle : Finset.sum (Finset.range (2^(j-1)))
      (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) ≤ (3^(2^(j-1)) - 1) / 2 := by
    rw [← htc_geom_sum (2^(j-1))]
    exact hlesumV
  have hOddH : 3^(2^(j-1)) % 2 = 1 := three_pow_odd (2^(j-1))
  have h2U : 2 * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      ≤ 3^(2^(j-1)) - 1 := by omega
  have h2V : 2 * Finset.sum (Finset.range (2^(j-1)))
      (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) ≤ 3^(2^(j-1)) - 1 := by omega
  have key4 : ∀ t : Nat, 1 ≤ t → t * (t - 1) + (t - 1) = t * t - 1 := by
    intro t ht
    have h1 : t - 1 + 1 = t := by omega
    have h2 : t * (t - 1) + (t - 1) + 1 = t * t := by
      calc t * (t - 1) + (t - 1) + 1 = t * (t - 1) + (t - 1 + 1) := by ring
        _ = t * (t - 1) + t := by rw [h1]
        _ = t * ((t - 1) + 1) := by ring
        _ = t * t := by rw [h1]
    omega
  have h2W : 2 * (3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i))
      ≤ 3^(2^j) - 1 := by
    calc 2 * (3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
        + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i))
        = 3^(2^(j-1)) * (2 * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i))
          + 2 * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) := by ring
      _ ≤ 3^(2^(j-1)) * (3^(2^(j-1)) - 1) + (3^(2^(j-1)) - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ h2U) h2V
      _ = 3^(2^j) - 1 := by
          rw [← htt]
          exact key4 _ (by have := three_pow_pos' (2^(j-1)); omega)
  have hWlt : 3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)
      < 3^(2^j) - 1 := by
    have key : ∀ w : Nat, 2 * w ≤ 3^(2^j) - 1 → w < 3^(2^j) - 1 := by
      intro w h1w; have := h9; omega
    exact key _ h2W
  have hWmod : (3^(2^(j-1)) * d j) % (3^(2^j) - 1)
      = 3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) := by
    rw [hrot, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hWlt]
  -- THE ARITHMETIC HALF: (3^H · d j) % M = d j + M/2
  have hRlt : 1 + 2^(j+1) < 2^(j+2) := by
    have hd : 2^(j+2) = 2 * 2^(j+1) := by
      rw [show j+2 = (j+1)+1 from by omega, Nat.pow_succ]
      ring
    have hpos := two_pow_pos (j+1)
    omega
  have hcong := half_turn_cong j hj
  obtain ⟨A, hA⟩ : ∃ A : Nat, 3^(2^(j-1)) = 2^(j+2) * A + (1 + 2^(j+1)) :=
    ⟨3^(2^(j-1)) / 2^(j+2), by
      exact (Nat.div_add_mod (3^(2^(j-1))) (2^(j+2))).symm.trans (by rw [hcong])⟩
  have hXmod : (3^(2^(j-1)) * d j) % (3^(2^j) - 1) = d j + (3^(2^j) - 1) / 2 := by
    have hsplit : 3^(2^(j-1)) * d j = (1 + 2^(j+1)) * d j + (3^(2^j) - 1) * A := by
      calc 3^(2^(j-1)) * d j = (2^(j+2) * A + (1 + 2^(j+1))) * d j := by rw [hA]
        _ = (1 + 2^(j+1)) * d j + A * (2^(j+2) * d j) := by ring
        _ = (1 + 2^(j+1)) * d j + A * (3^(2^j) - 1) := by rw [hQd]
        _ = (1 + 2^(j+1)) * d j + (3^(2^j) - 1) * A := by ring
    have hRdlt : (1 + 2^(j+1)) * d j < 3^(2^j) - 1 := by
      have hmono : (1 + 2^(j+1)) * d j < 2^(j+2) * d j :=
        Nat.mul_lt_mul_of_pos_right hRlt hdpos
      rw [hQd] at hmono
      exact hmono
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hRdlt]
    have hQ2 : 2^(j+2) = 2 * 2^(j+1) := by
      rw [show j+2 = (j+1)+1 from by omega, Nat.pow_succ]
      ring
    have h2t : 2 * (2^(j+1) * d j) = 3^(2^j) - 1 := by
      calc 2 * (2^(j+1) * d j) = (2 * 2^(j+1)) * d j := by ring
        _ = 2^(j+2) * d j := by rw [hQ2]
        _ = 3^(2^j) - 1 := hQd
    have hdiv : (3^(2^j) - 1) / 2 = 2^(j+1) * d j := by omega
    rw [hdiv]
    ring
  have hXW : d j + (3^(2^j) - 1) / 2
      = 3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i) :=
    hXmod.symm.trans hWmod
  -- THE FIRE: some trit of d j is 1, so the complement has a 2
  obtain ⟨p₀, hp₀lt, hp₀dig⟩ : ∃ p : Nat, p < 2^j ∧ (d j / 3^p) % 3 = 1 := by
    by_contra hall
    have hall' : ∀ p, p < 2^j → (d j / 3^p) % 3 ≠ 1 := by
      intro p hp hpe
      exact hall ⟨p, hp, hpe⟩
    have hzero : Finset.sum (Finset.range (2^j)) (fun i => (d j / 3^i) % 3 * 3^i) = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        have h1 : (d j / 3^i) % 3 = 0 := by
          have h3 : (d j / 3^i) % 3 < 3 := Nat.mod_lt _ (show 0 < 3 by decide)
          have hne := hall' i (Finset.mem_range.mp hi)
          omega
        rw [h1, Nat.zero_mul])
    rw [hrecon, hzero] at hdpos
    omega
  have hXsum : d j + (3^(2^j) - 1) / 2
      = Finset.sum (Finset.range (2^j)) (fun i => ((d j / 3^i) % 3 + 1) * 3^i) := by
    conv_lhs => rw [hrecon, ← htc_geom_sum (2^j)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hdigX : ((d j + (3^(2^j) - 1) / 2) / 3^p₀) % 3 = 2 := by
    rw [hXsum, htc_digit_of_sum (fun i => (d j / 3^i) % 3 + 1) (2^j)
      (fun i hi => by have h3 : (d j / 3^i) % 3 < 3 := Nat.mod_lt _ (show 0 < 3 by decide); omega)
      p₀ hp₀lt, hp₀dig]
  have hfireX : hasTernaryTwo (d j + (3^(2^j) - 1) / 2) = true :=
    hasTernaryTwo_of_digit (d j + (3^(2^j) - 1) / 2) p₀ hdigX
  -- THE SILENCE: the rotated word is a {0,1}-word
  have hWdig : ∀ p, ((3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)) / 3^p) % 3 ≠ 2 :=
    htc_half_turn_silent (2^(j-1)) (Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^i) % 3 * 3^i))
      (Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i))
      hUdig hVdig hUlt hVlt
  have hWsil : hasTernaryTwo (3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1)))
      (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)) = false := by
    cases hbb : hasTernaryTwo (3^(2^(j-1)) * Finset.sum (Finset.range (2^(j-1)))
      (fun i => (d j / 3^i) % 3 * 3^i)
      + Finset.sum (Finset.range (2^(j-1))) (fun i => (d j / 3^(2^(j-1) + i)) % 3 * 3^i)) with
    | false => rfl
    | true => exact absurd (hasTernaryTwo_pos _ hbb) (by
        rintro ⟨p, hp⟩
        exact hWdig p hp)
  -- THE COLLISION
  rw [hXW] at hfireX
  rw [hWsil] at hfireX
  exact Bool.noConfusion hfireX

/-! ## §14 THE SPINE COLLAPSES — the crown of Law 2 alone

With Postulate I a THEOREM, the entire §8 law-promotion spine
collapses onto the absorption-mirror bridge alone: every hypothesis
`hPI` is now discharged by `postulate_I`.  The even-exponent Erdős
statement `∀ K ≥ 8, noTernaryTwo (4^K) = false` is a theorem of the
ONE remaining granted law. -/

theorem hWave_of_mirror (hM : CardinalWorldsMirrorBridge) :
    ∀ s core : Nat, 1 ≤ s → 2 ≤ core → ¬ (3 ∣ core) →
      hasTernaryTwo (omegaCutWord s core) = true :=
  hWave_of_postulateI_mirror postulate_I hM

theorem hS0_of_mirror (hM : CardinalWorldsMirrorBridge) :
    ∀ a : Nat, 5 ≤ a → ¬ (3 ∣ a) → (a % 9 = 1 ∨ a % 9 = 4) →
      hasTernaryTwo (4^a) = true :=
  hS0_of_postulateI_mirror postulate_I hM

theorem four_power_omega_shadow_wave_tailF_of_mirror (hM : CardinalWorldsMirrorBridge) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  four_power_omega_shadow_wave_tailF_of_postulateI postulate_I hM

/-- **THE CROWN OF LAW 2 ALONE** — with Postulate I closed by the
half-turn complement rotation, the even-exponent Erdős statement is a
theorem of the absorption-mirror bridge, the single remaining grant. -/
theorem erdos_even_conjecture_of_mirror (hM : CardinalWorldsMirrorBridge) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_of_postulateI postulate_I hM

/-! ## §15 Receipts — Law 1 closed -/

#print axioms htc_sum_lt
#print axioms htc_digit_of_sum
#print axioms htc_geom_sum
#print axioms htc_mod_div_digit
#print axioms htc_digit_reconstruction
#print axioms htc_half_turn_silent
#print axioms half_turn_step
#print axioms half_turn_cong
#print axioms postulate_I
#print axioms hWave_of_mirror
#print axioms hS0_of_mirror
#print axioms four_power_omega_shadow_wave_tailF_of_mirror
#print axioms erdos_even_conjecture_of_mirror

end GSTCardinalWorldsBridge
