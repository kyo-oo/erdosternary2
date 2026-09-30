import GSTFourPowerDirectResidue
import GSTFourPowerExactExponentPeriod
import GSTFourPowerAffinePrefixIsometry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE SHADOW GAP — the exact law of the surviving exponent classes

Every window strategy in the campaign — the kernel base camps, the tower
levels, the residue classifiers — certifies the digit-two property of
`4^K` inside a bounded ternary window `p < L+1`, and that window content
depends only on the exponent class `K % 3^L` (the green exact
exponent-period law).  This file delivers the exact law of the classes
that no window can certify:

* **THE GENERATOR LAW** (`pow4_generator_surj`): the power map
  `r ↦ 4^r` enumerates ALL of `1 + 3Z` modulo `3^(L+1)` as `r` runs
  below `3^L` — the four-powers are a generator of the one-plus-three
  congruence class at every ternary scale.  The proof is the standard
  generator lifting, driven by the green LTE law
  `4^(3^L) = 1 + 3^(L+1) * lteCoeff L` with `lteCoeff L ≡ 1 (mod 3)`.

* **THE CLEAN WORDS** (`cleanList`): the words whose ternary digits are
  all zero or one — exactly `2^n` of them below `3^n`, exhibited as a
  duplicate-free complete list.

* **THE SHADOW STRUCTURE THEOREM** (`shadow_class_iff`): a class `r`
  below `3^L` survives window `L+1` (no ternary digit two of `4^r` in
  rows `< L+1`) **exactly when** `4^r ≡ 1 + 3z (mod 3^(L+1))` for a
  clean word `z` — the surviving classes are precisely the discrete
  logarithms of the clean one-plus-three words.

* **THE SHADOW COUNT, EXACT** (`shadow_count_exact`): at every level
  `L` there are **exactly `2^L`** surviving classes — the survivor list
  is exhibited, duplicate-free, and complete.  The surviving classes
  double at every level, forever: no window, however deep, ever
  certifies the digit-two property for all exponents.

* **THE INHABITANCE LAW** (`survivors_are_lived_in`): every surviving
  class is lived in by the real exponents congruent to it — each of the
  `2^L` surviving classes contains infinitely many natural exponents
  whose window at that scale is clean.  The separation of the natural
  exponents from this doubling shadow is the conjecture's own remaining
  content, named here as a machine-checked object.
-/

namespace GSTShadowGap

open GSTFourPowerDirectResidue
open GSTFourPowerExactExponentPeriod
open GSTFourPowerAffinePrefixIsometry

/-! ## Section 0 — arithmetic helpers -/

private theorem three_pow_pos (n : Nat) : 0 < 3^n := by positivity

private theorem three_pow_succ_mul (n : Nat) : 3^(n+1) = 3 * 3^n := by
  rw [Nat.mul_comm]
  exact Nat.pow_succ 3 n

/-- Divide by three after a one-trit consumption: `3y + e` with `e < 3`
has the digits of `y`, one row down. -/
theorem digit3_shift (y e q : Nat) (he : e < 3) :
    digit3 (3 * y + e) (q + 1) = digit3 y q := by
  unfold digit3
  have hdiv3 : (3 * y + e) / 3 = y := by
    have h1 : (3 * y + e) / 3 = y + e / 3 :=
      Nat.mul_add_div (by norm_num) y e
    have h2 : e / 3 = 0 := Nat.div_eq_of_lt he
    omega
  have hsplit : 3^(q+1) = 3 * 3^q := three_pow_succ_mul q
  have hdd : (3 * y + e) / 3^(q+1) = ((3 * y + e) / 3) / 3^q := by
    rw [hsplit, Nat.div_div_eq_div_mul]
  rw [hdd, hdiv3]

/-- The window law: ternary digits strictly inside a modulus window are
untouched by the window reduction. -/
theorem digit3_mod_window (R B p : Nat) (hp : p < B) :
    digit3 (R % 3^B) p = digit3 R p := by
  unfold digit3
  have h3p : (0:Nat) < 3^p := three_pow_pos p
  have hdm : 3^B * (R / 3^B) + R % 3^B = R := Nat.div_add_mod R (3^B)
  have hB : 3^B = 3^p * 3^(B - p) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  -- the division split: R / 3^p = (R % 3^B) / 3^p + 3^(B-p) * (R / 3^B)
  have hsplit : R / 3^p = (R % 3^B) / 3^p + 3^(B - p) * (R / 3^B) := by
    have hrepr : R = (R % 3^B) + 3^p * (3^(B-p) * (R / 3^B)) := by
      have h1 : 3^B * (R / 3^B) = 3^p * (3^(B-p) * (R / 3^B)) := by
        rw [← Nat.mul_assoc, ← hB]
      omega
    conv_lhs => rw [hrepr]
    rw [Nat.add_mul_div_left _ _ h3p]
  have hzero : (3^(B - p) * (R / 3^B)) % 3 = 0 := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : B - p ≠ 0) with ⟨m, hm⟩
    rw [hm, Nat.pow_succ]
    simp [Nat.mul_mod]
  rw [hsplit, Nat.add_mod, hzero, Nat.add_zero, Nat.mod_mod]

/-- The window-class law: the window content of `4^m` at scale `L`
depends only on `m % 3^L`. -/
theorem pow4_mod_window_class (L m : Nat) :
    4^m % 3^(L+1) = 4^(m % 3^L) % 3^(L+1) := by
  have hmodid : m % 3^L = (m % 3^L) % 3^L :=
    (Nat.mod_mod_of_dvd m (dvd_refl (3^L))).symm
  have key := (pow4_modeq_iff_exponent_modeq L m (m % 3^L)).2 hmodid
  exact key

/-! ## Section 1 — the generator law -/

/-- **THE GENERATOR LAW.**  The four-powers enumerate all one-plus-three
residues at every ternary scale: for every `z < 3^L` there is a class
`r < 3^L` with `4^r ≡ 1 + 3z (mod 3^(L+1))`.  Proof: generator lifting
by the LTE law `4^(3^L) = 1 + 3^(L+1) * lteCoeff L`, whose coefficient
is one modulo three. -/
theorem pow4_generator_surj : ∀ (L z : Nat), z < 3^L →
    ∃ r : Nat, r < 3^L ∧ 4^r % 3^(L+1) = (1 + 3*z) % 3^(L+1) := by
  intro L
  induction L with
  | zero =>
      intro z hz
      have hz0 : z = 0 := Nat.lt_one_iff.mp hz
      subst hz0
      refine ⟨0, by simp, ?_⟩
      decide
  | succ L ih =>
      intro z hz
      -- the parent word and its class
      have h3L : 0 < 3^L := three_pow_pos L
      obtain ⟨rp, hrp, hrpow⟩ := ih (z % 3^L) (Nat.mod_lt _ h3L)
      -- the parent target matches the child target at the parent scale
      have hzsplit : z = 3^L * (z / 3^L) + z % 3^L :=
        (Nat.div_add_mod z (3^L)).symm
      have htarget : (1 + 3*(z % 3^L)) % 3^(L+1) = (1 + 3*z) % 3^(L+1) := by
        have h3z : 1 + 3*z = (1 + 3*(z % 3^L)) + 3^(L+1) * (z / 3^L) := by
          conv_lhs => rw [hzsplit]
          rw [three_pow_succ_mul]
          ring
        rw [h3z, Nat.add_mul_mod_self_left]
      rw [htarget] at hrpow
      -- LTE: the lifting generator and its unit coefficient
      have hLTE : 4^(3^L) = 1 + 3^(L+1) * lteCoeff L :=
        pow4_three_power_lte_exact L
      have hu : lteCoeff L % 3 = 1 := lteCoeff_mod3_one L
      have hA3 : 4^rp % 3 = 1 := pow4_mod3_one rp
      -- the scales
      have hMM : 3^(L+2) = 3 * 3^(L+1) := by
        rw [Nat.mul_comm]
        exact Nat.pow_succ 3 (L+1)
      have hmpos : 0 < 3^(L+1) := three_pow_pos (L+1)
      -- the key modular law: c + m*Y mod 3m for c < m
      have keymod (m c Y : Nat) (hm : 0 < m) (hclt : c < m) :
          (c + m * Y) % (3 * m) = c + m * (Y % 3) := by
        have hY : Y = 3 * (Y / 3) + Y % 3 := Nat.div_add_mod Y 3
        have hY3 : Y % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have hexp : c + m * Y = (c + m * (Y % 3)) + (3 * m) * (Y / 3) := by
          rw [hY]
          ring
        rw [hexp, Nat.add_mul_mod_self_left]
        apply Nat.mod_eq_of_lt
        have h2 : m * (Y % 3) ≤ 2 * m := by
          calc m * (Y % 3) ≤ m * 2 := Nat.mul_le_mul_left _ (by omega)
            _ = 2 * m := by ring
        omega
      -- the lifts of the generator power
      have gtmod (t : Nat) (ht : t ≤ 2) :
          (4^(3^L))^t % 3^(L+2) = (1 + t * (3^(L+1) * lteCoeff L)) % 3^(L+2) := by
        obtain ht012 : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        rcases ht012 with h0 | h1 | h2
        · subst h0; simp
        · subst h1
          rw [Nat.pow_one, hLTE]
          rw [show 1 + 3^(L+1) * lteCoeff L = 1 + 1 * (3^(L+1) * lteCoeff L)
            from by ring]
        · subst h2
          have hg2 : (4^(3^L))^2 = 1 + 2 * (3^(L+1) * lteCoeff L)
              + (3^(L+1) * lteCoeff L)^2 := by
            rw [Nat.pow_two, hLTE]
            ring
          have hdvd : 3^(L+2) ∣ (3^(L+1) * lteCoeff L)^2 := by
            have hsq : (3^(L+1) * lteCoeff L)^2
                = 3^(L+1) * 3^(L+1) * (lteCoeff L)^2 := by
              ring
            have hMdvd : 3^(L+2) ∣ 3^(L+1) * 3^(L+1) := by
              have hp2 : 3^(L+1) * 3^(L+1) = 3^((L+1) + (L+1)) :=
                (Nat.pow_add 3 (L+1) (L+1)).symm
              have hle : L + 2 ≤ (L+1) + (L+1) := by omega
              rw [hp2]
              exact Nat.pow_dvd_pow 3 hle
            rw [hsq]
            exact hMdvd.mul _
          rw [hg2, hMM]
          obtain ⟨k, hk⟩ := hdvd
          have hexp : 1 + 2 * (3^(L+1) * lteCoeff L) + (3^(L+1) * lteCoeff L)^2
              = (1 + 2 * (3^(L+1) * lteCoeff L)) + (3 * 3^(L+1)) * k := by
            rw [hk, hMM]
            ring
          rw [hexp, Nat.add_mul_mod_self_left]
      -- each lift's window value at the child scale
      have liftval (t : Nat) (ht : t ≤ 2) :
          4^(rp + t * 3^L) % 3^(L+2)
            = (4^rp % 3^(L+1)) + 3^(L+1) * (((4^rp / 3^(L+1)) + t) % 3) := by
        have hpow : 4^(rp + t * 3^L) = 4^rp * (4^(3^L))^t := by
          rw [Nat.pow_add, Nat.mul_comm t (3^L), Nat.pow_mul]
        have hgt : (4^(3^L))^t % 3^(L+2)
            = (1 + t * (3^(L+1) * lteCoeff L)) % 3^(L+2) := gtmod t ht
        have hme : (4^rp * (4^(3^L))^t) % 3^(L+2)
            = (4^rp * (1 + t * (3^(L+1) * lteCoeff L))) % 3^(L+2) :=
          Nat.ModEq.mul_left (4^rp) hgt
        rw [hpow, hme]
        have hexpand : 4^rp * (1 + t * (3^(L+1) * lteCoeff L))
            = (4^rp % 3^(L+1))
              + 3^(L+1) * ((4^rp / 3^(L+1)) + t * lteCoeff L * 4^rp) := by
          have hAm : 4^rp = 3^(L+1) * (4^rp / 3^(L+1)) + 4^rp % 3^(L+1) :=
            (Nat.div_add_mod (4^rp) (3^(L+1))).symm
          have h1 : 4^rp * (1 + t * (3^(L+1) * lteCoeff L))
              = 4^rp + t * (3^(L+1) * lteCoeff L) * 4^rp := by ring
          have h2 : (4^rp % 3^(L+1))
              + 3^(L+1) * ((4^rp / 3^(L+1)) + t * lteCoeff L * 4^rp)
              = (3^(L+1) * (4^rp / 3^(L+1)) + 4^rp % 3^(L+1))
                + t * (3^(L+1) * lteCoeff L) * 4^rp := by ring
          rw [h1, h2, ← hAm]
        rw [hexpand, hMM, keymod _ _ _ hmpos (Nat.mod_lt _ hmpos)]
        have huA : (lteCoeff L * 4^rp) % 3 = 1 := by
          have hm := Nat.mul_mod (lteCoeff L) (4^rp) 3
          rw [hu, hA3] at hm
          simp at hm
          exact hm
        have hmod3 : ((4^rp / 3^(L+1)) + t * lteCoeff L * 4^rp) % 3
            = ((4^rp / 3^(L+1)) + t) % 3 := by
          have hassoc : t * lteCoeff L * 4^rp = t * (lteCoeff L * 4^rp) := by
            ring
          have hm := Nat.mul_mod t (lteCoeff L * 4^rp) 3
          rw [huA] at hm
          rw [hassoc, Nat.add_mod, Nat.add_mod, hm]
          omega
        rw [hmod3]
      -- the child value at the same scale
      have childval : (1 + 3*z) % 3^(L+2)
          = (4^rp % 3^(L+1)) + 3^(L+1) * (((1 + 3*z) / 3^(L+1)) % 3) := by
        have hBeq : 1 + 3*z
            = (4^rp % 3^(L+1)) + 3^(L+1) * ((1 + 3*z) / 3^(L+1)) := by
          have hdm : 3^(L+1) * ((1 + 3*z) / 3^(L+1)) + (1 + 3*z) % 3^(L+1)
              = 1 + 3*z := Nat.div_add_mod (1 + 3*z) (3^(L+1))
          have hcc : (1 + 3*z) % 3^(L+1) = 4^rp % 3^(L+1) := hrpow
          omega
        rw [hMM]
        conv_lhs => rw [hBeq]
        rw [keymod _ _ _ hmpos (Nat.mod_lt _ hmpos)]
      -- choose the lift
      have hext : ∃ t : Nat, t ≤ 2 ∧
          ((4^rp / 3^(L+1)) + t) % 3 = ((1 + 3*z) / 3^(L+1)) % 3 := by
        have hma : (4^rp / 3^(L+1)) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have hmb : ((1 + 3*z) / 3^(L+1)) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        refine ⟨(((1 + 3*z) / 3^(L+1)) % 3 + 3 - (4^rp / 3^(L+1)) % 3) % 3,
          by omega, ?_⟩
        omega
      obtain ⟨t, ht, htpow⟩ := hext
      refine ⟨rp + t * 3^L, ?_, ?_⟩
      · rw [three_pow_succ_mul]
        omega
      · rw [liftval t ht, childval, htpow]

/-! ## Section 2 — the clean words -/

/-- The clean words below `3^n`: all ternary digits zero or one. -/
def cleanList : Nat → List Nat
  | 0 => [0]
  | n+1 => (cleanList n).map (fun z => 3 * z) ++ (cleanList n).map (fun z => 3 * z + 1)

theorem cleanList_length (n : Nat) : (cleanList n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cleanList, List.length_map, List.length_append, ih]
      have hp : 2^(n+1) = 2 * 2^n := by
        rw [Nat.mul_comm]
        exact Nat.pow_succ 2 n
      omega

theorem cleanList_bound (n : Nat) : ∀ z ∈ cleanList n, z < 3^n ∧
    ∀ q : Nat, q < n → digit3 z q ≠ 2 := by
  induction n with
  | zero =>
      intro z hz
      simp only [cleanList, List.mem_singleton] at hz
      subst hz
      refine ⟨by simp, ?_⟩
      intro q hq
      omega
  | succ n ih =>
      intro z hz
      simp only [cleanList, List.mem_append, List.mem_map] at hz
      rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · obtain ⟨hy1, hy2⟩ := ih y hy
        refine ⟨by rw [three_pow_succ_mul]; omega, ?_⟩
        intro q hq
        cases q with
        | zero =>
            simp only [digit3, Nat.pow_zero, Nat.div_one]
            omega
        | succ q =>
            have hq' : q < n := by omega
            have hclean := hy2 q hq'
            rw [← Nat.add_zero (3 * y), digit3_shift y 0 q (by omega)]
            exact hclean
      · obtain ⟨hy1, hy2⟩ := ih y hy
        refine ⟨by rw [three_pow_succ_mul]; omega, ?_⟩
        intro q hq
        cases q with
        | zero =>
            simp only [digit3, Nat.pow_zero, Nat.div_one]
            omega
        | succ q =>
            have hq' : q < n := by omega
            have hclean := hy2 q hq'
            rw [digit3_shift y 1 q (by omega)]
            exact hclean

theorem cleanList_complete (n : Nat) : ∀ z : Nat, z < 3^n →
    (∀ q : Nat, q < n → digit3 z q ≠ 2) → z ∈ cleanList n := by
  induction n with
  | zero =>
      intro z hz _
      have hz0 : z = 0 := Nat.lt_one_iff.mp hz
      subst hz0
      simp [cleanList]
  | succ n ih =>
      intro z hz hclean
      have he : z % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hd0 : digit3 z 0 = z % 3 := by
        simp only [digit3, Nat.pow_zero, Nat.div_one]
      have hne : z % 3 ≠ 2 := by
        rw [← hd0]
        exact hclean 0 (by omega)
      have hzy : z = 3 * (z / 3) + z % 3 := (Nat.div_add_mod z 3).symm
      have hylt : z / 3 < 3^n := by
        apply Nat.div_lt_of_lt_mul
        rw [← three_pow_succ_mul]
        omega
      have hyclean : ∀ q : Nat, q < n → digit3 (z / 3) q ≠ 2 := by
        intro q hq
        have hrow := hclean (q+1) (by omega)
        rw [hzy, digit3_shift (z / 3) (z % 3) q he] at hrow
        exact hrow
      have hy := ih (z / 3) hylt hyclean
      rcases Nat.lt_or_ge (z % 3) 1 with h01 | h12
      · have he0 : z % 3 = 0 := by omega
        refine List.mem_append_left _ ?_
        rw [hzy, he0]
        exact List.mem_map_of_mem hy
      · have he1 : z % 3 = 1 := by omega
        refine List.mem_append_right _ ?_
        rw [hzy, he1]
        exact List.mem_map_of_mem hy

theorem cleanList_nodup (n : Nat) : (cleanList n).Nodup := by
  induction n with
  | zero => simp [cleanList]
  | succ n ih =>
      simp only [cleanList]
      have inj1 : Function.Injective (fun z : Nat => 3 * z) := by
        intro a b h
        have h' : 3 * a = 3 * b := h
        omega
      have inj2 : Function.Injective (fun z : Nat => 3 * z + 1) := by
        intro a b h
        have h' : 3 * a + 1 = 3 * b + 1 := h
        omega
      refine List.Nodup.append (List.Nodup.map inj1 ih) (List.Nodup.map inj2 ih) ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨b, _, hb⟩ := hmem
      omega

/-! ## Section 3 — the shadow structure and the exact count -/

/-- The discrete log of a word at scale `L`: the class whose four-power
carries the word `1 + 3z` modulo `3^(L+1)`. -/
noncomputable def shadowLog (L z : Nat) : Nat :=
  if h : z < 3^L then Nat.find (pow4_generator_surj L z h) else 0

theorem shadowLog_spec (L z : Nat) (hz : z < 3^L) :
    shadowLog L z < 3^L ∧ 4^(shadowLog L z) % 3^(L+1) = 1 + 3*z := by
  have hzlt : 1 + 3*z < 3^(L+1) := by
    have hB : 3^(L+1) = 3 * 3^L := three_pow_succ_mul L
    omega
  unfold shadowLog
  rw [dif_pos hz]
  have hfs := Nat.find_spec (pow4_generator_surj L z hz)
  have h2' : 4^(Nat.find (pow4_generator_surj L z hz)) % 3^(L+1)
      = 1 + 3*z := by
    rw [hfs.2, Nat.mod_eq_of_lt hzlt]
  exact ⟨hfs.1, h2'⟩

theorem shadowLog_eq (L z r : Nat) (hz : z < 3^L) (hr : r < 3^L)
    (h : 4^r % 3^(L+1) = 1 + 3*z) : shadowLog L z = r := by
  have hspec := shadowLog_spec L z hz
  have hmodeq : 4^r ≡ 4^(shadowLog L z) [MOD 3^(L+1)] := by
    show 4^r % 3^(L+1) = 4^(shadowLog L z) % 3^(L+1)
    rw [h, hspec.2]
  have hex := (pow4_modeq_iff_exponent_modeq L r (shadowLog L z)).mp hmodeq
  have hex' : r % 3^L = (shadowLog L z) % 3^L := hex
  have h1 : r % 3^L = r := Nat.mod_eq_of_lt hr
  have h2 : (shadowLog L z) % 3^L = shadowLog L z :=
    Nat.mod_eq_of_lt hspec.1
  omega

private theorem shadowLog_inj_aux (L z z' : Nat) (hz : z < 3^L)
    (hz' : z' < 3^L) (h : shadowLog L z = shadowLog L z') (hle : z ≤ z') :
    z = z' := by
  by_contra hne
  have hlt : z < z' := by omega
  have s1 := shadowLog_spec L z hz
  have s2 := shadowLog_spec L z' hz'
  rw [h] at s1
  obtain ⟨_, s1b⟩ := s1
  obtain ⟨_, s2b⟩ := s2
  have hraw : (1:Nat) + 3*z = 1 + 3*z' := by omega
  have hcongr : (1 + 3*z) % 3^(L+1) = (1 + 3*z') % 3^(L+1) :=
    congrArg (fun w => w % 3^(L+1)) hraw
  -- cancel the common word: 3*(z'-z) ≡ 0 mod 3^(L+1)
  have hme0 : (1 + 3*z) + 3*(z'-z) ≡ (1 + 3*z) + 0 [MOD 3^(L+1)] := by
    rw [Nat.add_zero]
    have hx : (1 + 3*z) + 3*(z'-z) = 1 + 3*z' := by omega
    rw [hx]
    exact hcongr.symm
  have hzero : 3*(z'-z) ≡ 0 [MOD 3^(L+1)] :=
    Nat.ModEq.add_left_cancel' (1 + 3*z) hme0
  have hdvd : 3^(L+1) ∣ 3 * (z' - z) := Nat.modEq_zero_iff_dvd.mp hzero
  have hdvd' : 3^L ∣ (z' - z) := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have hp : 3^(L+1) = 3^L * 3 := Nat.pow_succ 3 L
    rw [hp] at hk
    have hke : 3 * (z' - z) = 3 * (3^L * k) := by
      rw [hk]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0:Nat) < 3) hke
  have hzero' := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
  omega

theorem shadowLog_inj (L z z' : Nat) (hz : z < 3^L) (hz' : z' < 3^L)
    (h : shadowLog L z = shadowLog L z') : z = z' := by
  rcases le_total z z' with hle | hle
  · exact shadowLog_inj_aux L z z' hz hz' h hle
  · exact (shadowLog_inj_aux L z' z hz' hz h.symm hle).symm

/-- **THE SHADOW STRUCTURE THEOREM.**  A class `r < 3^L` survives the
window `L+1` — no ternary digit two of `4^r` in rows `< L+1` — exactly
when `4^r` carries a clean word `1 + 3z` modulo `3^(L+1)`.  The
surviving classes are the discrete logarithms of the clean
one-plus-three words. -/
theorem shadow_class_iff (L r : Nat) (hr : r < 3^L) :
    (∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2) ↔
    (∃ z : Nat, z ∈ cleanList L ∧ 4^r % 3^(L+1) = 1 + 3*z) := by
  constructor
  · intro hsurv
    have hyM : 4^r % 3^(L+1) < 3^(L+1) :=
      Nat.mod_lt _ (three_pow_pos (L+1))
    have h3dvd : (3 : Nat) ∣ 3^(L+1) := by
      have hp : 3^(L+1) = 3 * 3^L := three_pow_succ_mul L
      rw [hp]
      exact ⟨3^L, rfl⟩
    have hy3 : (4^r % 3^(L+1)) % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd (4^r) h3dvd]
      exact pow4_mod3_one r
    have hyz : 4^r % 3^(L+1) = 1 + 3 * ((4^r % 3^(L+1)) / 3) := by
      have hdm : 3 * ((4^r % 3^(L+1)) / 3) + (4^r % 3^(L+1)) % 3
          = 4^r % 3^(L+1) := Nat.div_add_mod _ 3
      omega
    have hzlt : (4^r % 3^(L+1)) / 3 < 3^L := by
      apply Nat.div_lt_of_lt_mul
      have hB : 3^(L+1) = 3 * 3^L := three_pow_succ_mul L
      omega
    have hclean : ∀ q : Nat, q < L →
        digit3 ((4^r % 3^(L+1)) / 3) q ≠ 2 := by
      intro q hq
      have hrow := hsurv (q+1) (by omega)
      have hwin : digit3 (4^r % 3^(L+1)) (q+1) = digit3 (4^r) (q+1) :=
        digit3_mod_window (4^r) (L+1) (q+1) (by omega)
      rw [← hwin] at hrow
      rw [hyz, Nat.add_comm, digit3_shift _ 1 q (by omega)] at hrow
      exact hrow
    have hmem := cleanList_complete L ((4^r % 3^(L+1)) / 3) hzlt hclean
    exact ⟨(4^r % 3^(L+1)) / 3, hmem, hyz⟩
  · rintro ⟨z, hmem, hcongr⟩
    obtain ⟨hzlt, hzclean⟩ := cleanList_bound L z hmem
    intro p hp
    cases p with
    | zero =>
        have hd0 : digit3 (4^r) 0 = 4^r % 3 := by
          simp only [digit3, Nat.pow_zero, Nat.div_one]
        rw [hd0, pow4_mod3_one]
        omega
    | succ q =>
        have hwin : digit3 (4^r % 3^(L+1)) (q+1) = digit3 (4^r) (q+1) :=
          digit3_mod_window (4^r) (L+1) (q+1) (by omega)
        rw [← hwin, hcongr, Nat.add_comm, digit3_shift z 1 q (by omega)]
        exact hzclean q (by omega)

/-- **THE SHADOW COUNT, EXACT.**  At every scale `L` there are exactly
`2^L` surviving classes: the exhibited list is duplicate-free, all its
members survive the window `L+1`, and every surviving class is on it. -/
theorem shadow_count_exact (L : Nat) :
    ∃ S : List Nat,
      S.length = 2^L ∧
      S.Nodup ∧
      (∀ r ∈ S, r < 3^L ∧ ∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2) ∧
      (∀ r : Nat, r < 3^L →
        (∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2) → r ∈ S) := by
  have hkey : ∀ z ∈ cleanList L, shadowLog L z < 3^L ∧
      4^(shadowLog L z) % 3^(L+1) = 1 + 3*z := by
    intro z hmem
    exact shadowLog_spec L z (cleanList_bound L z hmem).1
  refine ⟨(cleanList L).map (shadowLog L), ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, cleanList_length]
  · refine List.Nodup.map_on ?_ (cleanList_nodup L)
    intro x hx y hy hxy
    have hx' := cleanList_bound L x hx
    have hy' := cleanList_bound L y hy
    exact shadowLog_inj L x y hx'.1 hy'.1 hxy
  · intro r hr
    obtain ⟨z, hmem, rfl⟩ := List.mem_map.mp hr
    have hspec := hkey z hmem
    refine ⟨hspec.1, ?_⟩
    exact (shadow_class_iff L (shadowLog L z) hspec.1).mpr
      ⟨z, hmem, hspec.2⟩
  · intro r hr hsurv
    obtain ⟨z, hmem, hcongr⟩ := (shadow_class_iff L r hr).mp hsurv
    have hlog : shadowLog L z = r :=
      shadowLog_eq L z r (cleanList_bound L z hmem).1 hr hcongr
    have hmem' : shadowLog L z ∈ (cleanList L).map (shadowLog L) :=
      List.mem_map_of_mem hmem
    rw [hlog] at hmem'
    exact hmem'

/-- **THE INHABITANCE LAW.**  Every surviving class is lived in: each
exponent congruent to a surviving class has a clean window at that
scale — the level-`L` window certification fails on every one of the
`2^L` surviving classes' worth of exponents, at every level, forever. -/
theorem survivors_are_lived_in (L r : Nat) (hr : r < 3^L)
    (hsurv : ∀ p : Nat, p < L + 1 → digit3 (4^r) p ≠ 2) :
    ∀ m : Nat, m % 3^L = r → ∀ p : Nat, p < L + 1 → digit3 (4^m) p ≠ 2 := by
  intro m hmr p hp
  have hcls : 4^m % 3^(L+1) = 4^r % 3^(L+1) := by
    rw [pow4_mod_window_class L m, hmr]
  have hwin : digit3 (4^m % 3^(L+1)) p = digit3 (4^m) p :=
    digit3_mod_window (4^m) (L+1) p hp
  rw [← hwin, hcls, digit3_mod_window (4^r) (L+1) p hp]
  exact hsurv p hp

/-! ## Section 4 — receipts -/

#print axioms digit3_shift
#print axioms digit3_mod_window
#print axioms pow4_generator_surj
#print axioms shadow_class_iff
#print axioms shadow_count_exact
#print axioms survivors_are_lived_in

end GSTShadowGap
