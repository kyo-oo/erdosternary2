#!/usr/bin/env python3
from pathlib import Path
import runpy

patcher = Path('scripts/apply_u2d_atomic_replacement.py')
s = patcher.read_text(encoding='utf-8')

start1 = s.index("/-- Kernel adapter for the already-proved creation certificate.")
end1 = s.index("/-- Inverse of the forced `s+1` prefix shift.", start1)
new1 = r'''/-- Kernel adapter for the already-proved universal creation certificate.
The carry-one branch is advanced by one exact GST carry edge, exactly as in the
independent pre-prefix-one kernel probe. -/
theorem gst_h_creation_full_power_navigation_atomic
    (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :
    GSTNavigationWitness (4^k) := by
  obtain ⟨p, hp1, hd, hcase⟩ := h_creation_for_4pow k hk5 hk7
  have hClt : gstCarry (4^k) p < 4 := gstCarry_lt_four _ _ hp1
  rcases hcase with hmod0 | hmod1
  · have hCmod : gstCarry (4^k) p % 3 = 0 := by
      simpa [gstCarry] using hmod0
    have hC : gstCarry (4^k) p = 0 ∨ gstCarry (4^k) p = 3 := by
      omega
    rcases hC with h0 | h3
    · exact gstNavigationWitness_of_digit_carry_zero (4^k) p hd h0
    · exact gstNavigationWitness_of_digit_carry_three (4^k) p hd h3
  · have hCmod : gstCarry (4^k) p % 3 = 1 := by
      simpa [gstCarry] using hmod1.1
    have hC : gstCarry (4^k) p = 1 := by omega
    have hnext := gstCarry_forward_exact (4^k) p hp1
    rw [hC, hd] at hnext
    norm_num [gstStepCarry] at hnext
    have hdnext : gstDigit (4^k) (p+1) = 2 := by
      simpa [gstDigit] using hmod1.2
    exact gstNavigationWitness_of_digit_carry_three (4^k) (p+1) hdnext hnext

'''
s = s[:start1] + new1 + s[end1:]

start2 = s.index("/-- Inverse of the forced `s+1` prefix shift.")
end2 = s.index("/-- Atomic Surgery V2:", start2)
new2 = r'''/-- Inverse of the forced `s+1` prefix shift.  A full perfect-power
Navigation witness cannot occur below the exact prefix `1 mod 3^(s+1)`, hence
it descends through the already-proved universal Navigation-position iff. -/
theorem gst_full_power_navigation_descends_atomic
    (s b : Nat) (hs : 1 ≤ s) (hb : 1 ≤ b) (hb3 : b % 3 ≠ 0)
    (hfull : GSTNavigationWitness (4^(3^s * b))) :
    GSTNavigationWitness (gstNavigationConstant s b) := by
  obtain ⟨p, hd, hspace⟩ := hfull
  have hpge : s + 1 ≤ p := by
    by_contra hnot
    have hplt : p < s + 1 := by omega
    have hdecomp := gst_navigation_decomposition s b hs
    have hbiggt : 1 < 3^(s+1) := by
      have h9 : 9 ≤ 3^(s+1) := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
          (show 2 ≤ s+1 by omega))
      omega
    have hRmodBig : 4^(3^s * b) % 3^(s+1) = 1 := by
      rw [hdecomp, Nat.add_mod]
      have hmul :
          (3^(s+1) * gstNavigationConstant s b) % 3^(s+1) = 0 :=
        Nat.mod_eq_zero_of_dvd ⟨gstNavigationConstant s b, rfl⟩
      rw [hmul, Nat.add_zero]
      exact Nat.mod_eq_of_lt hbiggt
    have hdvd : 3^(p+1) ∣ 3^(s+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hsmallgt : 1 < 3^(p+1) := by
      have h3 : 3 ≤ 3^(p+1) := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
          (show 1 ≤ p+1 by omega))
      omega
    have hm := Nat.mod_mod_of_dvd (4^(3^s * b)) hdvd
    rw [hRmodBig, Nat.mod_eq_of_lt hsmallgt] at hm
    have hRmodSmall : 4^(3^s * b) % 3^(p+1) = 1 := hm.symm
    have hdi := digit_identity (4^(3^s * b)) p
    rw [hRmodSmall] at hdi
    change 4^(3^s * b) / 3^p % 3 = 2 at hd
    by_cases hp0 : p = 0
    · subst p
      norm_num at hd
      omega
    · have hp1 : 1 ≤ p := by omega
      have h3p : 3 ≤ 3^p := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hp1)
      have hdiv0 : 1 / 3^p = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv0] at hdi
      norm_num at hdi
      omega
  let j := p - (s+1)
  have hpEq : p = s + 1 + j := by
    dsimp [j]
    omega
  refine ⟨j, ?_⟩
  apply (gst_navigation_position_universal s b j hs hb hb3).1
  rw [← hpEq]
  exact ⟨hd, hspace⟩

'''
s = s[:start2] + new2 + s[end2:]

patcher.write_text(s, encoding='utf-8')
runpy.run_path(str(patcher), run_name='__main__')
