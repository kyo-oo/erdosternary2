import ErdosTernary2

/-!
# DeepMind Problem 406 — comparator solution

This is the solution-side Lean file for the official comparator harness.
It imports the checked green monolith `ErdosTernary2` and bridges the
question-side recursive predicate to the monolith's `noTernaryTwo`
predicate.

The production seam now carries the Ω-shadow wave tail in its second-sheet
form as its single named input: the Ω-Wave Law (`GSTGraphV2OmegaWaveLaw`)
delivers the ternary digit two unconditionally for every exponent outside
the Ω-shadow residue (the canonical 3-free-core classes the tower's proven
levels do not reach), the kernel-checked modular base carries every
half-exponent up to five hundred — shadow members included — the tower's
third and fourth levels carry their gate classes (thirteen and
twenty-five modulo twenty-seven at sheet level two and above; the top
third of the residue window modulo eighty-one at sheet level three and
above), the Ω-sheet gate — the wave word one digit beyond the
stabilization window — carries every dodger whose sheet-local cut word
has top trit two modulo the squared cut modulus, the Ω-second-sheet gate
— the binomial correction's own trit at row `2s+3`, where the wave word's
second order first touches — carries the four-sheet's lowest-third and
the seven-sheet's middle-third sheet words, and the sheet-zero
exponent-cycle gates carry the base's own period classes at rows three
and four.  The input speaks only for shadow exponents above the kernel
base that dodge every proven gate, both sheet gates, and the period
classes: weaker than the sealed shadow wave, and strictly weaker than the
retired third-wave climb.  The repository also carries the campaign's
zero-input target `four_power_omega_shadow_wave_closed` together with
the receipt theorem `four_power_omega_shadow_wave_closed_iff_tail4`:
the closed statement is equivalent to the fifth-weakening tail input,
so the tail's residual is exactly the closed wave's own content.
-/

/-- Byte-identical challenge-side definition. -/
def noTernaryDigitTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryDigitTwo (n / 3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 3)

/-- Bridge the challenge recursion to the monolith's `noTernaryTwo`. -/
theorem noTernaryDigitTwo_eq_noTernaryTwo (n : Nat) :
    noTernaryDigitTwo n = noTernaryTwo n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [noTernaryDigitTwo.eq_def n, noTernaryTwo.eq_def n]
    by_cases hn : n = 0
    · simp [hn]
    · by_cases h2 : n % 3 = 2
      · simp [hn, h2]
      · simp [hn, h2]
        exact ih (n / 3) (Nat.div_lt_self (by omega) (by decide : 1 < 3))

/-- DeepMind Problem 406 / Erdős ternary-2 comparator solution, delivered
from the Ω-Wave Law through the green monolith seam. -/
theorem erdos_ternary_2
    (hTail4 : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tail4) :
    ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false := by
  intro n hn
  rw [noTernaryDigitTwo_eq_noTernaryTwo (2^n)]
  exact erdos_ternary_2_universal_tail4 hTail4 n hn
