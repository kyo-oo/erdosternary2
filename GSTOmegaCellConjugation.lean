import GSTGraphV2OmegaWaveLaw
import GSTFourPowerDirectExistenceFromHappy
import GSTCanonicalTailStateIso

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# The Cell Conjugation and the Level-Three Happy Gate

The tower laws of the Ω-Wave Law read the cut decomposition
`4^(3^a * core) = 1 + 3^(a+1) * omegaCutWord a core` one row at a time and
one coordinate at a time: the level-two and level-three digit laws deliver
ternary digits, and the class-two LTE-cut gate delivers a full Happy cell
at the cut row itself.  What the tower never assembled is the CARRY half
of the slice at depth: the seed-zero law of the infinite controller
(`prefix_slice_seed_zero`) carries the x4-carry of the cut word up to the
power exactly as the digit law carries the digit — and the two together
make the slice a full CELL conjugation.

This file delivers, all unconditional, all from green parts:

* **THE CELL CONJUGATION** (`omega_happy_conjugation`): for every sheet
  level `a ≥ 1` and every depth `j`, a Happy cell of the cut word at row
  `j` IS a Happy cell of the power at row `a+1+j`.  The class-two LTE-cut
  gate is the `j = 0` row; the digit laws are the digit half; the law here
  is the first to carry BOTH coordinates at every depth.

* **THE LEVEL-THREE HAPPY GATE** (`omega_level3_happy_gate`): every
  exponent `K = 3^a * core` with `a ≥ 2` and core mass in the classes
  `{5, 8, 10, 13}` modulo 27 owns a physical Happy row at `a+3` — digit
  two at the 9s place of `16 * core mod 27` (the green level-three cut
  word law) with x4-carry `⌊4·(7·core mod 9)/9⌋ ∈ {0, 3}` (the level-two
  word law).  The classes 5 and 8 re-derive class two one sheet deeper;
  the classes 10 and 13 are NEW — the first full Happy cells certified
  inside the `core ≡ 1 (mod 3)` half of the exponent space, where the
  tower previously reached only digit-twos (13) or nothing at all (10).

* **THE COMMON-TWO WIRING** (`commonTwo_of_omega_classTwo`,
  `commonTwo_of_omega_level3`): both infinite families now feed the
  creation master's atomic input `CommonTwo` directly through the green
  FromHappy bridge.  One socket; the socket's certified families grow.
-/

namespace GSTOmegaCellConjugation

open GSTGraphV2OmegaWaveLaw
open GSTGraphV2InfiniteControl
open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport

/-! ## Section 1 — the cell conjugation -/

/-- **THE CELL CONJUGATION.**  For every sheet level `a ≥ 1` and every
depth `j`: a Happy cell of the cut word at row `j` is a Happy cell of the
power `4^(3^a * core)` at row `a+1+j`.  The cut decomposition is a
prefix/tail slice with prefix one and seed zero (the quadrupled prefix
`4·1` stays below the cut modulus from sheet level one onward), so the
infinite controller's slice laws carry BOTH the ternary digit and the
x4-carry of the word up to the power, one cut modulus higher. -/
theorem omega_happy_conjugation (a core j : Nat) (ha : 1 ≤ a)
    (h : HappyCell (carry4 (omegaCutWord a core) j)
        (digit3 (omegaCutWord a core) j)) :
    HappyCell (carry4 (4^(3^a * core)) (a+1+j))
        (digit3 (4^(3^a * core)) (a+1+j)) := by
  obtain ⟨hd, hc⟩ := h
  have hf : 4^(3^a * core) = 1 + 3^(a+1) * omegaCutWord a core :=
    omega_cut_factor a core
  have hP : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hseed : (4:Nat) * 1 < 3^(a+1) := by
    have h9 : (3:Nat)^2 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 2 ≤ a+1)
    have h32 : (3:Nat)^2 = 9 := by norm_num
    omega
  refine ⟨?_, ?_⟩
  · have hdig := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) j hP
    rw [hf, hdig]
    exact hd
  · have hcar := prefix_slice_seed_zero (a+1) 1 (omegaCutWord a core) j hP hseed
    have hsc : seededCarry 0 (omegaCutWord a core) j
        = carry4 (omegaCutWord a core) j := by
      unfold seededCarry carry4
      rw [Nat.zero_add]
    rw [hf, hcar, hsc]
    exact hc

/-! ## Section 2 — the level-three Happy gate -/

/-- The covered cut-word cells at depth two: the four residue classes of
the core mass modulo 27 whose cut word owns a Happy cell at row two —
digit two at the 9s place of `16 * core mod 27` with x4-carry
`⌊4·(7·core mod 9)/9⌋ ∈ {0, 3}`. -/
theorem omega_word_happy_row2 (a core : Nat) (ha : 2 ≤ a)
    (hcore : core % 27 = 5 ∨ core % 27 = 8 ∨
      core % 27 = 10 ∨ core % 27 = 13) :
    HappyCell (carry4 (omegaCutWord a core) 2)
        (digit3 (omegaCutWord a core) 2) := by
  have hw27 : omegaCutWord a core % 27 = 26 ∨ omegaCutWord a core % 27 = 20 ∨
      omegaCutWord a core % 27 = 25 ∨ omegaCutWord a core % 27 = 19 := by
    rw [omega_cut_word_mod27 a core ha]
    rcases hcore with h5 | h8 | h10 | h13 <;> omega
  have hw9 : omegaCutWord a core % 9 = 8 ∨ omegaCutWord a core % 9 = 2 ∨
      omegaCutWord a core % 9 = 7 ∨ omegaCutWord a core % 9 = 1 := by
    rw [omega_cut_word_mod9 a core (by omega : 1 ≤ a)]
    rcases hcore with h5 | h8 | h10 | h13 <;> omega
  have h9 : (3:Nat)^2 = 9 := by decide
  refine ⟨?_, ?_⟩
  · unfold digit3
    rw [h9]
    rcases hw27 with h | h | h | h <;> omega
  · unfold carry4
    rw [h9]
    rcases hw9 with h | h | h | h <;> omega

/-- **THE LEVEL-THREE HAPPY GATE.**  Every exponent `K = 3^a * core` with
`a ≥ 2` and core mass in the classes `{5, 8, 10, 13}` modulo 27 owns a
physical Happy row at row `a+3`.  The classes 10 and 13 are the new
content — the first full Happy cells inside the `core ≡ 1 (mod 3)` half
of the exponent space. -/
theorem omega_level3_happy_gate (a core : Nat) (ha : 2 ≤ a)
    (hcore : core % 27 = 5 ∨ core % 27 = 8 ∨
      core % 27 = 10 ∨ core % 27 = 13) :
    HappyCell (carry4 (4^(3^a * core)) (a+1+2))
        (digit3 (4^(3^a * core)) (a+1+2)) :=
  omega_happy_conjugation a core 2 (by omega : 1 ≤ a)
    (omega_word_happy_row2 a core ha hcore)

/-! ## Section 3 — the CommonTwo wiring (the master socket) -/

/-- **THE LEVEL-THREE FAMILY INTO THE MASTER SOCKET.**  Every exponent of
the level-three family owns a common-two row — the atomic input of the
creation master — through the green FromHappy bridge. -/
theorem commonTwo_of_omega_level3 (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧
      (core % 27 = 5 ∨ core % 27 = 8 ∨
        core % 27 = 10 ∨ core % 27 = 13) ∧
      K = 3^a * core) :
    GSTFourPowerDirectExistence.CommonTwo K := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine GSTFourPowerDirectExistenceFromHappy.happy_row_to_commonTwo
    K (a+1+2) (by omega) ?_
  rw [hKac]
  exact omega_level3_happy_gate a core ha hcore

/-- **THE CLASS-TWO FAMILY INTO THE MASTER SOCKET.**  The Ω-Wave Law's
class-two Happy gate, rewired through the same FromHappy bridge: both
infinite families now feed the identical atomic socket. -/
theorem commonTwo_of_omega_classTwo (K : Nat)
    (hK : GSTGraphV2OmegaWaveLaw.omegaClassTwo K) :
    GSTFourPowerDirectExistence.CommonTwo K := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine GSTFourPowerDirectExistenceFromHappy.happy_row_to_commonTwo
    K (a+1) (by omega) ?_
  rw [hKac]
  exact omega_cut_happy_gate a core ha hcore

/-! ## Section 4 — receipts -/

#check omega_happy_conjugation
#check omega_level3_happy_gate
#check commonTwo_of_omega_level3
#check commonTwo_of_omega_classTwo
#print axioms omega_happy_conjugation
#print axioms omega_level3_happy_gate
#print axioms commonTwo_of_omega_level3
#print axioms commonTwo_of_omega_classTwo

end GSTOmegaCellConjugation
