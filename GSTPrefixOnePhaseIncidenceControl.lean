import GSTCanonicalEnergyControl
import GSTInfiniteCoupledLedger

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2
open GSTV2

/-!
# Canonical prefix-one phase-incidence coordinates

This module places the exact earliest horizontal chord in the same theorem as
the all-depth parent bad suffix and the coupled Past synchronization law.  It
does not identify the horizontal base-six chord code with the vertical
ternary Past coordinate: those are different observables.  Instead it records
the exact vertical Past equation forced by each of the two carry-correlated
chords.
-/

def gpt56PhaseA (s : Nat) : Nat := 4^(3^s)

def gpt56PhaseT (s n : Nat) : Nat :=
  gstNavigationConstant (s+1) n

def gpt56PhaseInitialState (s n : Nat) : GSTV2.CoupledState where
  parentSeed := 1
  parentOffset := c s / 3
  childResidue := 1 + 4 * (c s / 3)
  childCarry := 0
  childTail := gpt56PhaseT s n

def GPT56NullChord (s n q : Nat) : Prop :=
  gstDigit (gpt56PhaseT s n) q = 2 ∧
  gstCarry (gpt56PhaseT s n) q = 0 ∧
  GSTFirstBig1AtS
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 1 ∧
  gstBig1ProjectedPathCodeS
    (fun r => GSTPhysicalKernel.binaryColumnCarry
      (gpt56PhaseT s n) q r)
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 1 = 4 ∧
  Finset.sum (Finset.range 1)
    (fun r => GSTPhysicalKernel.signedKernelTwice
      (GSTPhysicalKernel.binaryColumnCarry (gpt56PhaseT s n) q r)
      (GSTPhysicalKernel.binaryColumnDigit (gpt56PhaseT s n) q r)) =
        (-14 : Int)

def GPT56PlusChord (s n q : Nat) : Prop :=
  gstDigit (gpt56PhaseT s n) q = 2 ∧
  gstCarry (gpt56PhaseT s n) q = 3 ∧
  GSTFirstBig1AtS
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 3 ∧
  gstBig1ProjectedPathCodeS
    (fun r => GSTPhysicalKernel.binaryColumnCarry
      (gpt56PhaseT s n) q r)
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 3 = 179 ∧
  Finset.sum (Finset.range 3)
    (fun r => GSTPhysicalKernel.signedKernelTwice
      (GSTPhysicalKernel.binaryColumnCarry (gpt56PhaseT s n) q r)
      (GSTPhysicalKernel.binaryColumnDigit (gpt56PhaseT s n) q r)) = 0

theorem gpt56_phase_initial_residue_lt
    (s : Nat) (hs : 1 ≤ s) :
    1 + 4 * (c s / 3) < gpt56PhaseA s := by
  have hcmod : c s % 3 = 1 := c_mod3 s hs
  have hcne : c s ≠ 0 := by
    intro h0
    rw [h0] at hcmod
    norm_num at hcmod
  have hcpos : 0 < c s := Nat.pos_of_ne_zero hcne
  have hcdiv : c s / 3 ≤ c s := Nat.div_le_self _ _
  have h4 : 4 * (c s / 3) ≤ 4 * c s :=
    Nat.mul_le_mul_left 4 hcdiv
  have h49 : 4 * c s < 9 * c s := by omega
  have hpow : 9 ≤ 3^(s+1) := by
    have h : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h ⊢
    exact h
  have h9A : 9 * c s ≤ 3^(s+1) * c s :=
    Nat.mul_le_mul_right (c s) hpow
  have hLTE := lte_identity s hs
  unfold gpt56PhaseA
  rw [hLTE]
  omega

theorem gpt56_phase_initial_invariant
    (s n : Nat) (hs : 1 ≤ s) :
    GSTV2.CoupledInvariant (gpt56PhaseA s)
      (gpt56PhaseInitialState s n) := by
  constructor
  · simp [gpt56PhaseInitialState]
  · simpa [gpt56PhaseInitialState] using
      gpt56_phase_initial_residue_lt s hs

theorem gpt56_phase_bad_to_v2_seeded
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.SeededBadTrace 1
      ((gpt56PhaseInitialState s n).parentWord (gpt56PhaseA s)) := by
  have hold := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
  have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
    rw [Nat.pow_one, c_mod3 s hs]
    decide
  rw [hseed] at hold
  simpa [GSTV2.SeededBadTrace, GSTV2.Happy, GSTV2.affineCarry,
    GSTV2.digit, GSTV2.CoupledState.parentWord,
    gpt56PhaseInitialState, gpt56PhaseA, gpt56PhaseT,
    GSTSeededAffineBadTrace, GSTBadPair, gstAffineMulCarry, gstDigit] using hold

theorem gpt56_phase_infinite_bad_control
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.InfiniteBadCoupledControl
      (gpt56PhaseA s) (gpt56PhaseInitialState s n) := by
  apply GSTV2.infinite_bad_coupled_control
  · unfold gpt56PhaseA
    exact Nat.pow_pos (by decide)
  · exact gpt56_phase_initial_invariant s n hs
  · rfl
  · exact gpt56_phase_bad_to_v2_seeded s n hs hBad

/-!
At the reindexed earliest gate, the NULL and GST+ signatures give different
exact vertical Past equations.  The parent bad suffix and the all-depth
synchronization equation are retained at that same coordinate.
-/
theorem gpt56_prefix_one_exact_gate_past_incidence
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (gpt56PhaseInitialState s n).parentPast (gpt56PhaseA s) q +
          3^q *
            (GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).childResidue =
        (gpt56PhaseInitialState s n).childResidue +
          gpt56PhaseA s * (gpt56PhaseInitialState s n).childPast q ∧
      GSTV2.SeededBadTrace
        (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed
        ((GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentWord (gpt56PhaseA s)) ∧
      ((GPT56NullChord s n q ∧
          (gpt56PhaseInitialState s n).childPast q =
            4 * (gpt56PhaseT s n % 3^q)) ∨
       (GPT56PlusChord s n q ∧
          (gpt56PhaseInitialState s n).childPast q + 3 * 3^q =
            4 * (gpt56PhaseT s n % 3^q))) := by
  have hpacket := gpt56_prefix_one_live_exact_chord_energy_packet
    s n hs hn (by simpa [gpt56PhaseT] using hchild) hBad
  dsimp only at hpacket
  obtain ⟨q, hchord, _hseeded, _henergy⟩ := hpacket
  have hcontrol := gpt56_phase_infinite_bad_control s n hs hBad
  have hsync := GSTV2.coupledOrbit_past_synchronization
    (gpt56PhaseA s) (gpt56PhaseInitialState s n)
    (by unfold gpt56PhaseA; exact Nat.pow_pos (by decide))
    (gpt56_phase_initial_invariant s n hs) q
  refine ⟨q, hsync, hcontrol.parentBadSuffix q, ?_⟩
  rcases hchord with hnull | hplus
  · have hdiv :
        (4 * (gpt56PhaseT s n % 3^q)) / 3^q = 0 := by
      simpa [gpt56PhaseT, gstCarry] using hnull.2.1
    have hdecomp := Nat.mod_add_div
      (4 * (gpt56PhaseT s n % 3^q)) (3^q)
    rw [hdiv] at hdecomp
    have hmod :
        (4 * (gpt56PhaseT s n % 3^q)) % 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa using hdecomp
    have hpast :
        (gpt56PhaseInitialState s n).childPast q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa [GSTV2.CoupledState.childPast, GSTV2.seededPast,
        gpt56PhaseInitialState] using hmod
    exact Or.inl ⟨by simpa [GPT56NullChord, gpt56PhaseT] using hnull, hpast⟩
  · have hdiv :
        (4 * (gpt56PhaseT s n % 3^q)) / 3^q = 3 := by
      simpa [gpt56PhaseT, gstCarry] using hplus.2.1
    have hdecomp := Nat.mod_add_div
      (4 * (gpt56PhaseT s n % 3^q)) (3^q)
    rw [hdiv] at hdecomp
    have hmod :
        (4 * (gpt56PhaseT s n % 3^q)) % 3^q + 3 * 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      omega
    have hpast :
        (gpt56PhaseInitialState s n).childPast q + 3 * 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa [GSTV2.CoupledState.childPast, GSTV2.seededPast,
        gpt56PhaseInitialState] using hmod
    exact Or.inr ⟨by simpa [GPT56PlusChord, gpt56PhaseT] using hplus, hpast⟩

#check gpt56_prefix_one_exact_gate_past_incidence
#print axioms gpt56_prefix_one_exact_gate_past_incidence
