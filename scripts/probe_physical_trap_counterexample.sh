#!/usr/bin/env bash
set -euxo pipefail
SNAP="$PWD/ker07-snapshot/branches/15_sol_new__physical-phase-crossing-surgery"
cat > CanonicalPhysicalTrapCounterexampleProbe.lean <<'EOF'
import ErdosPreOmega
import InformationRegenerationScratch
import StripConservationScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Local copy of the RED physical-trap certificate, isolated so the probe does
not import the deliberately unclosed CanonicalPhaseCrossingSurgeryScratch. -/
def GSTCanonicalPhysicalTrapProbeS
    (Q : Nat → Nat → Nat) (s n c z : Nat) : Prop :=
  ∃ q,
    let N := 3^s
    let A := 4^N
    let T := Q (s+1) n
    let D := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
    let Z := gstAffineMulCarryS A z T (q+1)
    let W := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
    let C := gstAffineMulCarryS 4 0 T (q+1)
    let Y := T / 3^(q+1)
    let S := D + 4*Z
    GSTSeededBadTraceS D (Z + A*Y) ∧
      GSTSeededBadTraceS C Y ∧
      (C = 2 ∨ C = 3) ∧
      S = W + A*C ∧
      W < A ∧
      S = gstWideCarryS
        (4^(N+1)) (4^(3^(s+1)*n)) (s+2+(q+1)) ∧
      S / 3^(2*N) = 0

theorem probe_seed3_word4_bad : GSTSeededBadTraceS 3 4 := by
  intro j
  by_cases hj : j ≤ 1
  · interval_cases j <;>
      norm_num [GSTSeededBadTraceS, GSTBadPairS, gstAffineMulCarryS, gstDigitS]
  · have hj2 : 2 ≤ j := by omega
    have hp : 3^2 ≤ 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hj2
    have hdiv : 4 / 3^j = 0 := Nat.div_eq_of_lt (by norm_num at hp ⊢; omega)
    unfold GSTBadPairS
    simp [gstDigitS, hdiv]

theorem probe_seed3_word306_bad : GSTSeededBadTraceS 3 306 := by
  intro j
  by_cases hj : j ≤ 5
  · interval_cases j <;>
      norm_num [GSTSeededBadTraceS, GSTBadPairS, gstAffineMulCarryS, gstDigitS]
  · have hj6 : 6 ≤ j := by omega
    have hp : 3^6 ≤ 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hj6
    have hdiv : 306 / 3^j = 0 := Nat.div_eq_of_lt (by norm_num at hp ⊢; omega)
    unfold GSTBadPairS
    simp [gstDigitS, hdiv]

theorem probe_canonical_physical_trap_s1_n4 :
    GSTCanonicalPhysicalTrapProbeS gstNavigationConstant 1 4 7 2 := by
  refine ⟨40, ?_⟩
  dsimp only
  have hconcrete :
      GSTSeededBadTraceS 3 306 ∧
      GSTSeededBadTraceS 3 4 ∧
      (3 = 2 ∨ 3 = 3) ∧
      203 = 11 + 64*3 ∧
      11 < 64 ∧
      203 = gstWideCarryS 256 (4^36) 44 ∧
      203 / 3^6 = 0 := by
    refine ⟨probe_seed3_word306_bad, probe_seed3_word4_bad, ?_⟩
    norm_num [gstWideCarryS]
  simpa [gstNavigationConstant, gstAffineMulCarryS] using hconcrete

def GSTCanonicalPrefixOnePhysicalTrapImpossibleProbeS : Prop :=
  ∀ (Q : Nat → Nat → Nat),
    GSTCanonicalOriginEnergyS Q →
    ∀ s n c z,
      1 ≤ s → 1 ≤ n →
      4^(3^s) = 1 + 3^(s+1)*c →
      c = 1 + 3*z →
      ¬ GSTCanonicalPhysicalTrapProbeS Q s n c z

theorem probe_physical_trap_impossibility_is_false :
    ¬ GSTCanonicalPrefixOnePhysicalTrapImpossibleProbeS := by
  intro h
  have hA : 4^(3^1) = 1 + 3^(1+1)*7 := by norm_num
  have hc : 7 = 1 + 3*2 := by norm_num
  exact (h gstNavigationConstant gst_navigation_constant_origin_energyS
    1 4 7 2 (by decide) (by decide) hA hc)
    probe_canonical_physical_trap_s1_n4

#check probe_canonical_physical_trap_s1_n4
#check probe_physical_trap_impossibility_is_false
#print axioms probe_physical_trap_impossibility_is_false
EOF
LEAN_PATH="$SNAP:$PWD:${LEAN_PATH:-}" lake env lean CanonicalPhysicalTrapCounterexampleProbe.lean | tee physical-trap-counterexample.log
! grep -E 'sorryAx|declaration uses .*[Ss]orry' physical-trap-counterexample.log
