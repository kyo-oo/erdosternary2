import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectExistence
import GSTFourPowerDirectAdditionCarry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectCreationMaster

open GSTFourPowerOntologicalAdapter
open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry

/-- A direct common-two row is already exactly the historical creation
certificate on the source four-power.  This is the positive algebraic bridge:
the source row has digit two, and the target digit-two equation forces the
multiplication carry to be zero modulo three.  No navigation, collision, or
phase-window contradiction is used. -/
theorem commonTwo_to_creation_certificate
    (K : Nat) (h : CommonTwo K) :
    CreationCertificate (4^K) := by
  rcases h with ⟨p, hp, hsrc, htgt⟩
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTFourPowerDirectResidue.digit3] using hsrc
  · have htgtMul : digit3 (4 * (4^K)) p = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htgt
    have hformula := digit3_four_mul (4^K) p
    rw [hsrc, htgtMul] at hformula
    let c := directCarry4 (4^K) p
    have hcLt : c < 4 := by
      dsimp [c]
      exact directCarry4_lt_four (4^K) p
    have hcEq : (2 + c) % 3 = 2 := by
      dsimp [c]
      exact hformula.symm
    have hcMod : c % 3 = 0 := by
      interval_cases c
      · norm_num
      · norm_num at hcEq
      · norm_num at hcEq
      · norm_num
    left
    dsimp [c] at hcMod
    simpa [directCarry4] using hcMod

/-- The historical creation certificate is not weaker than direct existence.
In its carry-zero branch the same row is already common-two.  In its carry-one
branch the exact carry recurrence sends carry one plus source digit two to
carry three one row later, while the certificate supplies digit two there;
that next row is therefore common-two. -/
theorem creation_certificate_to_commonTwo
    (K : Nat) (h : CreationCertificate (4^K)) :
    CommonTwo K := by
  rcases h with ⟨p, hp, hsrcRaw, hcase⟩
  have hsrc : digit3 (4^K) p = 2 := by
    simpa [GSTFourPowerDirectResidue.digit3] using hsrcRaw
  rcases hcase with hzero | hone
  · have hcmod : directCarry4 (4^K) p % 3 = 0 := by
      simpa [directCarry4] using hzero
    have hclt : directCarry4 (4^K) p < 4 :=
      directCarry4_lt_four (4^K) p
    have hc : directCarry4 (4^K) p = 0 ∨ directCarry4 (4^K) p = 3 := by
      omega
    have htMul : digit3 (4 * (4^K)) p = 2 := by
      rw [digit3_four_mul, hsrc]
      rcases hc with h0 | h3
      · rw [h0]
        norm_num
      · rw [h3]
        norm_num
    have ht : digit3 (4^(K+1)) p = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htMul
    exact ⟨p, hp, hsrc, ht⟩
  · have hcmod : directCarry4 (4^K) p % 3 = 1 := by
      simpa [directCarry4] using hone.1
    have hclt : directCarry4 (4^K) p < 4 :=
      directCarry4_lt_four (4^K) p
    have hc : directCarry4 (4^K) p = 1 := by
      omega
    have hnext := directCarry4_forward_exact_all (4^K) p
    have hcnext : directCarry4 (4^K) (p+1) = 3 := by
      rw [hc, hsrc] at hnext
      norm_num at hnext
      exact hnext
    have hsrcNext : digit3 (4^K) (p+1) = 2 := by
      simpa [GSTFourPowerDirectResidue.digit3] using hone.2
    have htMulNext : digit3 (4 * (4^K)) (p+1) = 2 := by
      rw [digit3_four_mul, hsrcNext, hcnext]
      norm_num
    have htNext : digit3 (4^(K+1)) (p+1) = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htMulNext
    exact ⟨p+1, by omega, hsrcNext, htNext⟩

/-- The direct arithmetic existence theorem supplies the exact historical
four-power creation master.  This is the production-facing replacement for the
old collision/navigation route. -/
theorem directExistence_to_creation_master
    (hDirect : FourPowerDirectExistence) :
    FourPowerCreationMaster := by
  intro K hK5 hK7
  exact commonTwo_to_creation_certificate K (hDirect K hK5 hK7)

/-- Conversely, any genuine creation master already supplies the direct
same-position common-two law. -/
theorem creationMaster_to_directExistence
    (hMaster : FourPowerCreationMaster) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  exact creation_certificate_to_commonTwo K (hMaster K hK5 hK7)

/-- The two production seam formulations are mathematically equivalent. -/
theorem directExistence_iff_creationMaster :
    FourPowerDirectExistence ↔ FourPowerCreationMaster :=
  ⟨directExistence_to_creation_master, creationMaster_to_directExistence⟩

#check commonTwo_to_creation_certificate
#check creation_certificate_to_commonTwo
#check directExistence_to_creation_master
#check creationMaster_to_directExistence
#print axioms commonTwo_to_creation_certificate
#print axioms creation_certificate_to_commonTwo
#print axioms directExistence_to_creation_master
#print axioms creationMaster_to_directExistence
#print axioms directExistence_iff_creationMaster

end GSTFourPowerDirectCreationMaster
