import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact kernel-verifiable GST coefficient c_17 modulo 3^18
Never expand the huge number 4^(3^17). Instead propagate a tiny modular
coefficient by the exact GST cubic recursion and a polynomial congruence law.
-/
namespace GSTWorldtraceCoeff18Compute

open GSTCanonicalTailLTE

def modulus : Nat := 3^18

def residueCoeff : Nat → Nat
 | 0 => 1
 | n+1 =>
   let x := residueCoeff n
   (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus

private theorem polynomial_mod (n x y : Nat)
    (h : x%modulus=y%modulus) :
    (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus =
    (y+3^(n+1)*y^2+3^(2*n+1)*y^3)%modulus := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [h]

theorem residue_coeff_correct (n : Nat) :
    residueCoeff n = lteCoeff n%modulus := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have h : residueCoeff n%modulus=lteCoeff n%modulus := by
        rw [ih]
        simp only [Nat.mod_mod]
      have hp := polynomial_mod n (residueCoeff n) (lteCoeff n) h
      change
        (residueCoeff n +3^(n+1)*(residueCoeff n)^2+
          3^(2*n+1)*(residueCoeff n)^3)%modulus =
        (lteCoeff n +3^(n+1)*(lteCoeff n)^2+
          3^(2*n+1)*(lteCoeff n)^3)%modulus
      exact hp

/-- A finite 18-step modular-recurrence computation, not huge raw powers. -/
theorem residue_coeff17 :
    residueCoeff 17 = 235352482 := by decide

/-- Fully kernel-certified GST stable-coefficient value c_17 modulo 3^18. -/
theorem coeff17_exact_mod18 :
    lteCoeff 17 % 3^18 = 235352482 := by
  calc
    lteCoeff 17 % 3^18 = residueCoeff 17 :=
      (residue_coeff_correct 17).symm
    _ = 235352482 := residue_coeff17

#print axioms residue_coeff_correct
#print axioms residue_coeff17
#print axioms coeff17_exact_mod18

end GSTWorldtraceCoeff18Compute
