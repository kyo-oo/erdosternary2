import GSTProblem406CarryEntropyBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Sharpened GST physical survivor measure exponent

The previously verified 7-of-9 two-step bound gives asymptotic
survivor dimension exponent log(7)/log(9) ~ 0.886.
A positive supersolution w=(4,6,6,5) of the four-state
carry transfer matrix satisfies 2 M w <= 5 w coordinatewise.

Consequently the exact physical initial carry 1 survivor count
satisfies 2^n S_n(1) <= 6 * 5^n for EVERY n.
This is a stronger bound: S_n(1) <= 6*(5/2)^n, giving
counting exponent log_3(5/2) ~ 0.834.

It remains compatible with an exceptional sparse natural exponent set;
this is quantitative structure, not pointwise universal hGate.
-/

namespace GSTProblem406CarryEntropySharp

open GSTProblem406CarryEntropyBound

def weight (c : Nat) : Nat :=
  if c=0 then 4 else if c=1 then 6 else if c=2 then 6 else 5

theorem positive_weight (c : Nat) (hc : c<4) :
    0<weight c := by
  interval_cases c <;> decide

/-- Exact rational Perron supersolution: 2 M w <= 5 w.
The four rows of the controller act as (0+1),(0+1+3),
(0+2+3),(1+2). -/
theorem uniform_weighted_drift (c : Nat) (hc : c<4) :
    (if c=0 then 2*(weight 0+weight 1)
     else if c=1 then 2*(weight 0+weight 1+weight 3)
     else if c=2 then 2*(weight 0+weight 2+weight 3)
     else 2*(weight 1+weight 2))
      ≤ 5*weight c := by
  interval_cases c <;> decide

/-- All four carry states obey the strict rational exponential
upper bound, using only original exact counts and a positive drift. -/
theorem five_halves_survivor_bound (n : Nat) :
    ∀ c : Nat, c<4 →
      2^n * survivingCount n c ≤ 5^n * weight c := by
  induction n with
  | zero =>
      intro c hc
      interval_cases c <;> norm_num [survivingCount,weight]
  | succ n ih =>
      have h0 := ih 0 (by decide)
      have h1 := ih 1 (by decide)
      have h2 := ih 2 (by decide)
      have h3 := ih 3 (by decide)
      intro c hc
      interval_cases c
      · simp only [survivingCount]
        simp only [weight, if_pos, if_neg, pow_succ] at *
        nlinarith [h0,h1]
      · simp only [survivingCount]
        simp only [weight, if_pos, if_neg, pow_succ] at *
        nlinarith [h0,h1,h3]
      · simp only [survivingCount]
        simp only [weight, if_pos, if_neg, pow_succ] at *
        nlinarith [h0,h2,h3]
      · simp only [survivingCount]
        simp only [weight, if_pos, if_neg, pow_succ] at *
        nlinarith [h1,h2]

/-- Strong exact original physical exponent-prefix survival bound. -/
theorem original_physical_five_halves_bound (n : Nat) :
    2^n * survivingCount n 1 ≤ 6 * 5^n := by
  have h := five_halves_survivor_bound n 1 (by decide)
  simpa [weight, Nat.mul_comm] using h

/-- The old 7-of-9 upper estimate and the new 5/2 estimate apply
simultaneously and are not extrapolated across quantifiers. -/
theorem original_physical_two_upper_envelopes (m : Nat) :
    survivingCount (2*m) 1 ≤ 7^m ∧
    2^(2*m) * survivingCount (2*m) 1 ≤ 6*5^(2*m) :=
  ⟨original_affine_pair_survivor_bound m,
   original_physical_five_halves_bound (2*m)⟩

#print axioms positive_weight
#print axioms uniform_weighted_drift
#print axioms five_halves_survivor_bound
#print axioms original_physical_five_halves_bound
#print axioms original_physical_two_upper_envelopes

end GSTProblem406CarryEntropySharp
