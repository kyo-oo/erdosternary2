import GST.Problem406.PublicAPI
import GST.Arithmetic.TernaryDigits
import GST.Arithmetic.Carries
import GST.FourPower.CommonTwo
import GST.FourPower.PrefixLaw
import GST.FourPower.Certificate

/-!
# GST public API

Reviewer-facing imports for the Problem 406 formalization.

This umbrella module exposes clean public namespaces while preserving the proof
artifact and internal modules.  The theorem universe is indexed separately; this
API promotes only the mathematical spine and stable bridge statements.
-/
