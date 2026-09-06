import GST.Problem406.PublicAPI
import GST.Arithmetic.TernaryDigits
import GST.Arithmetic.Carries
import GST.FourPower.CommonTwo
import GST.FourPower.PrefixLaw
import GST.FourPower.Certificate

/-!
# General Space Theory compatibility API

This module preserves the historical `GST.*` public imports used by the checked
proof corpus.

For the whole mathematical framework, use `Worldtrace.PublicAPI`.  General Space
Theory is the navigation-geometric pillar inside Worldtrace Arithmetic; the
Problem 406 proof also uses ternary event arithmetic, carry-information theory,
residue tower laws, four-power dynamics, collision/wave closure, phase-cycle
transport, and finite certificate kernels.
-/
