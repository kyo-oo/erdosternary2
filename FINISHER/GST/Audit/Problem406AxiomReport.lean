import GST.Problem406.PublicAPI

/-!
# Problem 406 axiom report

This audit module centralizes axiom-printing commands for the public Problem 406
surface. It is intentionally separate from the reviewer-facing API wrapper so
that the public theorem file stays calm while CI can still expose the trusted
kernel boundary.
-/

#check erdos_ternary_2_universal
#print axioms erdos_ternary_2_universal

#check GST.Problem406.contains_two_digit_of_nine_le
#print axioms GST.Problem406.contains_two_digit_of_nine_le
