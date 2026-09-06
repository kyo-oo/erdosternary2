import GST.PublicAPI

/-!
# Public surface smoke check

This audit module keeps reviewer-facing `#check` commands out of the smallest
public API wrappers. It has no proof bodies and exists only to compile-check the
names exported by the professional shell.
-/

#check GST.Problem406.contains_two_digit_of_nine_le
#check GST.Arithmetic.digit3
#check GST.Arithmetic.Navigation
#check GST.Arithmetic.carry4
#check GST.Arithmetic.carry4_lt_four
#check GST.Arithmetic.carry4_forward_exact
#check GST.FourPower.CommonTwo
#check GST.FourPower.DirectExistence
#check GST.FourPower.exponentPrefix
#check GST.FourPower.exponentTrit
#check GST.FourPower.exponent_prefix_trit_decomposition
#check GST.FourPower.CreationCertificate
#check GST.FourPower.CreationMaster
#check GST.FourPower.creation_certificate_to_navigation
