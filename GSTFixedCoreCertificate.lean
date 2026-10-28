import GSTWorldtraceTowerWindow

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Kernel-checkable finite Worldtrace coefficient certificate
Exact 18-trit computation on every u in 1..566 with no native_decide.
Its unlimited-scale extension is proved separately from GST tower-window
and coefficient stabilization. This module isolates only finite arithmetic.
-/

namespace GSTFixedCoreCertificate

/-- Stable GST LTE coefficient residue c_17 modulo 3^18. -/
def coeff18 : Nat := 235352482

def witnessAt (u k : Nat) : Bool :=
  ((u * coeff18) / 3^k) % 3 == 2

def allCore566 : Bool :=
  (List.range 566).all (fun v =>
    (List.range 18).any (fun k => witnessAt (v+1) k))

/-- Full 566-multiplier finite certificate, checked by Lean's kernel;
there are 566 times 18 bounded exact digit computations. -/
theorem all_core_566 : allCore566 = true := by decide

#print axioms all_core_566

end GSTFixedCoreCertificate
