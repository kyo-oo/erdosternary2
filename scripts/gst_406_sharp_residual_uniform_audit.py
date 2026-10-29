#!/usr/bin/env python3
"""Independent exact-integer finite audit of sharp GST physical exponent residual.

Tests all K in [4, 250000) with K % 9 == 4.
For m=v3(2*K+1), q=(2*K+1)/3^m, verify
  ((4^K-1)/3 - K) mod 3^(m+3) == 3^(m+2)*(q mod 3).
This implies the asserted exact valuation m+2 in this finite range.

Does not infer the theorem for K>=250000 or imply CommonTwo.
Original powers are represented with pow(4,K,3^(m+4)); no floating point.
"""
from __future__ import annotations

def audit() -> None:
    checked = 0
    max_m = 0
    for k in range(4, 250000, 9):
        n = 2*k+1
        m = 0
        while n % 3 == 0:
            n //= 3
            m += 1
        assert m >= 2 and n % 3 != 0
        mod = 3**(m+3)
        source_quotient = (pow(4, k, 3*mod)-1)//3
        residue = (source_quotient-k) % mod
        expected = 3**(m+2)*(n%3)
        assert residue == expected, (k,m,n,residue,expected)
        checked += 1
        max_m = max(max_m,m)
    assert checked == len(range(4,250000,9))
    print("GST406_SHARP_PHYSICAL_RESIDUAL_FINITE_AUDIT_PASS=1")
    print(f"tested={checked}; K range=[4,250000); K mod9=4; max_valuation={max_m}")
    print("unbounded_K_proved_by_this_script=NO")
    print("original_CommonTwo_proved_by_this_script=NO")

if __name__ == "__main__":
    audit()
