#!/usr/bin/env python3
"""Exact finite original-power digit audit for GST Erdős #406.

Claim tested (finite only):
Every integer 5 <= K < 1_000_000, K != 7, has a common ternary 2 in
the original physical powers 4^K and 4^(K+1) at a row p < 120.

Method: integer modular recurrence modulo 3^120, exact repeated base-3
division, independent modular exponentiation spot checks. No floating point,
no sampling in the population, no inferred statement for K >= 1_000_000.
"""
from __future__ import annotations

MAX_EXPONENT = 1_000_000  # exclusive
ROWS = 120
MODULUS = 3**ROWS
EXPECTED_NO_HIT = [0, 1, 2, 3, 4, 7]
EXPECTED_MAXIMUM = (181_406, 81)


def full_integer_first_hit(k: int) -> int | None:
    """Exact all-digit check for tiny exceptional powers, no row cutoff."""
    source, neighbor, row = 4**k, 4**(k+1), 0
    while source or neighbor:
        if source % 3 == 2 and neighbor % 3 == 2:
            return row
        source //= 3
        neighbor //= 3
        row += 1
    return None


def audit() -> None:
    residue = 1  # 4^0 modulo 3^120
    no_hit: list[int] = []
    latest = (-1, -1)
    checked = 0
    for k in range(MAX_EXPONENT):
        neighbor = (4*residue) % MODULUS
        # Independently guard the recurrence against updates/integer mistakes.
        if k % 10000 == 0:
            assert residue == pow(4, k, MODULUS), ("source residue", k)
            assert neighbor == pow(4, k+1, MODULUS), ("neighbor residue", k)
        a, b = residue, neighbor
        first: int | None = None
        for row in range(ROWS):
            if a % 3 == 2 and b % 3 == 2:
                first = row
                break
            a //= 3
            b //= 3
        if first is None:
            no_hit.append(k)
        elif first > latest[1]:
            latest = (k, first)
        residue = neighbor
        checked += 1
    assert checked == MAX_EXPONENT, checked
    assert no_hit == EXPECTED_NO_HIT, ("finite-survivor list", no_hit)
    assert latest == EXPECTED_MAXIMUM, ("latest first hit", latest)
    for k in EXPECTED_NO_HIT:
        assert full_integer_first_hit(k) is None, ("tiny exception", k)
    assert pow(4, 181_406, 3**82) // 3**81 == 2
    assert pow(4, 181_407, 3**82) // 3**81 == 2
    print("EXHAUSTIVE_ORIGINAL_PHYSICAL_406_FINITE_PASS=1")
    print(f"range=0..{MAX_EXPONENT-1}, digit_rows=0..{ROWS-1}, checked={checked}")
    print(f"no_hit_within_120_rows={no_hit}")
    print(f"maximum_first_hit_row={latest[1]}, exponent={latest[0]}")
    print("universal_claim_for_all_K=NOT_TESTED")


if __name__ == "__main__":
    audit()
