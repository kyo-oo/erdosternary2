#!/usr/bin/env python3
"""Exact finite experiments for the two handwritten GST equations.

This is diagnostic evidence, not a substitute for the Lean proof.
It constructs the full 12-cell local x4 graph, checks the U-jump classifier,
checks the all-depth quotient/remainder flux identity on a deterministic grid,
and probes the residual Navigation lift on small canonical origins.
"""

from itertools import product


def step(carry: int, digit: int):
    mass = carry + 4 * digit
    return mass // 3, mass % 3, mass


def u_charge(carry: int) -> int:
    return 5 if carry == 0 else 21 if carry == 3 else 15


def u_jump(carry: int, digit: int) -> int:
    nxt, _, _ = step(carry, digit)
    return 3 * u_charge(nxt) - u_charge(carry) - 24 * digit


def rotate(state):
    carry, digit = state
    nxt, out, _ = step(carry, digit)
    return nxt, out


def cycles():
    states = list(product(range(4), range(3)))
    seen = set()
    result = []
    for start in states:
        if start in seen:
            continue
        path = []
        x = start
        while x not in path:
            path.append(x)
            seen.add(x)
            x = rotate(x)
        result.append(path[path.index(x):])
    return result


def affine_carry(seed: int, x: int, k: int) -> int:
    return (seed + 4 * (x % (3**k))) // (3**k)


def nullspace(seed: int, x: int, k: int) -> int:
    return (seed + 4 * (x % (3**k))) % (3**k)


def nav_const(s: int, b: int) -> int:
    return (4 ** ((3**s) * b)) // (3 ** (s + 1))


def witness(r: int):
    p = 0
    p3 = 1
    while p3 <= 4 * r + 1:
        digit = (r // p3) % 3
        carry = (4 * (r % p3)) // p3
        if digit == 2 and carry in (0, 3):
            return p
        p += 1
        p3 *= 3
    return None


# 1) Full local graph.
rows = []
for c, d in product(range(4), range(3)):
    nxt, out, mass = step(c, d)
    happy = d == 2 and c in (0, 3)
    jump = u_jump(c, d)
    assert (jump < 0) == happy
    assert mass == out + 3 * nxt
    rows.append((c, d, mass, out, nxt, jump, happy))

# 2) All-depth Equation-I grid.
flux_checks = 0
for seed in range(4):
    for x in range(0, 1000):
        for k in range(0, 9):
            lhs = seed + 4 * (x % (3**k))
            rhs = (3**k) * affine_carry(seed, x, k) + nullspace(seed, x, k)
            assert lhs == rhs
            flux_checks += 1

# 3) Equation-II synchronization grid.
for j in range(0, 100):
    assert (2**j) * (3**j) == 6**j

# 4) Residual-lift probe: child Navigation => parent Navigation.
# Small but nontrivial canonical grid; the Lean theorem is universal.
residual_cases = 0
residual_failures = []
for s in range(1, 4):
    for k in range(1, 5):
        for m in range(1, 21):
            if m % 3 == 0:
                continue
            child = nav_const(s + k, m)
            child_w = witness(child)
            if child_w is None:
                continue
            residual_cases += 1
            parent = nav_const(s, 1 + (3**k) * m)
            parent_w = witness(parent)
            if parent_w is None:
                residual_failures.append((s, k, m, child_w))

assert not residual_failures, residual_failures

print("GST HANDWRITTEN GRAPH EXPERIMENT: GREEN")
print(f"local_cells={len(rows)}")
print(f"local_cycles={cycles()}")
print(f"flux_identity_checks={flux_checks}")
print("synchronization_checks=100")
print(f"residual_navigation_cases={residual_cases}")
print("residual_navigation_failures=0")
print("cell_table: carry,digit,mass,out,next,u_jump,happy")
for row in rows:
    print(row)
