#!/usr/bin/env python3
"""
GST Graph V2 canonical-origin experiment.

This is an exact finite arithmetic model of the Sol V2 objects already proved
in the Lean scratch tree.  It is deliberately NOT a proof of the final Erdős
theorem.  Its job is to preserve all coordinates that the old line-8574
bad-reflection seam discarded:

  * canonical origin n and level s,
  * retained affine offset / multiplier,
  * parent seed,
  * the single shared information carrier S_q,
  * child + parent physical GST coordinates,
  * macro base-4 rotation,
  * exact finite natural-origin termination.

No floating point and no external packages are used.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Optional


def A(s: int) -> int:
    assert s >= 0
    return 4 ** (3 ** s)


def c(s: int) -> int:
    return (A(s) - 1) // (3 ** (s + 1))


def z(s: int) -> int:
    cs = c(s)
    assert cs % 3 == 1
    return (cs - 1) // 3


def Q(s: int, n: int) -> int:
    assert s >= 0 and n >= 0
    if n == 0:
        return 0
    As = A(s)
    return c(s) * ((As**n - 1) // (As - 1))


def trit(x: int, q: int) -> int:
    return (x // (3**q)) % 3


def affine_carry(mult: int, seed: int, x: int, q: int) -> int:
    return (seed + mult * (x % (3**q))) // (3**q)


def gst_carry(x: int, q: int) -> int:
    return affine_carry(4, 0, x, q)


def seeded_happy(seed: int, x: int, q: int) -> bool:
    d = trit(x, q)
    C = affine_carry(4, seed, x, q)
    return d == 2 and C in (0, 3)


def first_seeded_happy(seed: int, x: int, max_q: int) -> Optional[int]:
    for q in range(max_q + 1):
        if seeded_happy(seed, x, q):
            return q
    return None


def hard_tail(s: int, n: int) -> int:
    return z(s) + A(s) * Q(s + 1, n)


def parent_navigation(s: int, n: int) -> int:
    return 1 + 3 * hard_tail(s, n)


def child_navigation(s: int, n: int) -> int:
    return Q(s + 1, n)


def shared_carrier(s: int, n: int, q: int) -> int:
    """S_q = affineCarry_(4A,1+4z)(T,q), exactly InformationStateScratch."""
    As = A(s)
    zs = z(s)
    T = child_navigation(s, n)
    return affine_carry(4 * As, 1 + 4 * zs, T, q)


def validate_shared_carrier(s: int, n: int, q: int) -> None:
    As = A(s)
    zs = z(s)
    T = child_navigation(s, n)
    H = hard_tail(s, n)
    S = shared_carrier(s, n, q)

    D = affine_carry(4, 1, H, q)
    Z = affine_carry(As, zs, T, q)
    assert S == D + 4 * Z
    assert S % 4 == D
    assert S // 4 == Z
    assert S // As == gst_carry(T, q)

    d = trit(T, q)
    S1 = shared_carrier(s, n, q + 1)
    assert S1 == (S + (4 * As) * d) // 3


def macro_rotate(A_: int, S: int) -> int:
    """One aligned base-4 macro re-coordinate rho_A(S)."""
    return S // 4 + A_ * (S % 4)


def macro_cycle(A_: int, S: int, steps: int) -> list[int]:
    out = [S]
    for _ in range(steps):
        S = macro_rotate(A_, S)
        out.append(S)
    return out


@dataclass(frozen=True)
class OriginState:
    ell: int
    n: int
    alpha: int
    beta: int
    seed: int
    depth: int


@dataclass(frozen=True)
class OriginStep:
    before: OriginState
    origin_trit: int
    emitted_trit: int
    parent_output_trit: int
    after: OriginState


def initial_origin_state(s: int, n: int) -> OriginState:
    return OriginState(
        ell=s + 1,
        n=n,
        alpha=z(s),
        beta=A(s),
        seed=1,
        depth=0,
    )


def origin_step(st: OriginState) -> OriginStep:
    assert st.n > 0
    r = st.n % 3
    u = st.n // 3

    E = st.alpha + st.beta * Q(st.ell, r)
    d = E % 3
    alpha1 = E // 3
    beta1 = st.beta * (A(st.ell) ** r)

    parent_out = (st.seed + 4 * d) % 3
    seed1 = (st.seed + 4 * d) // 3

    aft = OriginState(
        ell=st.ell + 1,
        n=u,
        alpha=alpha1,
        beta=beta1,
        seed=seed1,
        depth=st.depth + 1,
    )

    lhs = st.alpha + st.beta * Q(st.ell, st.n)
    rhs = d + 3 * (alpha1 + beta1 * Q(st.ell + 1, u))
    assert lhs == rhs

    return OriginStep(st, r, d, parent_out, aft)


def exhaust_origin(s: int, n: int) -> tuple[OriginState, list[OriginStep]]:
    st = initial_origin_state(s, n)
    steps: list[OriginStep] = []
    while st.n:
        e = origin_step(st)
        steps.append(e)
        st = e.after

    L = st.depth
    H = hard_tail(s, n)

    assert st.alpha == H // (3**L)
    assert st.seed == affine_carry(4, 1, H, L)

    parent_exp = (3**s) * (1 + 3 * n)
    assert st.beta == 4**parent_exp
    assert st.beta == 1 + 3 ** (s + 1) + 3 ** (s + 2) * H

    return st, steps


def terminal_probe(s: int, n: int, happy_window: int = 256) -> dict:
    st, steps = exhaust_origin(s, n)
    j = first_seeded_happy(st.seed, st.alpha, happy_window)
    return {
        "s": s,
        "n": n,
        "n_mod3": n % 3,
        "origin_depth": st.depth,
        "terminal_seed": st.seed,
        "terminal_mod6": st.alpha % 6,
        "terminal_mod35": st.alpha % 35,
        "terminal_mod455": st.alpha % 455,
        "first_terminal_happy": j,
        "origin_trits_lsf": [e.origin_trit for e in steps],
        "emitted_trits_lsf": [e.emitted_trit for e in steps],
    }


def residual_origins_of_exact_ternary_length(L: int) -> Iterable[int]:
    assert L >= 1
    lo = 1 if L == 1 else 3 ** (L - 1)
    hi = 3**L
    for n in range(lo, hi):
        if n % 3 != 0:
            yield n


def exhaustive_terminal_scan(
    s: int,
    max_ternary_digits: int = 8,
    happy_window: int = 256,
) -> list[dict]:
    rows = []
    for L in range(1, max_ternary_digits + 1):
        tested = 0
        missing = []
        max_gate = -1
        argmax = None
        for n in residual_origins_of_exact_ternary_length(L):
            tested += 1
            p = terminal_probe(s, n, happy_window)
            j = p["first_terminal_happy"]
            if j is None:
                missing.append(n)
            elif j > max_gate:
                max_gate = j
                argmax = p
        rows.append({
            "s": s,
            "ternary_digits": L,
            "tested_residual_origins": tested,
            "missing_within_window": len(missing),
            "first_missing": missing[:8],
            "max_first_terminal_happy": max_gate,
            "argmax": argmax,
        })
    return rows


def validate_graph_sample(s: int, n: int) -> None:
    T = child_navigation(s, n)
    H = hard_tail(s, n)
    assert parent_navigation(s, n) == Q(s, 1 + 3 * n)

    qmax = max(8, (T.bit_length() // 2) + 4)
    for q in range(qmax):
        validate_shared_carrier(s, n, q)

        child_d = trit(T, q)
        parent_d = trit(H, q)
        As = A(s)
        Z = affine_carry(As, z(s), T, q)
        assert parent_d == (Z + child_d) % 3

    exhaust_origin(s, n)


def main() -> None:
    print("GST Graph V2 canonical-origin experiment")
    print("========================================")

    for s in (1, 2):
        for n in (1, 2, 4, 5, 7, 8, 10, 11):
            if n % 3:
                validate_graph_sample(s, n)

    print("\nExact identities: PASS")

    for s in (1, 2):
        print(f"\nExhaustive residual terminal scan, s={s}")
        for row in exhaustive_terminal_scan(s, max_ternary_digits=8, happy_window=256):
            print(
                "  L={ternary_digits}: tested={tested_residual_origins}, "
                "missing={missing_within_window}, "
                "max-first-gate={max_first_terminal_happy}".format(**row)
            )
            if row["argmax"]:
                p = row["argmax"]
                print(
                    f"      argmax n={p['n']}, seed={p['terminal_seed']}, "
                    f"mod35={p['terminal_mod35']}, mod455={p['terminal_mod455']}"
                )

    print(
        "\nSTATUS: experimental evidence only. "
        "The candidate theorem is: every canonical finite-origin terminal "
        "state reachable from the true residual prefix-one transducer is "
        "not a complete seeded bad trace."
    )


if __name__ == "__main__":
    main()
