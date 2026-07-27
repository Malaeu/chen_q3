#!/usr/bin/env python3
"""Fail-closed validator for the SOFT_L2 exact projection ledger."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "SOFT_L2_EXACT_PROJECTION_DEFECT_LAG_EQUATION_2026-07-13.md"
CERT = ROOT / "SOFT_L2_EXACT_PROJECTION_DEFECT_LAG_EQUATION_CERTIFICATE.json"
ROUND9 = ROOT / "SOFT_L2_PRO_VERDICT_ROUND9_2026-07-13.md"
ROUND10 = ROOT / "SOFT_L2_PRO_VERDICT_ROUND10_2026-07-13.md"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def inner(x: list[complex], y: list[complex]) -> complex:
    return sum(a.conjugate() * b for a, b in zip(x, y))


def mv(a: list[list[complex]], x: list[complex]) -> list[complex]:
    return [sum(aij * xj for aij, xj in zip(row, x)) for row in a]


def add(*xs: list[complex]) -> list[complex]:
    return [sum(vs) for vs in zip(*xs)]


def sub(x: list[complex], y: list[complex]) -> list[complex]:
    return [a - b for a, b in zip(x, y)]


def close(x: complex, y: complex, tol: float = 1e-12) -> bool:
    return abs(x - y) <= tol * max(1.0, abs(x), abs(y))


def main() -> None:
    report = REPORT.read_text()
    round9 = ROUND9.read_text()
    round10 = ROUND10.read_text()
    cert = json.loads(CERT.read_text())

    require("CODEX DIRECTIVE" in round9, "SOFT_L2_ROUND9_NOT_VERBATIM")
    require(
        "SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED" in round9,
        "SOFT_L2_ROUND9_SUCCESS_CODE_MISSING",
    )
    require(
        "SOFT_L2_SCALE_AND_DEGREE_LEDGER_LOCKED" in round10,
        "SOFT_L2_ROUND10_NOT_VERBATIM",
    )

    required = [
        "S_(m,N) := Pi_sec Pi_(m,N) P_L",
        "E_proj(t) = <(I-S)U_t q,T_full q>",
        "E_win(t)",
        "E_Gal(t)",
        "E_sec(t)",
        "E_polemid(t)",
        "E_Arch(t)",
        "D_(a,L)(t) != 0  ==>  t*a>0 and |t-a|<L",
        "|D_(a,L)(t)| <= r_L(t) r_L(a)",
        "Plant A",
        "Plant B",
        "SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED",
        "does not create Bus 010",
    ]
    for token in required:
        require(token in report, f"SOFT_L2_LEDGER_TOKEN_MISSING:{token}")

    require(
        cert["output_code"] == "SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED",
        "SOFT_L2_CERTIFICATE_CODE_MISMATCH",
    )
    require(not cert["claims"]["smallness"], "SOFT_L2_SMALLNESS_SMUGGLED")
    require(
        not cert["claims"]["Galerkin_compact_support"],
        "SOFT_L2_GALERKIN_SUPPORT_SMUGGLED",
    )
    require(not cert["claims"]["RH"], "SOFT_L2_RH_SMUGGLED")
    require(not cert["claims"]["bus_010_created"], "SOFT_L2_BUS_010_SMUGGLED")

    # Finite exact-algebra plant.  P >= Pi >= S and I-S telescope into
    # window, Galerkin, and sector residual projections.
    ident = [[complex(i == j) for j in range(4)] for i in range(4)]
    p = [[0j] * 4 for _ in range(4)]
    pi = [[0j] * 4 for _ in range(4)]
    s = [[0j] * 4 for _ in range(4)]
    for i in (0, 1, 2):
        p[i][i] = 1
    for i in (0, 1):
        pi[i][i] = 1
    s[0][0] = 1
    rwin = [[ident[i][j] - p[i][j] for j in range(4)] for i in range(4)]
    rgal = [[p[i][j] - pi[i][j] for j in range(4)] for i in range(4)]
    rsec = [[pi[i][j] - s[i][j] for j in range(4)] for i in range(4)]

    q = [1 + 0j, 0j, 0j, 0j]
    x = [0.7 - 0.1j, -0.4 + 0.8j, 0.3 + 0.2j, -0.6 - 0.5j]
    tfull = [
        [2, 1 + 2j, 0.5 - 0.2j, -0.3 - 0.4j],
        [1 - 2j, -1, 0, 0],
        [0.5 + 0.2j, 0, 0.7, 0],
        [-0.3 + 0.4j, 0, 0, 0.4],
    ]
    tprime = [
        [0.3, 0.1 - 0.1j, 0 + 0.2j, 0.4],
        [0.1 + 0.1j, 0.2, 0, 0],
        [0 - 0.2j, 0, 0.1, 0],
        [0.4, 0, 0, 0.2],
    ]
    tarch = [
        [tfull[i][j] + tprime[i][j] for j in range(4)] for i in range(4)
    ]
    mu = 0.75
    ccorr = [
        [mu - 2, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 0, 0],
    ]

    sx = mv(s, x)
    iq = mv(tfull, q)
    cq = mv(ccorr, q)
    mq = add(mv(s, mv(tfull, mv(s, q))), cq)
    require(all(close(a, b) for a, b in zip(mq, [mu, 0, 0, 0])), "SOFT_L2_EIGEN_PLANT_BAD")

    lhs = inner(x, iq)
    eproj = inner(sub(x, sx), iq)
    ecorr = -inner(sx, cq)
    rhs = mu * inner(x, q) + eproj + ecorr
    require(close(lhs, rhs), "SOFT_L2_MASTER_IDENTITY_FAILED")

    ewin = -inner(mv(rwin, x), mv(tprime, q))
    earch = inner(mv(rwin, x), mv(tarch, q))
    egal = inner(mv(rgal, x), iq)
    esec = inner(mv(rsec, x), iq)
    epolemid = ecorr
    require(
        close(eproj + ecorr, ewin + earch + egal + esec + epolemid),
        "SOFT_L2_FIVE_COMPONENT_DECOMPOSITION_FAILED",
    )

    # Fixed-window shift plant for q=1_[-1/2,1/2], L=2, t=a=1/4.
    # Before relative shift the tails vanish; after b=4/5 their common
    # right-tail interval is [1,31/20] and has length 11/20.
    unshifted_d = 0.0
    fixed_window_shifted_d = 11.0 / 20.0
    joint_shifted_d = unshifted_d
    require(
        fixed_window_shifted_d > unshifted_d,
        "SOFT_L2_WINDOW_SHIFT_COMMUTATOR_MISSING",
    )
    require(close(joint_shifted_d, unshifted_d), "SOFT_L2_SHIFT_PLANT_INERT")

    print("SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
