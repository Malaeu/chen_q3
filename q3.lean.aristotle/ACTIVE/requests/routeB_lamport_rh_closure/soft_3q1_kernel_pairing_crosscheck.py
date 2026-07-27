#!/usr/bin/env python3
"""Numerical cross-checks and P1--P5 scoring for SOFT_3Q1."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import numpy as np


HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "routeB_twolevel_spectral_ladder" / "out"
RESULT = HERE / "SOFT_3Q1_KERNEL_PAIRING_CROSSCHECK.json"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def load_coeffs(path: Path) -> tuple[int, int, np.ndarray, np.ndarray]:
    data = json.loads(path.read_text())
    rows = sorted(data["coefficients"], key=lambda r: int(r["n"]))
    ns = np.array([int(r["n"]) for r in rows], dtype=np.int64)
    c = np.array([complex(float(r["re"]), float(r["im"])) for r in rows], dtype=np.complex128)
    c /= np.linalg.norm(c)
    return int(data["lambda_sq"]), int(data["N"]), ns, c


def basis_transform(x: np.ndarray, L: float, ns: np.ndarray) -> np.ndarray:
    a = 2 * np.pi * ns / L
    # D0.6 (3.2), including the removable value sqrt(L)(-1)^n.
    return np.sqrt(L) * ((-1.0) ** ns)[None, :] * np.sinc(
        (x[:, None] - a[None, :]) * L / (2 * np.pi)
    )


def packet_crosscheck(path: Path, x_order: int = 640, u_order: int = 560) -> dict[str, Any]:
    m, N, ns, c = load_coeffs(path)
    L = math.log(m)
    B = 12.0
    gx, gw = np.polynomial.legendre.leggauss(x_order)
    x = B * gx
    wx = B * gw
    bump = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (x / B) ** 2))
    # Smooth compactly supported, complex, and sign-changing in real part.
    phi = bump * ((x / B) - 0.12 + 0.35j * ((x / B) ** 2 - 0.28))

    F_exact = basis_transform(x, L, ns) @ c
    lhs = np.sum(wx * phi * F_exact * np.conj(F_exact))

    gu, gwu = np.polynomial.legendre.leggauss(u_order)
    u = (L / 2) * gu
    wu = (L / 2) * gwu
    centered_c = ((-1.0) ** ns) * c
    q = np.exp(1j * np.outer(u, 2 * np.pi * ns / L)) @ centered_c / np.sqrt(L)
    F_quad = np.exp(-1j * np.outer(x, u)) @ (wu * q)
    rhs = np.sum(wx * phi * F_quad * np.conj(F_quad))
    wrong_sign = np.sum(wx * phi * (
        (np.exp(+1j * np.outer(x, u)) @ (wu * q))
        * np.conj(np.exp(+1j * np.outer(x, u)) @ (wu * q))
    ))
    scale = max(1.0, abs(lhs), abs(rhs))
    return {
        "lambda_sq": m,
        "N": N,
        "source": str(path.name),
        "phi": "C_c^inf([-12,12]); complex; real part sign-changing",
        "lhs_direct_pairing": {"re": lhs.real, "im": lhs.imag},
        "rhs_fubini_u_minus_v": {"re": rhs.real, "im": rhs.imag},
        "relative_error": abs(lhs - rhs) / scale,
        "wrong_sign_control": {"re": wrong_sign.real, "im": wrong_sign.imag},
        "wrong_sign_relative_difference": abs(lhs - wrong_sign) / scale,
    }


def sharp_plant() -> dict[str, float | str]:
    L = math.log(13)
    n = 1
    a = 2 * math.pi * n / L
    x = 0.73

    def B(z: float) -> float:
        return 2 / math.sqrt(L) * math.sin(z * L / 2) / (z - a)

    correct = B(x) ** 2
    wrong = B(x) * B(-x)
    even = lambda z: 1 + z * z
    even_correct = even(x) ** 2
    even_wrong = even(x) * even(-x)
    return {
        "basis": "V_1",
        "x": x,
        "correct_ZEO_conjugation_product": correct,
        "wrong_reflection_product": wrong,
        "relative_difference": abs(correct - wrong) / max(1.0, abs(correct)),
        "even_control_difference": abs(even_correct - even_wrong),
        "verdict": "SOFT_3Q1_SHARP_COORDINATE_MISMATCH_FIRES_ON_V1_XI_CONTROL_SILENT",
    }


def support_away_plant() -> dict[str, Any]:
    zeros = json.loads((OUT / "anchor_locked_zeros_first_200.json").read_text())["zeros"]
    nodes = np.array([float(z["gamma"]) for z in zeros], dtype=np.float64)
    left, right = nodes[0], nodes[1]
    center = (left + right) / 2
    radius = 0.35 * (right - left)
    xg, wg = np.polynomial.legendre.leggauss(400)
    x = center + radius * xg
    wx = radius * wg
    bump = np.exp(-1.0 / np.maximum(1e-300, 1.0 - ((x - center) / radius) ** 2))

    m, _, ns, c = load_coeffs(OUT / "portable_k_coeffs_lambda_sq_13_N_120.json")
    L = math.log(m)
    F = basis_transform(x, L, ns) @ c
    direct = float(np.sum(wx * bump * np.abs(F) ** 2).real)
    sampled = float(np.sum(
        [0.0 if not (center - radius < z < center + radius) else 1.0 for z in nodes]
    ))
    return {
        "support": [center - radius, center + radius],
        "adjacent_sample_nodes": [left, right],
        "sample_nodes_inside_support": int(sampled),
        "Psi_zero_sampling_value": 0.0,
        "direct_real_axis_pairing": direct,
        "verdict": "SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH",
    }


def kernel_sign_plant() -> dict[str, Any]:
    """Complex non-even kernel that does not mask u-v versus v-u."""
    L = 2.0
    gx, gw = np.polynomial.legendre.leggauss(500)
    x = 5.0 * gx
    wx = 5.0 * gw
    gu, gwu = np.polynomial.legendre.leggauss(500)
    u = gu
    wu = gwu
    q = 1.0 + 0.7j * np.exp(1.3j * u) + 0.2 * u
    bump = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (x / 5.0) ** 2))
    phi = bump * (0.2 + x / 5.0 + 0.3j * ((x / 5.0) ** 2 - 0.1))
    f_minus = np.exp(-1j * np.outer(x, u)) @ (wu * q)
    f_plus = np.exp(+1j * np.outer(x, u)) @ (wu * q)
    correct = np.sum(wx * phi * np.abs(f_minus) ** 2)
    wrong = np.sum(wx * phi * np.abs(f_plus) ** 2)
    return {
        "kernel": "q(u)=1+0.7i exp(1.3iu)+0.2u on [-1,1]",
        "correct_u_minus_v": {"re": correct.real, "im": correct.imag},
        "wrong_v_minus_u": {"re": wrong.real, "im": wrong.imag},
        "relative_difference": abs(correct - wrong) / max(1.0, abs(correct)),
        "verdict": "D06_U_MINUS_V_SIGN_VISIBLE",
    }


def main() -> None:
    cells = [
        packet_crosscheck(OUT / "portable_k_coeffs_lambda_sq_13_N_120.json"),
        packet_crosscheck(OUT / "off_axis_k1_coeffs_lambda_sq_53_N_120_float64.json"),
    ]
    sharp = sharp_plant()
    away = support_away_plant()
    sign = kernel_sign_plant()

    for cell in cells:
        require(cell["relative_error"] < 2e-10, "SOFT_3Q1_FUBINI_NUMERICAL_MISMATCH")
    require(sharp["relative_difference"] > 1e-3, "SOFT_3Q1_SHARP_COORDINATE_MISMATCH_PLANT_INERT")
    require(sharp["even_control_difference"] < 1e-15, "SOFT_3Q1_EVEN_CONTROL_NOT_SILENT")
    require(away["sample_nodes_inside_support"] == 0, "SOFT_3Q1_SUPPORT_AWAY_PLANT_HIT_NODE")
    require(away["direct_real_axis_pairing"] > 1e-12, "SOFT_3Q1_SUPPORT_AWAY_DIRECT_PAIRING_ZERO")
    require(sign["relative_difference"] > 1e-2, "SOFT_3Q1_D06_KERNEL_SIGN_PLANT_INERT")

    payload = {
        "schema": "soft_3q1_direct_kernel_pairing_crosscheck_v1",
        "sharp_lock": {
            "coordinate_line": "w=i*z from D0.6 Xi(z)=xi(1/2+i*z)",
            "ZEO_sharp": "F^sharp(z)=conj(F(conj z))",
            "wrong": "conj(F(-conj z))",
            "plant": sharp,
        },
        "fubini": {
            "transform": "F(x)=integral q(u) exp(-i*x*u) du",
            "test_transform": "hat_phi(y)=integral phi(x) exp(-i*x*y) dx",
            "coefficient_c_D06": 1,
            "kernel_argument": "u-v",
            "cells": cells,
        },
        "support_away_plant": away,
        "kernel_sign_plant": sign,
        "scoring": {
            "P1": "PASS_DIRECT_FUBINI",
            "P2": "FIRED_PSI_SUPPORT_AWAY_MISMATCH",
            "P3": "PASS_ZEO_SHARP_IS_CONJUGATION",
            "P4": "PASS_SIGN_CHANGING_PHI_LEGAL",
            "P5": "OPEN_RANK_ONE_KERNEL_CONVERGENCE_IS_NEXT_WALL",
        },
        "output_code": "SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_AND_SHARP_LOCKED",
        "rh_status": "NOT_RH",
        "bus_010_created": False,
    }
    RESULT.write_text(json.dumps(payload, indent=2) + "\n")
    for k, v in payload["scoring"].items():
        print(f"{k}={v}")
    print(payload["output_code"])
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
