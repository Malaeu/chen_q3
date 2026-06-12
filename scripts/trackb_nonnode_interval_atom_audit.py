#!/usr/bin/env python3
"""
Track B / E5' non-node interval-atom audit.

This script is a proof-generator scaffold, not a proof certificate.  It
selects the same `clvsigncert` opnorm direction, focuses on one non-node mesh
interval, and emits the analytic atom ranges that the future outward-rounded
certificate must prove:

  E_delta^(j), F_v^(j), H_v^(j), S_v^(j).

The receiver and combined H/S ranges are still directed-rounded sampled
ranges.  The packet-profile F ranges additionally include a natural
Cox-de-Boor-style centered-B-spline interval extension over the same raw-a
interval.

All coordinates are raw-log coordinates: a = r * log(p).
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Any

import numpy as np

import trackb_edge_operator_probe as probe


Interval = tuple[float, float]
BSPLINE_INTERVAL_PAD = 1e-12


def out_down(x: float) -> float:
    return float(math.nextafter(float(x), -math.inf))


def out_up(x: float) -> float:
    return float(math.nextafter(float(x), math.inf))


def iv_make(lo: float, hi: float | None = None) -> Interval:
    if hi is None:
        hi = lo
    lo_f = float(lo)
    hi_f = float(hi)
    if lo_f <= hi_f:
        return (out_down(lo_f), out_up(hi_f))
    return (out_down(hi_f), out_up(lo_f))


def iv_add(x: Interval, y: Interval) -> Interval:
    return (out_down(x[0] + y[0]), out_up(x[1] + y[1]))


def iv_sub(x: Interval, y: Interval) -> Interval:
    return (out_down(x[0] - y[1]), out_up(x[1] - y[0]))


def iv_neg(x: Interval) -> Interval:
    return (out_down(-x[1]), out_up(-x[0]))


def iv_scale(c: float, x: Interval) -> Interval:
    c_f = float(c)
    if c_f >= 0.0:
        return (out_down(c_f * x[0]), out_up(c_f * x[1]))
    return (out_down(c_f * x[1]), out_up(c_f * x[0]))


def iv_mul(x: Interval, y: Interval) -> Interval:
    products = [x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]]
    return (out_down(min(products)), out_up(max(products)))


def iv_inv(x: Interval) -> Interval:
    if x[0] <= 0.0 <= x[1]:
        raise ValueError(f"interval crosses zero: {x}")
    vals = [1.0 / x[0], 1.0 / x[1]]
    return (out_down(min(vals)), out_up(max(vals)))


def iv_div(x: Interval, y: Interval) -> Interval:
    return iv_mul(x, iv_inv(y))


def iv_pad(x: Interval, pad: float = BSPLINE_INTERVAL_PAD) -> Interval:
    pad_f = abs(float(pad))
    return (out_down(x[0] - pad_f), out_up(x[1] + pad_f))


def iv_pow_int(x: Interval, n: int) -> Interval:
    if n < 0:
        return iv_inv(iv_pow_int(x, -n))
    if n == 0:
        return (1.0, 1.0)
    if x[0] >= 0.0:
        return (out_down(x[0] ** n), out_up(x[1] ** n))
    if x[1] <= 0.0:
        vals = [x[0] ** n, x[1] ** n]
        return (out_down(min(vals)), out_up(max(vals)))
    if n % 2 == 0:
        hi = max(abs(x[0]), abs(x[1])) ** n
        return (0.0, out_up(hi))
    return (out_down(x[0] ** n), out_up(x[1] ** n))


def iv_recip_power(x: Interval, n: int) -> Interval:
    return iv_inv(iv_pow_int(x, n))


def iv_width(x: Interval) -> float:
    return out_up(x[1] - x[0])


def iv_exp(x: Interval) -> Interval:
    return (out_down(math.exp(x[0])), out_up(math.exp(x[1])))


def critical_value_in_interval(lo: float, hi: float, base: float, period: float) -> bool:
    k_min = math.ceil((lo - base) / period)
    k_max = math.floor((hi - base) / period)
    return k_min <= k_max


def iv_sin(x: Interval) -> Interval:
    lo, hi = float(x[0]), float(x[1])
    if hi - lo >= 2.0 * math.pi:
        return (-1.0, 1.0)
    values = [math.sin(lo), math.sin(hi)]
    if critical_value_in_interval(lo, hi, 0.5 * math.pi, 2.0 * math.pi):
        values.append(1.0)
    if critical_value_in_interval(lo, hi, 1.5 * math.pi, 2.0 * math.pi):
        values.append(-1.0)
    return (out_down(min(values)), out_up(max(values)))


def iv_cos(x: Interval) -> Interval:
    lo, hi = float(x[0]), float(x[1])
    if hi - lo >= 2.0 * math.pi:
        return (-1.0, 1.0)
    values = [math.cos(lo), math.cos(hi)]
    if critical_value_in_interval(lo, hi, 0.0, 2.0 * math.pi):
        values.append(1.0)
    if critical_value_in_interval(lo, hi, math.pi, 2.0 * math.pi):
        values.append(-1.0)
    return (out_down(min(values)), out_up(max(values)))


def positive_polygamma_series_interval(m: int, x: Interval, *, tail_terms: int) -> Interval:
    if m < 1:
        raise ValueError("polygamma order must be >= 1")
    if x[0] <= 0.0:
        raise ValueError(f"positive series requires x>0, got {x}")
    p = m + 1
    y_lo = float(x[0])
    y_hi = float(x[1])
    sum_hi_arg = 0.0
    sum_lo_arg = 0.0
    for n in range(int(tail_terms)):
        sum_hi_arg += 1.0 / ((y_hi + n) ** p)
        sum_lo_arg += 1.0 / ((y_lo + n) ** p)
    n_tail = float(tail_terms)
    tail_lower = ((y_hi + n_tail) ** (1 - p)) / float(p - 1)
    tail_upper = ((y_lo + max(0.0, n_tail - 1.0)) ** (1 - p)) / float(p - 1)
    positive_sum = (
        out_down(sum_hi_arg + tail_lower),
        out_up(sum_lo_arg + tail_upper),
    )
    scale = ((-1.0) ** (m + 1)) * float(math.factorial(m))
    return iv_scale(scale, positive_sum)


def polygamma_interval(m: int, x: Interval, *, tail_terms: int = 400) -> Interval:
    """Interval enclosure for real polygamma order m>=1 away from poles.

    The interval is shifted to the positive half-line by the recurrence
    psi_m(z+1)=psi_m(z)+(-1)^m*m!/z^(m+1), then enclosed by the positive
    series with an integral tail bound.
    """
    if m < 1:
        raise ValueError("polygamma order must be >= 1")
    shift = 0
    if x[0] <= 0.75:
        shift = int(math.ceil(0.75 - x[0]))
    x_shifted = iv_add(x, iv_make(float(shift)))
    base = positive_polygamma_series_interval(m, x_shifted, tail_terms=tail_terms)
    correction = (0.0, 0.0)
    coeff = ((-1.0) ** m) * float(math.factorial(m))
    for k in range(shift):
        denom = iv_add(x, iv_make(float(k)))
        correction = iv_add(correction, iv_scale(coeff, iv_recip_power(denom, m + 1)))
    return iv_sub(base, correction)


def directed_range(values: np.ndarray) -> dict[str, Any]:
    arr = np.asarray(values, dtype=float)
    finite = arr[np.isfinite(arr)]
    if finite.size == 0:
        return {"lo": None, "hi": None, "max_abs": None}
    lo = out_down(float(np.min(finite)))
    hi = out_up(float(np.max(finite)))
    max_abs = out_up(max(abs(lo), abs(hi)))
    return {
        "lo": lo,
        "hi": hi,
        "max_abs": max_abs,
    }


def abs_lower_from_endpoint_values(left: float, right: float) -> float:
    lower = min(abs(float(left)), abs(float(right)))
    return max(0.0, out_down(lower))


def abs_upper_from_endpoint_values(left: float, right: float) -> float:
    upper = max(abs(float(left)), abs(float(right)))
    return out_up(upper)


def centered_bspline_interval(deg: int, x: Interval) -> Interval:
    """Natural interval extension of the centered cardinal B-spline recursion.

    This avoids the large cancellation of the alternating positive-part power
    formula used for point evaluation in the Step13 pilot.
    """
    if deg < 0:
        raise ValueError("degree must be nonnegative")
    support_radius = 0.5 * (deg + 1)
    if x[1] < -support_radius or x[0] > support_radius:
        return (0.0, 0.0)
    if deg == 0:
        if x[1] < -0.5 or x[0] > 0.5:
            return (0.0, 0.0)
        if -0.5 <= x[0] and x[1] <= 0.5:
            return iv_pad((1.0, 1.0))
        return iv_pad((0.0, 1.0))

    half_width = 0.5 * (deg + 1)
    left_coeff = iv_scale(1.0 / float(deg), iv_add(x, iv_make(half_width)))
    right_coeff = iv_scale(1.0 / float(deg), iv_sub(iv_make(half_width), x))
    left = centered_bspline_interval(deg - 1, iv_add(x, iv_make(0.5)))
    right = centered_bspline_interval(deg - 1, iv_sub(x, iv_make(0.5)))
    return iv_pad(iv_add(iv_mul(left_coeff, left), iv_mul(right_coeff, right)))


def centered_bspline_derivative_interval(deg: int, x: Interval) -> Interval:
    if deg <= 0:
        return (0.0, 0.0)
    return iv_sub(
        centered_bspline_interval(deg - 1, iv_add(x, iv_make(0.5))),
        centered_bspline_interval(deg - 1, iv_sub(x, iv_make(0.5))),
    )


def centered_bspline_second_derivative_interval(deg: int, x: Interval) -> Interval:
    if deg <= 1:
        return (0.0, 0.0)
    return iv_add(
        iv_sub(
            centered_bspline_interval(deg - 2, iv_add(x, iv_make(1.0))),
            iv_scale(2.0, centered_bspline_interval(deg - 2, x)),
        ),
        centered_bspline_interval(deg - 2, iv_sub(x, iv_make(1.0))),
    )


def centered_bspline_third_derivative_interval(deg: int, x: Interval) -> Interval:
    if deg <= 2:
        return (0.0, 0.0)
    return iv_add(
        iv_add(
            centered_bspline_interval(deg - 3, iv_add(x, iv_make(1.5))),
            iv_scale(-3.0, centered_bspline_interval(deg - 3, iv_add(x, iv_make(0.5)))),
        ),
        iv_add(
            iv_scale(3.0, centered_bspline_interval(deg - 3, iv_sub(x, iv_make(0.5)))),
            iv_scale(-1.0, centered_bspline_interval(deg - 3, iv_sub(x, iv_make(1.5)))),
        ),
    )


def r_corr_derivative_interval(packet: Any, order: int, x: Interval) -> Interval:
    deg = 2 * int(packet.k_spline) + 1
    y = iv_scale(float(packet.s_k), x)
    if order == 0:
        base = centered_bspline_interval(deg, y)
    elif order == 1:
        base = centered_bspline_derivative_interval(deg, y)
    elif order == 2:
        base = centered_bspline_second_derivative_interval(deg, y)
    elif order == 3:
        base = centered_bspline_third_derivative_interval(deg, y)
    else:
        raise ValueError("only derivative orders 0..3 are supported")
    return iv_scale((float(packet.s_k) ** order) / float(packet.c_k), base)


def shifted_packet_matrix_entry_interval(
    packet: Any,
    *,
    D_value: float,
    ell: float,
    a_interval: Interval,
    order: int,
) -> Interval:
    ell_f = float(ell)
    x_minus = iv_scale(1.0 / ell_f, iv_sub(iv_make(float(D_value)), a_interval))
    x_plus = iv_scale(1.0 / ell_f, iv_add(iv_make(float(D_value)), a_interval))
    if order == 0:
        return iv_add(
            r_corr_derivative_interval(packet, 0, x_minus),
            r_corr_derivative_interval(packet, 0, x_plus),
        )
    if order == 1:
        return iv_scale(
            1.0 / ell_f,
            iv_add(
                iv_neg(r_corr_derivative_interval(packet, 1, x_minus)),
                r_corr_derivative_interval(packet, 1, x_plus),
            ),
        )
    if order == 2:
        return iv_scale(
            1.0 / (ell_f**2),
            iv_add(
                r_corr_derivative_interval(packet, 2, x_minus),
                r_corr_derivative_interval(packet, 2, x_plus),
            ),
        )
    if order == 3:
        return iv_scale(
            1.0 / (ell_f**3),
            iv_add(
                iv_neg(r_corr_derivative_interval(packet, 3, x_minus)),
                r_corr_derivative_interval(packet, 3, x_plus),
            ),
        )
    raise ValueError("only derivative orders 0..3 are supported")


def packet_profile_interval_range(
    *,
    packet: Any,
    D: np.ndarray,
    ell: float,
    coeffs: np.ndarray,
    a_interval: Interval,
    order: int,
) -> dict[str, Any]:
    total = (0.0, 0.0)
    nonzero_entries = 0
    max_entry_width = 0.0
    for i in range(D.shape[0]):
        ci = float(coeffs[i])
        if ci == 0.0:
            continue
        for j in range(D.shape[1]):
            cj = float(coeffs[j])
            coeff = ci * cj
            if coeff == 0.0:
                continue
            entry = shifted_packet_matrix_entry_interval(
                packet,
                D_value=float(D[i, j]),
                ell=float(ell),
                a_interval=a_interval,
                order=order,
            )
            if entry == (0.0, 0.0):
                continue
            nonzero_entries += 1
            max_entry_width = max(max_entry_width, iv_width(entry))
            total = iv_add(total, iv_scale(coeff, entry))
    return {
        "lo": total[0],
        "hi": total[1],
        "max_abs": out_up(max(abs(total[0]), abs(total[1]))),
        "width": iv_width(total),
        "nonzero_matrix_entries": int(nonzero_entries),
        "max_entry_width": out_up(max_entry_width),
    }


def range_contains(container: dict[str, Any], sample: dict[str, Any]) -> bool:
    if container["lo"] is None or container["hi"] is None:
        return False
    if sample["lo"] is None or sample["hi"] is None:
        return False
    return float(container["lo"]) <= float(sample["lo"]) and float(sample["hi"]) <= float(container["hi"])


def width_ratio(container: dict[str, Any], sample: dict[str, Any]) -> float | None:
    if container["lo"] is None or container["hi"] is None:
        return None
    if sample["lo"] is None or sample["hi"] is None:
        return None
    sample_width = float(sample["hi"]) - float(sample["lo"])
    if sample_width <= 0.0:
        return None
    return out_up((float(container["hi"]) - float(container["lo"])) / sample_width)


def interval_to_dict(x: Interval) -> dict[str, Any]:
    return {
        "lo": x[0],
        "hi": x[1],
        "max_abs": out_up(max(abs(x[0]), abs(x[1]))),
        "width": iv_width(x),
    }


def dict_to_interval(row: dict[str, Any]) -> Interval:
    return (float(row["lo"]), float(row["hi"]))


def interval_abs_lower(x: Interval) -> float:
    if x[0] <= 0.0 <= x[1]:
        return 0.0
    return out_down(min(abs(x[0]), abs(x[1])))


def vaaler_K0_derivatives_interval(z: Interval) -> tuple[Interval, Interval, Interval, Interval]:
    pi = iv_make(math.pi)
    pi2 = iv_make(math.pi * math.pi)
    sinp = iv_sin(iv_scale(math.pi, z))
    cosp = iv_cos(iv_scale(math.pi, z))
    sin2 = iv_sin(iv_scale(2.0 * math.pi, z))
    cos2 = iv_cos(iv_scale(2.0 * math.pi, z))
    z2 = iv_pow_int(z, 2)
    z3 = iv_pow_int(z, 3)
    z4 = iv_pow_int(z, 4)
    z5 = iv_pow_int(z, 5)

    k0 = iv_div(iv_pow_int(sinp, 2), iv_mul(pi2, z2))
    k1_num = iv_scale(
        2.0,
        iv_mul(sinp, iv_sub(iv_mul(iv_mul(pi, z), cosp), sinp)),
    )
    k1 = iv_div(k1_num, iv_mul(pi2, z3))
    k2_num_inner = iv_add(
        iv_sub(
            iv_mul(iv_mul(pi2, z2), cos2),
            iv_scale(2.0, iv_mul(iv_mul(pi, z), sin2)),
        ),
        iv_scale(3.0, iv_pow_int(sinp, 2)),
    )
    k2 = iv_div(iv_scale(2.0, k2_num_inner), iv_mul(pi2, z4))
    k3 = iv_add(
        iv_add(
            iv_scale(-4.0 * math.pi, iv_div(sin2, z2)),
            iv_scale(-12.0, iv_div(cos2, z3)),
        ),
        iv_add(
            iv_scale(18.0 / math.pi, iv_div(sin2, z4)),
            iv_scale(
                -12.0 / (math.pi * math.pi),
                iv_div(iv_sub((1.0, 1.0), cos2), z5),
            ),
        ),
    )
    return k0, k1, k2, k3


def vaaler_H0_derivatives_interval(
    z: Interval,
    *,
    tail_terms: int,
) -> tuple[Interval, Interval, Interval, Interval]:
    pi = iv_make(math.pi)
    sinp = iv_sin(iv_scale(math.pi, z))
    A = iv_div(iv_pow_int(sinp, 2), iv_pow_int(pi, 2))
    A1 = iv_div(iv_sin(iv_scale(2.0 * math.pi, z)), pi)
    A2 = iv_scale(2.0, iv_cos(iv_scale(2.0 * math.pi, z)))
    A3 = iv_scale(-4.0 * math.pi, iv_sin(iv_scale(2.0 * math.pi, z)))
    one_minus_z = iv_sub((1.0, 1.0), z)
    one_plus_z = iv_add((1.0, 1.0), z)
    psi1_minus = polygamma_interval(1, one_minus_z, tail_terms=tail_terms)
    psi1_plus = polygamma_interval(1, one_plus_z, tail_terms=tail_terms)
    psi2_minus = polygamma_interval(2, one_minus_z, tail_terms=tail_terms)
    psi2_plus = polygamma_interval(2, one_plus_z, tail_terms=tail_terms)
    psi3_minus = polygamma_interval(3, one_minus_z, tail_terms=tail_terms)
    psi3_plus = polygamma_interval(3, one_plus_z, tail_terms=tail_terms)
    psi4_minus = polygamma_interval(4, one_minus_z, tail_terms=tail_terms)
    psi4_plus = polygamma_interval(4, one_plus_z, tail_terms=tail_terms)

    B = iv_add(iv_sub(psi1_minus, psi1_plus), iv_scale(2.0, iv_inv(z)))
    B1 = iv_add(
        iv_add(iv_neg(psi2_minus), iv_neg(psi2_plus)),
        iv_scale(-2.0, iv_recip_power(z, 2)),
    )
    B2 = iv_add(
        iv_sub(psi3_minus, psi3_plus),
        iv_scale(4.0, iv_recip_power(z, 3)),
    )
    B3 = iv_add(
        iv_add(iv_neg(psi4_minus), iv_neg(psi4_plus)),
        iv_scale(-12.0, iv_recip_power(z, 4)),
    )
    h0 = iv_mul(A, B)
    h1 = iv_add(iv_mul(A1, B), iv_mul(A, B1))
    h2 = iv_add(
        iv_add(iv_mul(A2, B), iv_scale(2.0, iv_mul(A1, B1))),
        iv_mul(A, B2),
    )
    h3 = iv_add(
        iv_add(iv_mul(A3, B), iv_scale(3.0, iv_mul(A2, B1))),
        iv_add(iv_scale(3.0, iv_mul(A1, B2)), iv_mul(A, B3)),
    )
    return h0, h1, h2, h3


def selberg_receiver_interval_ranges(
    *,
    a_interval: Interval,
    lo: float,
    hi: float,
    receiver_delta: float,
    tail_terms: int,
) -> dict[str, Any]:
    delta = float(receiver_delta)
    if delta <= 0.0:
        raise ValueError("receiver_delta must be positive")
    if a_interval[0] < lo < a_interval[1] or a_interval[0] < hi < a_interval[1]:
        raise ValueError("receiver interval crosses an edge jump")
    if lo <= a_interval[0] and a_interval[1] <= hi:
        chi = 1.0
    elif a_interval[1] < lo or hi < a_interval[0]:
        chi = 0.0
    else:
        raise ValueError("receiver interval has ambiguous indicator state")

    za = iv_scale(delta, iv_sub(a_interval, iv_make(float(lo))))
    zb = iv_scale(delta, iv_sub(a_interval, iv_make(float(hi))))
    Ha = vaaler_H0_derivatives_interval(za, tail_terms=tail_terms)
    Hb = vaaler_H0_derivatives_interval(zb, tail_terms=tail_terms)
    Ka = vaaler_K0_derivatives_interval(za)
    Kb = vaaler_K0_derivatives_interval(zb)
    values: list[Interval] = []
    for order in range(4):
        raw = iv_add(
            iv_add(iv_scale(0.5, Ha[order]), iv_scale(-0.5, Hb[order])),
            iv_add(iv_scale(0.5, Ka[order]), iv_scale(0.5, Kb[order])),
        )
        raw = iv_scale(delta**order, raw)
        if order == 0:
            raw = iv_sub(raw, (chi, chi))
        values.append(raw)
    return {
        f"E{order}": {
            **interval_to_dict(values[order]),
            "left_z": interval_to_dict(za),
            "right_z": interval_to_dict(zb),
        }
        for order in range(4)
    }


def combined_hs_interval_ranges(
    *,
    a_interval: Interval,
    receiver_intervals: dict[str, Any],
    profile_intervals: dict[str, Any],
) -> dict[str, Any]:
    E = {idx: dict_to_interval(receiver_intervals[f"E{idx}"]) for idx in range(4)}
    F = {idx: dict_to_interval(profile_intervals[f"F{idx}"]) for idx in range(4)}
    H0 = iv_mul(E[0], F[0])
    H1 = iv_add(iv_mul(E[1], F[0]), iv_mul(E[0], F[1]))
    H2 = iv_add(
        iv_add(iv_mul(E[2], F[0]), iv_scale(2.0, iv_mul(E[1], F[1]))),
        iv_mul(E[0], F[2]),
    )
    H3 = iv_add(
        iv_add(iv_mul(E[3], F[0]), iv_scale(3.0, iv_mul(E[2], F[1]))),
        iv_add(iv_scale(3.0, iv_mul(E[1], F[2])), iv_mul(E[0], F[3])),
    )
    exp_half = iv_exp(iv_scale(-0.5, a_interval))
    S0 = iv_mul(exp_half, iv_sub(H1, iv_scale(0.5, H0)))
    S1 = iv_mul(exp_half, iv_add(iv_sub(H2, H1), iv_scale(0.25, H0)))
    S2 = iv_mul(
        exp_half,
        iv_add(
            iv_sub(H3, iv_scale(1.5, H2)),
            iv_sub(iv_scale(0.75, H1), iv_scale(0.125, H0)),
        ),
    )
    return {
        "H0": interval_to_dict(H0),
        "H1": interval_to_dict(H1),
        "H2": interval_to_dict(H2),
        "H3": interval_to_dict(H3),
        "S0": interval_to_dict(S0),
        "S1": interval_to_dict(S1),
        "S2": interval_to_dict(S2),
    }


def selected_opnorm_context(
    *,
    K: float,
    ell: float,
    grid_delta: float,
    k_spline: int,
    p0_na: int,
    receiver_delta: float,
) -> dict[str, Any]:
    pilot = probe.load_step13()
    lo, hi = 2.0 * float(K), 4.0 * float(K)
    ctx = probe.build_packet_context(
        pilot,
        K=float(K),
        ell=float(ell),
        grid_delta=float(grid_delta),
        k_spline=int(k_spline),
        p0_na=int(p0_na),
    )
    params = ctx["params"]
    packet = ctx["packet"]
    D = ctx["D"]
    N = ctx["N"]
    Gc = ctx["Gc"]
    effective_max_a = probe.effective_shift_cutoff(D, params.ell)
    shift_params = pilot.PilotParams(
        L=0.5 * effective_max_a,
        ell=params.ell,
        delta=params.delta,
        k_spline=params.k_spline,
        p0_na=int(p0_na),
    )
    shifts = pilot.prime_power_shifts(shift_params.L)

    def chi_weight(a: float) -> float:
        return 1.0 if lo <= a <= hi else 0.0

    def plus_weight(a: float) -> float:
        return float(
            probe.selberg_interval_values(
                np.array([a]),
                lo=lo,
                hi=hi,
                receiver_delta=float(receiver_delta),
                sign="plus",
            )[0]
        )

    P_edge = probe.build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, chi_weight)
    P_plus = probe.build_prime_matrix_for_weight(pilot, packet, D, params.ell, shifts, plus_weight)
    P0_edge = probe.build_P0_edge(pilot, packet, D, params.ell, lo, hi, int(p0_na))
    P0_plus = probe.build_continuum_matrix_for_weight(
        pilot,
        packet,
        D,
        params.ell,
        max_a=effective_max_a,
        p0_na=int(p0_na),
        weight_fn=plus_weight,
    )
    correction = pilot.sym((P_plus - P_edge) - (P0_plus - P0_edge))
    A_corr = probe.generalized_to_standard(pilot, probe.project_matrix(pilot, correction, N), Gc)
    eigs, evecs = np.linalg.eigh(A_corr)
    op_idx = int(np.argmax(np.abs(eigs)))
    coeffs = probe.standardized_eigenvector_to_full_coeffs(Gc, N, evecs[:, op_idx])
    return {
        "pilot": pilot,
        "params": params,
        "packet": packet,
        "D": D,
        "coeffs": coeffs,
        "lo": lo,
        "hi": hi,
        "effective_max_a": effective_max_a,
        "opnorm_eigenvalue": float(eigs[op_idx]),
        "correction_eig_min": float(eigs[0]),
        "correction_eig_max": float(eigs[-1]),
    }


def atom_samples(
    *,
    ctx: dict[str, Any],
    receiver_delta: float,
    a_grid: np.ndarray,
) -> dict[str, np.ndarray]:
    lo = float(ctx["lo"])
    hi = float(ctx["hi"])
    pilot = ctx["pilot"]
    packet = ctx["packet"]
    D = ctx["D"]
    ell = float(ctx["params"].ell)
    coeffs = ctx["coeffs"]

    mplus, e1, e2, e3 = probe.selberg_interval_plus_derivatives3(
        a_grid,
        lo=lo,
        hi=hi,
        receiver_delta=float(receiver_delta),
    )
    chi = np.where((lo <= a_grid) & (a_grid <= hi), 1.0, 0.0)
    e0 = mplus - chi
    f0 = probe.packet_profile_grid(pilot, packet, D, ell, coeffs, a_grid)
    f1 = probe.packet_profile_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    f2 = probe.packet_profile_second_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    f3 = probe.packet_profile_third_derivative_grid(pilot, packet, D, ell, coeffs, a_grid)
    h0 = e0 * f0
    h1 = e1 * f0 + e0 * f1
    h2 = e2 * f0 + 2.0 * e1 * f1 + e0 * f2
    h3 = e3 * f0 + 3.0 * e2 * f1 + 3.0 * e1 * f2 + e0 * f3
    exp_half = np.exp(-0.5 * a_grid)
    s0 = exp_half * (h1 - 0.5 * h0)
    s1 = exp_half * (h2 - h1 + 0.25 * h0)
    s2 = exp_half * (h3 - 1.5 * h2 + 0.75 * h1 - 0.125 * h0)
    return {
        "E0": e0,
        "E1": e1,
        "E2": e2,
        "E3": e3,
        "F0": f0,
        "F1": f1,
        "F2": f2,
        "F3": f3,
        "H0": h0,
        "H1": h1,
        "H2": h2,
        "H3": h3,
        "S0": s0,
        "S1": s1,
        "S2": s2,
    }


def run(args: argparse.Namespace) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for K in args.K:
        ell = probe.stable_receiver_ell(K, args.ell) if args.schedule == "stable" else args.ell
        for receiver_delta in args.receiver_delta:
            ctx = selected_opnorm_context(
                K=float(K),
                ell=float(ell),
                grid_delta=float(args.grid_delta),
                k_spline=int(args.k_spline),
                p0_na=int(args.p0_na),
                receiver_delta=float(receiver_delta),
            )
            cell_edges = np.linspace(
                0.0,
                float(ctx["effective_max_a"]),
                int(args.ledger_cells) + 1,
            )
            cell_idx = int(args.cell)
            if cell_idx < 0 or cell_idx >= int(args.ledger_cells):
                raise ValueError("cell must be inside ledger cell range")
            cell_lo = float(cell_edges[cell_idx])
            cell_hi = float(cell_edges[cell_idx + 1])
            mesh = np.linspace(cell_lo, cell_hi, int(args.cert_na))
            if args.mesh_index == "auto":
                # The current theorem-producing pilot is the worst leftmost
                # interval for K=3.5 cell 58.  For other cells, keep the same
                # deterministic first-interval default until a proof-grade
                # interval selector exists.
                mesh_idx = 0
            else:
                mesh_idx = int(args.mesh_index)
            if mesh_idx < 0 or mesh_idx >= len(mesh) - 1:
                raise ValueError("mesh-index must select an interval inside the cell mesh")
            a_lo = float(mesh[mesh_idx])
            a_hi = float(mesh[mesh_idx + 1])
            a_grid = np.linspace(a_lo, a_hi, int(args.atom_samples))
            samples = atom_samples(
                ctx=ctx,
                receiver_delta=float(receiver_delta),
                a_grid=a_grid,
            )
            ranges = {name: directed_range(values) for name, values in samples.items()}
            a_interval = iv_make(a_lo, a_hi)
            profile_intervals = {
                f"F{order}": packet_profile_interval_range(
                    packet=ctx["packet"],
                    D=ctx["D"],
                    ell=float(ctx["params"].ell),
                    coeffs=ctx["coeffs"],
                    a_interval=a_interval,
                    order=order,
                )
                for order in range(4)
            }
            profile_interval_comparison = {
                name: {
                    "contains_directed_sample_range": range_contains(interval, ranges[name]),
                    "interval_width_over_sample_width": width_ratio(interval, ranges[name]),
                    "interval_width": interval["width"],
                    "sample_width": None
                    if ranges[name]["lo"] is None or ranges[name]["hi"] is None
                    else out_up(float(ranges[name]["hi"]) - float(ranges[name]["lo"])),
                    "nonzero_matrix_entries": interval["nonzero_matrix_entries"],
                    "max_entry_width": interval["max_entry_width"],
                }
                for name, interval in profile_intervals.items()
            }
            receiver_intervals = selberg_receiver_interval_ranges(
                a_interval=a_interval,
                lo=float(ctx["lo"]),
                hi=float(ctx["hi"]),
                receiver_delta=float(receiver_delta),
                tail_terms=int(args.polygamma_tail_terms),
            )
            receiver_interval_comparison = {
                name: {
                    "contains_directed_sample_range": range_contains(interval, ranges[name]),
                    "interval_width_over_sample_width": width_ratio(interval, ranges[name]),
                    "interval_width": interval["width"],
                    "sample_width": None
                    if ranges[name]["lo"] is None or ranges[name]["hi"] is None
                    else out_up(float(ranges[name]["hi"]) - float(ranges[name]["lo"])),
                }
                for name, interval in receiver_intervals.items()
            }
            combined_intervals = combined_hs_interval_ranges(
                a_interval=a_interval,
                receiver_intervals=receiver_intervals,
                profile_intervals=profile_intervals,
            )
            combined_interval_comparison = {
                name: {
                    "contains_directed_sample_range": range_contains(interval, ranges[name]),
                    "interval_width_over_sample_width": width_ratio(interval, ranges[name]),
                    "interval_width": interval["width"],
                    "sample_width": None
                    if ranges[name]["lo"] is None or ranges[name]["hi"] is None
                    else out_up(float(ranges[name]["hi"]) - float(ranges[name]["lo"])),
                }
                for name, interval in combined_intervals.items()
                if name in ranges
            }
            width = out_up(a_hi - a_lo)
            endpoint_abs_S_lower = abs_lower_from_endpoint_values(
                float(samples["S0"][0]),
                float(samples["S0"][-1]),
            )
            endpoint_abs_S1_upper = abs_upper_from_endpoint_values(
                float(samples["S1"][0]),
                float(samples["S1"][-1]),
            )
            sample_S2_abs_upper = ranges["S2"]["max_abs"]
            guards: list[dict[str, Any]] = []
            for factor in args.curvature_factors:
                derivative_envelope = out_up(
                    endpoint_abs_S1_upper
                    + 0.5 * float(factor) * float(sample_S2_abs_upper) * width
                )
                guard = out_down(endpoint_abs_S_lower - 0.5 * derivative_envelope * width)
                guards.append(
                    {
                        "curvature_factor": float(factor),
                        "endpoint_abs_S_lower": endpoint_abs_S_lower,
                        "endpoint_abs_S1_upper": endpoint_abs_S1_upper,
                        "sample_sup_abs_S2_upper": sample_S2_abs_upper,
                        "derivative_envelope_upper": derivative_envelope,
                        "mesh_guard_lower": guard,
                        "passes": bool(guard > 0.0),
                    }
                )
            interval_s0 = dict_to_interval(combined_intervals["S0"])
            interval_s1 = dict_to_interval(combined_intervals["S1"])
            interval_s2 = dict_to_interval(combined_intervals["S2"])
            direct_s0_abs_lower = interval_abs_lower(interval_s0)
            direct_s1_abs_upper = combined_intervals["S1"]["max_abs"]
            direct_s2_abs_upper = combined_intervals["S2"]["max_abs"]
            direct_mesh_guard = out_down(direct_s0_abs_lower - 0.5 * direct_s1_abs_upper * width)
            curvature_mesh_guard = out_down(
                direct_s0_abs_lower
                - 0.5
                * out_up(direct_s1_abs_upper + 0.5 * direct_s2_abs_upper * width)
                * width
            )
            combined_interval_sign_guard = {
                "S0_excludes_zero": bool(not (interval_s0[0] <= 0.0 <= interval_s0[1])),
                "S0_abs_lower": direct_s0_abs_lower,
                "S1_abs_upper": direct_s1_abs_upper,
                "S2_abs_upper": direct_s2_abs_upper,
                "mesh_width_upper": width,
                "direct_S1_mesh_guard_lower": direct_mesh_guard,
                "curvature_S2_mesh_guard_lower": curvature_mesh_guard,
                "direct_S1_guard_passes": bool(direct_mesh_guard > 0.0),
                "curvature_S2_guard_passes": bool(curvature_mesh_guard > 0.0),
            }
            node_audit = probe.selberg_receiver_node_audit(
                a_grid,
                lo=float(ctx["lo"]),
                hi=float(ctx["hi"]),
                receiver_delta=float(receiver_delta),
            )
            rows.append(
                {
                    "mode": "trackb_nonnode_interval_atom_audit",
                    "status": "diagnostic_only",
                    "interval_kind": "directed_rounded_sample_ranges_not_proof_grade",
                    "K": float(K),
                    "ell": float(ell),
                    "grid_delta": float(args.grid_delta),
                    "k_spline": int(args.k_spline),
                    "p0_na": int(args.p0_na),
                    "ledger_cells": int(args.ledger_cells),
                    "cert_na": int(args.cert_na),
                    "cell": cell_idx,
                    "mesh_index": mesh_idx,
                    "atom_samples": int(args.atom_samples),
                    "receiver_delta": float(receiver_delta),
                    "raw_edge": [float(ctx["lo"]), float(ctx["hi"])],
                    "cell_interval": [cell_lo, cell_hi],
                    "mesh_interval": [a_lo, a_hi],
                    "mesh_width_directed_upper": width,
                    "opnorm_eigenvalue": float(ctx["opnorm_eigenvalue"]),
                    "correction_eig_min": float(ctx["correction_eig_min"]),
                    "correction_eig_max": float(ctx["correction_eig_max"]),
                    "atom_ranges": ranges,
                    "profile_interval_kind": (
                        "natural_centered_b_spline_interval_with_float_coefficients"
                    ),
                    "profile_interval_method": "centered_cardinal_b_spline_cox_de_boor_recursion",
                    "profile_interval_rounding_pad": BSPLINE_INTERVAL_PAD,
                    "profile_interval_ranges": profile_intervals,
                    "profile_interval_comparison": profile_interval_comparison,
                    "receiver_interval_kind": (
                        "vaaler_polygamma_recurrence_positive_series_tail_interval"
                    ),
                    "receiver_interval_polygamma_tail_terms": int(args.polygamma_tail_terms),
                    "receiver_interval_ranges": receiver_intervals,
                    "receiver_interval_comparison": receiver_interval_comparison,
                    "combined_interval_kind": "product_rule_interval_from_receiver_and_profile_atoms",
                    "combined_interval_ranges": combined_intervals,
                    "combined_interval_comparison": combined_interval_comparison,
                    "combined_interval_sign_guard": combined_interval_sign_guard,
                    "mesh_guards": guards,
                    "receiver_node_audit": node_audit,
                    "proof_status": (
                        "diagnostic_only: F_v profile atoms and E_delta receiver "
                        "atoms now have natural interval extensions over the "
                        "selected raw-a interval, and H/S ranges are combined "
                        "by interval product rules; "
                        "profile coefficients and centers are current floating "
                        "pilot data and receiver constants are floating interval "
                        "scaffold data, not rational Lean certificate data"
                    ),
                    "next_certificate_contract": (
                        "rationalize the current floating packet-profile "
                        "coefficients/centers plus receiver constants, then lift "
                        "the local interval sign guard to the full cell worklist"
                    ),
                    "D2": (
                        "raw a=r*log(p), edge=[2K,4K], Q3 xi=a/(2*pi), "
                        "w_Q(n)=2*Lambda(n)/sqrt(n)"
                    ),
                }
            )
    return rows


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--K", type=float, nargs="+", required=True)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--grid-delta", type=float, default=0.5)
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--receiver-delta", type=float, nargs="+", required=True)
    parser.add_argument(
        "--schedule",
        choices=["stable", "fixed"],
        default="stable",
        help="use previous stability-filtered ell choices or a fixed --ell",
    )
    parser.add_argument("--p0-na", type=int, default=1001)
    parser.add_argument("--ledger-cells", type=int, default=120)
    parser.add_argument("--cert-na", type=int, default=801)
    parser.add_argument("--cell", type=int, required=True)
    parser.add_argument(
        "--mesh-index",
        default="auto",
        help="mesh interval index inside the selected cell, or auto",
    )
    parser.add_argument("--atom-samples", type=int, default=65)
    parser.add_argument(
        "--polygamma-tail-terms",
        type=int,
        default=400,
        help="positive-series terms before the integral tail in receiver interval bounds",
    )
    parser.add_argument(
        "--curvature-factors",
        type=float,
        nargs="+",
        default=[1.0, 1000.0, 10000.0],
        help="diagnostic inflation factors for sampled S'' ranges",
    )
    return parser.parse_args()


def main() -> None:
    rows = run(parse_args())
    print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
