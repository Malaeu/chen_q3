#!/usr/bin/env python3
"""Diagnostic independent physical-kernel quadrature; writes gate.json only."""
import hashlib
import json
import platform
import resource
import time
from pathlib import Path

import mpmath as mp
import numpy as np
import scipy
from scipy.special import roots_legendre

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
M = 80
ORDERS = (12, 20, 32)
GAMMAS = (14, 50, 200, 800)
AS = ("0", "0.05", "0.1", "1/3")
TOL = 1e-12
mp.mp.dps = 80
LD = np.longdouble
L = np.log(LD(M))
PI = np.arccos(LD(-1))
J = np.arange(M + 1)
D = np.where(J == 0, LD(1), np.sqrt(LD(2)))
OMEGA = 2 * PI * J / L


def exact_a(s):
    return mp.mpf(1) / 3 if s == "1/3" else mp.mpf(s)


def analytic_reference(a_string, gamma):
    """80-digit stable sinc formula, algebraically identical to source quotient."""
    ll = mp.log(M)
    z = mp.mpc(gamma, exact_a(a_string))
    c = []
    for j in range(M + 1):
        w = 2 * mp.pi * j / ll
        d = mp.mpf(1) if j == 0 else mp.sqrt(2)
        # int cos(zx)cos(wx) dx = L/2 [sinc((z-w)L/2)+sinc((z+w)L/2)].
        # Source basis has (-1)^j; mp.sinc(t)=sin(t)/t, sinc(0)=1.
        c.append(d * (-1)**j * mp.sqrt(ll) / 2 *
                 (mp.sinc((z-w)*ll/2) + mp.sinc((z+w)*ll/2)))
    qmp = [[4 * mp.re(c[j] * c[k]) for k in range(M + 1)]
           for j in range(M + 1)]
    q = np.array([[LD(str(v)) for v in row] for row in qmp], dtype=LD)
    cc = np.array([complex(v) for v in c])
    # Independent quotient evaluation, away from removable resonances.
    cq = [(2 * (1 if j == 0 else mp.sqrt(2)) * z * mp.sin(z*ll/2)
           / (mp.sqrt(ll)*(z*z-(2*mp.pi*j/ll)**2))) for j in range(M+1)]
    err = max(abs(c[j]-cq[j]) for j in range(M+1))
    return c, q, cc, str(err)


def physical_integrals(a_string, gamma, order):
    """Composite GL of phi_j(x)cos(zx) on FULL physical interval.

    No sine quotient, sinc, or analytic coefficient routine is used here.
    Real/imaginary parts are integrated separately with long-double sums.
    """
    a = LD(1)/LD(3) if a_string == "1/3" else LD(a_string)
    panels = int(np.ceil(L * (LD(gamma) + OMEGA[-1]) / LD(12)))
    nodes, weights = roots_legendre(order)
    h = L / LD(panels)
    centers = -L/2 + (np.arange(panels, dtype=LD) + LD("0.5"))*h
    x = (centers[:, None] + h/2*nodes.astype(LD)).reshape(-1)
    w = np.tile(weights.astype(LD)*h/2, panels)
    cr = np.cos(LD(gamma)*x)*np.cosh(a*x)
    ci = -np.sin(LD(gamma)*x)*np.sinh(a*x)
    basis = D[:, None] * ((-1)**J)[:, None] / np.sqrt(L) * np.cos(OMEGA[:, None]*x)
    r = np.sum(basis*(w*cr), axis=1, dtype=LD)
    im = np.sum(basis*(w*ci), axis=1, dtype=LD)
    # Fubini/separability of the PHYSICAL double integral, no conjugation.
    q = 4 * (np.outer(r, r) - np.outer(im, im))
    return r, im, q, panels, len(x)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    wall0 = time.perf_counter()
    cpu0 = time.process_time()
    cells = []
    for astr in AS:
        for gamma in GAMMAS:
            c, qref, cc, formula_error = analytic_reference(astr, gamma)
            prev = None
            runs = []
            for order in ORDERS:
                r, im, q, panels, nodes = physical_integrals(astr, gamma, order)
                err = np.abs(q-qref)
                ij = np.unravel_index(np.argmax(err), err.shape)
                coefferr = max(abs(mp.mpc(str(r[j]), str(im[j]))-c[j]) for j in J)
                runs.append({"order": order, "panels": panels, "nodes": nodes,
                             "max_abs_Q_error": float(err[ij]),
                             "max_error_entry": [int(v) for v in ij],
                             "max_abs_coefficient_error": str(coefferr),
                             "max_abs_Q_change_from_previous_order": None if prev is None else float(np.max(np.abs(q-prev)))})
                prev = q
            cell = {"a": astr, "gamma": gamma, "reference_dps": mp.mp.dps,
                    "quotient_vs_sinc_max_coefficient_error": formula_error,
                    "quadrature": runs,
                    "pass": all(v["max_abs_Q_error"] <= TOL for v in runs[-2:])}
            if astr == "0":
                # Q=4rr^T is PSD analytically. A tiny floating negative eigenvalue
                # is reported as roundoff, never as a planted detection.
                eigs = np.linalg.eigvalsh(np.asarray(qref, dtype=float))
                cell["a0_Q_PSD_diagnostic"] = {
                    "exact_factorization": "Q=4 r r^T, r real; rank<=1",
                    "min_eigenvalue_float64": float(eigs[0]),
                    "max_eigenvalue_float64": float(eigs[-1]),
                    "roundoff_tolerance": TOL,
                    "pass": float(eigs[0]) >= -TOL,
                    "A_plus_Q_checked": False}
                cell["pass"] &= cell["a0_Q_PSD_diagnostic"]["pass"]
            cells.append(cell)
    # Explicit exact removable-resonance check for sinc evaluator, not part of grid.
    ll = mp.log(M)
    resonances = []
    for j in (0, 1, 40, 80):
        w = 2*mp.pi*j/ll
        d = 1 if j == 0 else mp.sqrt(2)
        cv = d * (-1)**j * mp.sqrt(ll)/2 * (mp.sinc(0)+mp.sinc(w*ll))
        expected = mp.sqrt(ll) if j == 0 else (-1)**j*mp.sqrt(ll/2)
        resonances.append({"j": j, "a": "0", "gamma": "omega_j",
                           "absolute_error": str(abs(cv-expected))})
    out = {"schema": "corner_physical_kernel_gate.v1", "honesty": "DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH; PX_RH_CLAIM_NOT_MADE",
           "m": M, "dimension": M+1, "L": str(L), "multiplicity": 1,
           "tolerance_absolute_entrywise": TOL, "orders": ORDERS,
           "pre_run_predictions_commit_parent_reported": "bc9204929faccc66f952ff9df9273e0b94afed4e",
           "predictions_sha256": sha(ROOT / "PREDICTIONS.md"),
           "source_pins": [
               {"path": "/tmp/corner_PROSHKA_VERDICT_CCM_HIGHER_MOMENTS_2026-11-04.md", "sha256": sha("/tmp/corner_PROSHKA_VERDICT_CCM_HIGHER_MOMENTS_2026-11-04.md"), "basis_lines": [122,122], "coefficient_and_block_lines": [603,612]},
               {"path": "/tmp/corner_PROSHKA_VERDICT_EXACT_MECHANISM_E1_E3_2026-11-04.md", "sha256": sha("/tmp/corner_PROSHKA_VERDICT_EXACT_MECHANISM_E1_E3_2026-11-04.md"), "basis_lines": [151,154], "physical_kernel_lines": [439,443]}],
           "runtime": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__, "mpmath": mp.__version__, "longdouble_precision_decimal": int(np.finfo(LD).precision)},
           "cells": cells, "removable_resonances": resonances,
           "positive_a_cells_passed": sum(c["pass"] for c in cells if c["a"] != "0"),
           "a0_cells_passed": sum(c["pass"] for c in cells if c["a"] == "0"),
           "max_abs_Q_error_final_positive_a": max(c["quadrature"][-1]["max_abs_Q_error"] for c in cells if c["a"] != "0"),
           "pass": all(c["pass"] for c in cells),
           "budget": {"initial_CPU_seconds": 120, "actual_process_CPU_seconds": time.process_time()-cpu0, "actual_wall_seconds": time.perf_counter()-wall0, "max_RSS_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
           "limitations": ["Numerical quadrature agreement is diagnostic, not a certified enclosure.", "a=0 check concerns Q only; no A source or full planted scan was run.", "Partial local tree has no Git metadata; predictions commit identity is parent-supplied."]}
    out["code_sha256"] = sha(__file__)
    (HERE / "gate.json").write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps({k: out[k] for k in ("pass", "positive_a_cells_passed", "a0_cells_passed", "max_abs_Q_error_final_positive_a", "budget")}))
    return 0 if out["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
