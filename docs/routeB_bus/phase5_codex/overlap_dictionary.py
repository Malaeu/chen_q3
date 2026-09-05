#!/usr/bin/env python3
"""Probe 25 (Goal 058, 2026-09-05): Fejér×heat dictionary (Malamutmann 2025, Thm 6.2 atoms, log variable) compressed on the literal CCM
full matrix K_{m,N}: positivity margin lambda_min(V^T K V, V^T V) versus density dist(fixed test, span V). Double precision: the compressed
lambda_min is meaningful only down to ~1e-12 (K's own bottom ~1e-31..1e-90 is invisible). DIAGNOSTIC_NEVER_A_PROOF.
Usage: .venv/bin/python docs/routeB_bus/phase5_codex/overlap_dictionary.py [--m 13]
"""
from __future__ import annotations
import argparse, math, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent; sys.path.insert(0, str(HERE.parent / "phase5_scripts")); sys.path.insert(0, str(HERE))
import numpy as np
from flint import ctx, acb
from edge_ledger_build import CCMArbBuilder
from conventions import full_matrix
from lattice_error import centered_xi

def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--m", type=int, default=13); a = ap.parse_args()
    m = a.m; N = m; ctx.dps = max(220, 4 * m + 120); b = CCMArbBuilder(m, N); Kf = full_matrix(b); L = math.log(m)
    K = np.array([[float(Kf[i, j].mid()) for j in range(2 * N + 1)] for i in range(2 * N + 1)])
    xs = np.linspace(0, L, 40001); dx = xs[1] - xs[0]; ns = np.arange(-N, N + 1)
    E = np.exp(-2j * np.pi * np.outer(ns, xs) / L) / math.sqrt(L)   # U_n conj on [0, L]
    def coeffs(gvals): return (E * gvals[None, :]).sum(axis=1) * dx
    ctx.dps = 60; Xi0 = float(centered_xi(acb(0)).real.mid())
    y = np.array([((-1) ** abs(n)) * float(centered_xi(acb(2 * math.pi * abs(n) / L)).real.mid()) / Xi0 for n in ns], dtype=complex); y /= np.linalg.norm(y)
    gb = coeffs(np.exp(-((xs - L / 2) / (L / 6)) ** 2)); gb /= np.linalg.norm(gb)
    def dist(v, V):
        c, *_ = np.linalg.lstsq(V, v, rcond=None); return float(np.linalg.norm(v - V @ c))
    ev = np.linalg.eigvalsh((K + K.T) / 2)
    print(f"# m={m} L={L:.4f} N={N}; lambda_min(K) in double = {ev[0]:.2e} (true ~1e-31..1e-90: below double)", flush=True)
    print("| Delta | t | sigma=sqrt(2t) | M | lambda_min(V^T K V, V^T V) | dist(y,V) | dist(gauss,V) | cond(G) |", flush=True)
    for div in (6, 10, 16, 24, 40):
        Delta = L / div
        for t in (0.002, 0.005, 0.02, 0.05, 0.1, 0.2):
            sig = math.sqrt(2 * t); B = 4 * sig
            centres = [Delta / 2 + k * Delta for k in range(div)]
            cols = []
            for xk in centres:
                g = np.clip(1 - np.abs(xs - xk) / B, 0, None) * np.exp(-(xs - xk) ** 2 / (4 * t)) / math.sqrt(4 * math.pi * t)
                cols.append(coeffs(g))
            V = np.array(cols).T
            G = V.conj().T @ V; G = (G + G.conj().T) / 2; Kc = V.conj().T @ K @ V; Kc = (Kc + Kc.conj().T) / 2
            w = np.linalg.eigvalsh(G); condG = w[-1] / max(w[0], 1e-300)
            if w[0] <= 1e-13 * w[-1]:
                print(f"| L/{div} | {t} | {sig:.3f} | {len(cols)} | (G singular) | {dist(y, V):.2e} | {dist(gb, V):.2e} | {condG:.1e} |", flush=True); continue
            Lc = np.linalg.cholesky(G); Li = np.linalg.inv(Lc); A = Li @ Kc @ Li.conj().T; lam = np.linalg.eigvalsh((A + A.conj().T) / 2)[0]
            print(f"| L/{div} | {t} | {sig:.3f} | {len(cols)} | {lam:+.3e} | {dist(y, V):.2e} | {dist(gb, V):.2e} | {condG:.1e} |", flush=True)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
