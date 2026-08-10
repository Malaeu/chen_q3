#!/usr/bin/env python3
"""Префлайт Мифоса: низкий спектр B_480 и проецированная невязка ‖P·G·P‖.

Ставки, зарегистрированные им ДО счёта:
  P-M4  низкий кластер B_480 имеет dim ≤ 6 и зазор ≥ 0.1 над собой,  p = 0.55
  P-M5  ‖P·G·P‖ ≤ 1e-50 — проецированная невязка мала, хотя полный Грам 7.6e-02,
        p = 0.50 — «ставка, на которой стоит весь ремонт; её опровержение —
        настоящий сигнал смерти пола на клетке m=13»

Логика: полный Грам заряжает все направления и валит сертификат на единичной шкале
(R10). Но пол живёт на `β*`-шкале в узком низком подпространстве. Если дальняя связь
почти ортогональна этому подпространству, спектрально-разрешённый штраф проходит там,
где скалярный и полный Грам падают.

Диагностика: собственные значения считаются `mpmath.eigsy` в высокой точности, потому
что спектр растянут от ~1e-55 до O(1) — в double нижняя часть неразличима в принципе.
Это НЕ интервальный сертификат: для строгости нужны интервальные границы
инвариантного подпространства, здесь их нет.

Read-only.
"""
from __future__ import annotations
import argparse, importlib.util, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
PHASE1 = REPO / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"


def load_phase1(dps, N):
    spec = importlib.util.spec_from_file_location("phase1_cell", PHASE1)
    m = importlib.util.module_from_spec(spec); sys.modules["phase1_cell"] = m
    spec.loader.exec_module(m); m.ctx.dps = dps; m.N = N
    return m


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=200)
    ap.add_argument("--N", type=int, default=960)
    ap.add_argument("--R", type=int, default=70)
    ap.add_argument("--S", type=int, default=480)
    ap.add_argument("--c0-exp", type=int, default=58)
    ap.add_argument("--cluster-max", type=int, default=12)
    args = ap.parse_args()

    from flint import arb, arb_mat
    from mpmath import mp, mpf, matrix as mpmatrix, matrix as mpm, eigsy
    mp.dps = args.dps

    print(f"Префлайт низкого спектра · B_{args.S} · dps={args.dps}", flush=True)
    t0 = time.time()
    p1 = load_phase1(args.dps, args.N)
    c0 = arb(1) / arb(10) ** args.c0_exp
    d = arb(1) - c0
    b = p1.CCMArbBuilder(); _e, odd, _s = b.parity_blocks()
    print(f"  odd {odd.nrows()}² за {time.time()-t0:.0f} с", flush=True)

    R, S = args.R, args.S
    A = arb_mat(R, R); D = arb_mat(S - R, S - R); E = arb_mat(S - R, R)
    for i in range(R):
        for j in range(R): A[i, j] = odd[i, j]
        A[i, i] = A[i, i] - c0
    for i in range(S - R):
        for j in range(S - R): D[i, j] = odd[R + i, R + j]
        D[i, i] = D[i, i] - c0
        for j in range(R): E[i, j] = odd[R + i, j]
    mE = arb_mat(S - R, R)
    for i in range(S - R):
        for j in range(R): mE[i, j] = -E[i, j]
    Y = D.solve(mE)
    EtY = E.transpose() * Y
    B = A + EtY + EtY.transpose() + Y.transpose() * D * Y

    t0 = time.time(); G = arb_mat(R, R)
    for k in range(S, odd.nrows()):
        r = [odd[k, j] for j in range(R)]
        for m_ in range(S - R):
            dkm = odd[k, R + m_]
            for j in range(R): r[j] = r[j] + dkm * Y[m_, j]
        for i in range(R):
            for j in range(i, R):
                v = r[i] * r[j]
                G[i, j] = G[i, j] + v
                if i != j: G[j, i] = G[j, i] + v
    print(f"  Грам за {time.time()-t0:.0f} с", flush=True)

    Bm = mpmatrix(R, R)
    Gm = mpmatrix(R, R)
    for i in range(R):
        for j in range(R):
            # str(arb) даёт формат «[0.123 +/- 1e-20]» — mpf его не парсит.
            # Нужен .str(n, radius=False): чистая мантисса без скобок.
            Bm[i, j] = mpf(B[i, j].mid().str(args.dps, radius=False))
            Gm[i, j] = mpf(G[i, j].mid().str(args.dps, radius=False))

    print("  собственное разложение B (mpmath.eigsy) …", flush=True)
    t0 = time.time(); vals, vecs = eigsy(Bm)
    print(f"    за {time.time()-t0:.0f} с", flush=True)
    ev = sorted(range(R), key=lambda i: vals[i])

    print()
    print("  низ спектра B_480:")
    for rank, i in enumerate(ev[:args.cluster_max]):
        print(f"    λ[{rank}] = {mp.nstr(vals[i], 8)}")
    print(f"    …")
    print(f"    λ[{R-1}] = {mp.nstr(vals[ev[-1]], 8)}  (верх)")

    print()
    print("  зазоры между соседними снизу:")
    best_dim, best_gap = None, 0
    for k in range(1, args.cluster_max):
        gap = vals[ev[k]] - vals[ev[k - 1]]
        print(f"    после dim={k}:  зазор = {mp.nstr(gap, 6)}")
        if gap > best_gap:
            best_dim, best_gap = k, gap

    print()
    print(f"  наибольший зазор в низу: после dim={best_dim}, θ = {mp.nstr(best_gap, 6)}")
    pm4 = (best_dim is not None and best_dim <= 6 and best_gap >= mpf("0.1"))
    print(f"  P-M4 (dim ≤ 6 и θ ≥ 0.1): {'ПОДТВЕРЖДЕНА' if pm4 else 'ОПРОВЕРГНУТА'}")

    print()
    print("  проецированная невязка по размерностям кластера:")
    print(f"    {'dim':>4}  {'λ[dim-1]':>14}  {'‖P·G·P‖':>14}  {'отношение к λ':>14}")
    Gv = []
    for b_ in range(args.cluster_max + 1):
        vb = [vecs[i, ev[b_]] for i in range(R)]
        Gv.append([sum(Gm[i, j] * vb[j] for j in range(R)) for i in range(R)])
    quad = {}
    for a_ in range(args.cluster_max + 1):
        va = [vecs[i, ev[a_]] for i in range(R)]
        for b_ in range(args.cluster_max + 1):
            quad[(a_, b_)] = sum(va[i] * Gv[b_][i] for i in range(R))
    pgp_by_dim = {}
    for dim_ in range(1, args.cluster_max + 1):
        # ПОПРАВКА (аудит Прошки, 2026-08-10): раньше здесь стоял max |элемента|
        # блока — это НЕ операторная норма. ‖P·G·P‖ есть наибольшее собственное
        # значение блока (quad[(a,b)])_{a,b<dim}; для dim=1 совпадает, дальше нет.
        blk = mpm(dim_, dim_)
        for a_ in range(dim_):
            for b_ in range(dim_):
                blk[a_, b_] = quad[(a_, b_)]
        for a_ in range(dim_):
            for b_ in range(a_ + 1, dim_):
                avg = (blk[a_, b_] + blk[b_, a_]) / 2
                blk[a_, b_] = avg; blk[b_, a_] = avg
        ev_blk = eigsy(blk, eigvals_only=True)
        m_ = max(abs(x) for x in ev_blk)
        pgp_by_dim[dim_] = m_
        lam = vals[ev[dim_ - 1]]
        ratio = m_ / lam if lam > 0 else mpf('inf')
        print(f"    {dim_:>4}  {mp.nstr(lam, 6):>14}  {mp.nstr(m_, 6):>14}  {mp.nstr(ratio, 6):>14}")
    dim = best_dim if best_dim else 1
    pgp = pgp_by_dim[1]
    print()
    print(f"  ключевое: на ОДНОМ нижнем направлении ‖P·G·P‖ = {mp.nstr(pgp, 8)}")
    print(f"            против λ[0] = {mp.nstr(vals[ev[0]], 8)}")
    trG = sum(Gm[i, i] for i in range(R))
    print(f"    для сравнения: след полного Грама = {mp.nstr(trG, 8)}")
    pm5 = pgp <= mpf("1e-50")
    print(f"  P-M5 (‖P·G·P‖ ≤ 1e-50): {'ПОДТВЕРЖДЕНА' if pm5 else 'ОПРОВЕРГНУТА'}")
    print()
    print(f"GLOWER_LOW_SPECTRUM_PREFLIGHT=P_M4_{'PASS' if pm4 else 'FAIL'}_P_M5_{'PASS' if pm5 else 'FAIL'}")
    print("Диагностика, НЕ сертификат: интервальных границ инвариантного подпространства нет.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
