#!/usr/bin/env python3
"""GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960 — директива вердикта 2026-08-10.

Вердикт `PROSHKA_VERDICT_PHASE4_CODE_AUDIT_2026-08-10` убил constant-floor суррогат
`d⁻¹·R_out^T·R_out` и выбрал точную внешнюю поправку

    H_exact = R_out^T · C_out⁻¹ · R_out

Здесь исполняются задачи 1–14 директивы на уже построенной матрице `N = 960`.

РАЗБИЕНИЕ (физические моды, метки явные — требование SOURCE_GATES):

    head  : моды 1..70      → индексы [0, 70)
    mid   : моды 71..480    → индексы [70, 480)
    out   : моды 481..960   → индексы [480, 960)

Блоки `K − c₀I` в этом разбиении:

    [ A        E_mid^T   E_out^T ]
    [ E_mid    D_mid     F^T     ]
    [ E_out    F         C       ]

Объекты директивы (задачи 4–7):

    C_out    = C     − F·D_mid⁻¹·F^T
    R_out    = E_out − F·D_mid⁻¹·E_mid
    X        : решение C_out·X = R_out
    H_exact  = R_out^T·X
    H_floor  = d⁻¹·R_out^T·R_out           (запрещённый суррогат, для сравнения)

Проверяемое тождество (задача 8):

    B_480 − H_exact = B_960

где `B_480 = A − E_mid^T·D_mid⁻¹·E_mid` (голова после исключения только mid),
а `B_960` строится напрямую исключением всего хвоста `71..960`.

Диагностики (задачи 11–14) считаются в серединных значениях и помечены как
диагностика: интервальных границ для обобщённых собственных значений здесь нет.

ЗАПРЕЩЕНО директивой и в коде не делается: `N = 1920`; вычисление `B₀`; подгонка
показателя затухания; трактовка минимального пивота `LDL^T` как собственного значения;
максимум элемента матрицы как операторная норма; активация Birman–Schwinger; промоушен
маршрута; заявление RH. Абсолютных путей репозитория нет — только relative.

Read-only.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve()
REPO = HERE.parents[3]
PHASE1_REL = "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"
SELF_REL = "docs/routeB_bus/phase4_scripts/glower_nested_schur_resolvent_audit.py"


def sha256_of(rel: str) -> str:
    return hashlib.sha256((REPO / rel).read_bytes()).hexdigest()


def git_head() -> str:
    try:
        return subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD"],
                              capture_output=True, text=True, timeout=30).stdout.strip()
    except Exception:
        return "UNAVAILABLE"


def load_phase1(dps: int, N: int):
    spec = importlib.util.spec_from_file_location("phase1_cell", REPO / PHASE1_REL)
    m = importlib.util.module_from_spec(spec)
    sys.modules["phase1_cell"] = m
    spec.loader.exec_module(m)
    m.ctx.dps = dps
    m.N = N
    return m


def block(odd, rows, cols, arb_mat):
    out = arb_mat(len(rows), len(cols))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            out[i, j] = odd[r, c]
    return out


def to_mp(M, dps, mpm, mpf):
    n, m = M.nrows(), M.ncols()
    out = mpm(n, m)
    for i in range(n):
        for j in range(m):
            out[i, j] = mpf(M[i, j].mid().str(dps, radius=False))
    return out


def rho_generalized(Bm, Hm, R, mp, mpm, eigsy, cholesky, lu_solve):
    """lambda_max(B^-1/2 H B^-1/2) через холецкий B = L L^T. Диагностика по серединам."""
    L = cholesky(Bm)
    X = mpm(R, R)
    for j in range(R):
        col = lu_solve(L, mpm([Hm[i, j] for i in range(R)]))
        for i in range(R):
            X[i, j] = col[i]
    M = mpm(R, R)
    for i in range(R):
        row = lu_solve(L, mpm([X[i, j] for j in range(R)]))
        for j in range(R):
            M[i, j] = row[j]
    for i in range(R):
        for j in range(i + 1, R):
            a = (M[i, j] + M[j, i]) / 2
            M[i, j] = a
            M[j, i] = a
    ev = eigsy(M, eigvals_only=True)
    return max(ev), min(ev)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=200, help="директива требует прогоны на 200 и 400")
    ap.add_argument("--N", type=int, default=960)
    ap.add_argument("--R", type=int, default=70, help="head: моды 1..R")
    ap.add_argument("--S", type=int, default=480, help="mid кончается на моде S")
    ap.add_argument("--c0-exp", type=int, default=58)
    ap.add_argument("--dims", type=int, default=12, help="задача 12: проекции для dim 1..dims")
    args = ap.parse_args()

    from flint import arb, arb_mat
    from mpmath import mp, mpf, matrix as mpm, eigsy, cholesky, lu_solve
    mp.dps = args.dps

    print("GLOWER_NESTED_SCHUR_RESOLVENT_LOSS_AUDIT_480_960")
    print(f"  HEAD                : {git_head()}")
    print(f"  self   {SELF_REL}")
    print(f"    sha256            : {sha256_of(SELF_REL)}")
    print(f"  source {PHASE1_REL}")
    print(f"    sha256            : {sha256_of(PHASE1_REL)}")
    print(f"  m=13 · ODD · c₀=1e-{args.c0_exp} · dps={args.dps}")
    print(f"  head = моды 1..{args.R}   mid = моды {args.R+1}..{args.S}   "
          f"out = моды {args.S+1}..{args.N}")
    print(flush=True)

    t0 = time.time()
    p1 = load_phase1(args.dps, args.N)
    c0 = arb(1) / arb(10) ** args.c0_exp          # урок R6: после установки точности
    d = arb(1) - c0
    builder = p1.CCMArbBuilder()
    _even, odd, _s = builder.parity_blocks()
    n = odd.nrows()
    print(f"[1] odd-блок {n}×{n} построен за {time.time()-t0:.0f} с", flush=True)
    if n != args.N or args.S >= n:
        print(f"    НЕСОВПАДЕНИЕ размера: ожидалось {args.N}, получено {n}"); return 2

    R, S = args.R, args.S
    head, mid, out = range(R), range(R, S), range(S, n)

    A = block(odd, head, head, arb_mat)
    D_mid = block(odd, mid, mid, arb_mat)
    E_mid = block(odd, mid, head, arb_mat)
    C = block(odd, out, out, arb_mat)
    F = block(odd, out, mid, arb_mat)
    E_out = block(odd, out, head, arb_mat)
    for i in range(R):
        A[i, i] = A[i, i] - c0
    for i in range(len(mid)):
        D_mid[i, i] = D_mid[i, i] - c0
    for i in range(len(out)):
        C[i, i] = C[i, i] - c0

    # ---- задача 2: B_480 = A − E_mid^T D_mid^-1 E_mid ----
    t0 = time.time()
    Zmid = D_mid.solve(E_mid)                       # D_mid^-1 E_mid
    B480 = A - E_mid.transpose() * Zmid
    print(f"[2] B_480 собран за {time.time()-t0:.0f} с", flush=True)

    # ---- задачи 4-5: C_out, R_out ----
    t0 = time.time()
    Wmid = D_mid.solve(F.transpose())               # D_mid^-1 F^T
    C_out = C - F * Wmid
    R_out = E_out - F * Zmid
    print(f"[4-5] C_out {C_out.nrows()}², R_out {R_out.nrows()}×{R_out.ncols()} "
          f"за {time.time()-t0:.0f} с", flush=True)

    # ---- задачи 6-7: X, H_exact ----
    t0 = time.time()
    X = C_out.solve(R_out)
    H_exact = R_out.transpose() * X
    print(f"[6-7] H_exact собран за {time.time()-t0:.0f} с", flush=True)

    # ---- задача 9: запрещённый суррогат, для сравнения ----
    H_floor = arb_mat(R, R)
    RtR = R_out.transpose() * R_out
    inv_d = arb(1) / d
    for i in range(R):
        for j in range(R):
            H_floor[i, j] = inv_d * RtR[i, j]

    # ---- задача 3: B_960 напрямую, исключая весь хвост 71..960 ----
    t0 = time.time()
    T = n - R
    Dtail = arb_mat(T, T)
    Etail = arb_mat(T, R)
    for i in range(T):
        for j in range(T):
            Dtail[i, j] = odd[R + i, R + j]
        Dtail[i, i] = Dtail[i, i] - c0
        for j in range(R):
            Etail[i, j] = odd[R + i, j]
    B960 = A - Etail.transpose() * Dtail.solve(Etail)
    print(f"[3] B_960 собран напрямую за {time.time()-t0:.0f} с", flush=True)

    # ---- задача 8: вложенное тождество ----
    print()
    print("[8] тождество B_480 − H_exact = B_960")
    worst = arb(0)
    overlap_ok = True
    for i in range(R):
        for j in range(R):
            lhs = B480[i, j] - H_exact[i, j]
            diff = lhs - B960[i, j]
            if not diff.contains(0):
                overlap_ok = False
            a = abs(diff)
            if (a - worst).mid() > 0:
                worst = a
    print(f"    интервалы разности накрывают ноль везде : {overlap_ok}")
    print(f"    наибольшая |разность| (середина)        : {float(worst.mid()):.6e}")
    scale = max(abs(float(B960[i, i].mid())) for i in range(R))
    print(f"    масштаб диагонали B_960                 : {scale:.6e}")

    # ---- задача 10: порядок Лёвнера H_floor − H_exact ----
    print()
    print("[10] H_floor − H_exact ⪰ 0 ?")
    diffM = arb_mat(R, R)
    for i in range(R):
        for j in range(R):
            diffM[i, j] = H_floor[i, j] - H_exact[i, j]
    rep = p1.interval_ldlt(diffM)
    print(f"    interval_ldlt: {rep['status']}")

    # ---- задача 11: rho_exact, rho_floor ----
    print()
    print(f"[11] обобщённые отношения (диагностика по серединам, dps={args.dps})")
    Bm = to_mp(B480, args.dps, mpm, mpf)
    He = to_mp(H_exact, args.dps, mpm, mpf)
    Hf = to_mp(H_floor, args.dps, mpm, mpf)
    t0 = time.time()
    rho_e_max, rho_e_min = rho_generalized(Bm, He, R, mp, mpm, eigsy, cholesky, lu_solve)
    rho_f_max, rho_f_min = rho_generalized(Bm, Hf, R, mp, mpm, eigsy, cholesky, lu_solve)
    print(f"    rho_exact = {mp.nstr(rho_e_max, 10)}   (min {mp.nstr(rho_e_min, 4)})")
    print(f"    rho_floor = {mp.nstr(rho_f_max, 10)}   (min {mp.nstr(rho_f_min, 4)})")
    print(f"    за {time.time()-t0:.0f} с", flush=True)
    print(f"    зарегистрированный прогноз вердикта: rho_exact ∈ [0.12, 0.30], "
          f"rho_floor ≈ 1.049387747")

    # ---- задачи 12-14: проекции в собственном базисе B_480 ----
    print()
    print(f"[12-14] спектр B_480 и проецированные ОБОБЩЁННЫЕ нормы (dim 1..{args.dims})")
    vals, vecs = eigsy(Bm)
    order = sorted(range(R), key=lambda i: vals[i])
    Hev = []
    for b_ in range(args.dims):
        vb = [vecs[i, order[b_]] for i in range(R)]
        Hev.append([sum(He[i, j] * vb[j] for j in range(R)) for i in range(R)])
    quad = {}
    for a_ in range(args.dims):
        va = [vecs[i, order[a_]] for i in range(R)]
        for b_ in range(args.dims):
            quad[(a_, b_)] = sum(va[i] * Hev[b_][i] for i in range(R))
    print(f"    {'dim':>4}  {'λ[dim-1]':>14}  {'‖P·H_exact·P‖':>16}  {'отношение':>12}")
    for dim_ in range(1, args.dims + 1):
        blk = mpm(dim_, dim_)
        for a_ in range(dim_):
            for b_ in range(dim_):
                blk[a_, b_] = quad[(a_, b_)]
        for a_ in range(dim_):
            for b_ in range(a_ + 1, dim_):
                av = (blk[a_, b_] + blk[b_, a_]) / 2
                blk[a_, b_] = av
                blk[b_, a_] = av
        nrm = max(abs(x) for x in eigsy(blk, eigvals_only=True))
        lam = vals[order[dim_ - 1]]
        print(f"    {dim_:>4}  {mp.nstr(lam, 6):>14}  {mp.nstr(nrm, 6):>16}  "
              f"{mp.nstr(nrm / lam, 6):>12}")

    print()
    verdict = "CONSTANT_FLOOR_SURROGATE_KILLED_RESOLVENT_ROUTE_ALIVE" \
        if (overlap_ok and rho_e_max < 1) else "AUDIT_INCONCLUSIVE"
    print(f"GLOWER_NESTED_SCHUR_AUDIT={verdict}")
    print("Диагностика по серединам для rho и проекций: интервальных границ обобщённых "
          "собственных значений здесь нет. Тождество [8] проверено интервально.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
