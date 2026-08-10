#!/usr/bin/env python3
"""GLOWER Вход 2: corrected-head сертификат B_c − d⁻¹R_c*R_c ⪰ 0 на конечном срезе.

Вердикт `PROSHKA_GLOWER_EXACT_CLOSURE_2026-08-09` раскладывает `Q_13^odd − c₀I` блоками

    [ A_c  E* ]        A_c = A − c₀I  (голова H_R)
    [ E    D_c]        D_c = D − c₀I  (хвост  T_R)

и требует одного конечномерного сертификата

    B_c − d⁻¹ R_c* R_c  ⪰  0,
    R_c = E + D_c Y,     B_c = A_c + E*Y + Y*E + Y*D_c Y.

Здесь используется **Re-representation 1**, прямо разрешённая вердиктом: вместо
произвольного `Y` берётся точное решение `D_c Y = −E`, при котором `R_c` обращается в
ноль, и остаётся чистая конечная матрица Шура. В интервальной арифметике ноль не точный,
поэтому `‖R_c‖` оценивается строго и штраф `d⁻¹‖R_c‖²` вычитается всегда — вердикт
запрещает выдавать конечный остаток за полный.

`R` берётся из Phase 4 (`R(μ=1) = 70`), `d = 1 − c₀` — оттуда же: хвост с моды 70 держит
пол `μ = 1`.

ЧТО ЭТО НЕ ДОКАЗЫВАЕТ. Срез конечен. `R_c`, посчитанный здесь, — остаток внутри среза, а
не полный остаток бесконечного хвоста; мод выше `N` в нём нет. PASS является проверкой
PASS-стороны на конечной клетке, а не сертификатом `Q_13^odd ⪰ c₀I`.

Read-only.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
PHASE1 = REPO / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"


def load_phase1(dps: int, N: int | None):
    spec = importlib.util.spec_from_file_location("phase1_cell", PHASE1)
    module = importlib.util.module_from_spec(spec)
    sys.modules["phase1_cell"] = module
    spec.loader.exec_module(module)
    module.ctx.dps = dps
    if N is not None:
        module.N = N
    return module


def submatrix(source, rows: range, cols: range, arb_mat):
    out = arb_mat(len(rows), len(cols))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            out[i, j] = source[r, c]
    return out


def frobenius_upper(matrix, arb):
    """Строгая верхняя оценка ‖M‖_F ≥ ‖M‖_2 — консервативно, зато без итераций.

    Y решается интервально, поэтому R_c = E + D_c·Y — это интервал вокруг нуля, и сумма
    его квадратов имеет нижнюю границу ниже нуля. Корень берётся от ВЕРХНЕЙ границы
    суммы: так оценка остаётся строгой сверху и не даёт nan.
    """
    total = arb(0)
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            total += matrix[i, j] ** 2
    upper = arb(total.upper())
    return upper.sqrt() if upper > 0 else arb(0)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=120)
    ap.add_argument("--N", type=int, default=240)
    ap.add_argument("--R", type=int, default=70, help="граница головы из Phase 4")
    ap.add_argument("--c0-exp", type=int, default=58, help="c₀ = 10^-c0_exp")
    args = ap.parse_args()

    from flint import arb, arb_mat  # noqa: E402

    print(f"GLOWER corrected head · m=13 odd · N={args.N} · R={args.R} · "
          f"c₀=1e-{args.c0_exp} · dps={args.dps}", flush=True)

    started = time.time()
    p1 = load_phase1(args.dps, args.N)

    # ВАЖНО: c₀ считается ПОСЛЕ установки точности. Посчитанная до неё, она несёт радиус
    # дефолтных 15 знаков (~1e-73 при 1e-58), и LDL^T без пивотирования раздувает его до
    # 1e-3 к 22-му шагу — сертификат ложно падает в INSUFFICIENT_PRECISION.
    c0 = arb(1) / arb(10) ** args.c0_exp
    builder = p1.CCMArbBuilder()
    _even, odd, _s = builder.parity_blocks()
    n = odd.nrows()
    print(f"  odd-блок {n}×{n} построен за {time.time()-started:.0f} с", flush=True)
    if args.R >= n:
        print("R не меньше размера блока — нечего разделять."); return 2

    head, tail = range(args.R), range(args.R, n)
    A = submatrix(odd, head, head, arb_mat)
    D = submatrix(odd, tail, tail, arb_mat)
    E = submatrix(odd, tail, head, arb_mat)
    for i in range(A.nrows()):
        A[i, i] = A[i, i] - c0
    for i in range(D.nrows()):
        D[i, i] = D[i, i] - c0

    # d из Phase 4: хвост с моды R держит пол μ=1, значит D_c ⪰ (1−c₀)I.
    d = arb(1) - c0
    print(f"  d = 1 − c₀ (из Phase 4: K_odd[{args.R}:,{args.R}:] ⪰ 1·I)", flush=True)

    print("  решаю D_c·Y = −E …", flush=True)
    started = time.time()
    minus_E = arb_mat(E.nrows(), E.ncols())
    for i in range(E.nrows()):
        for j in range(E.ncols()):
            minus_E[i, j] = -E[i, j]
    Y = D.solve(minus_E)
    print(f"    решено за {time.time()-started:.0f} с", flush=True)

    R_c = E + D * Y
    res_norm = frobenius_upper(R_c, arb)
    print(f"  ‖R_c‖_F ≤ {res_norm}", flush=True)

    Et_Y = E.transpose() * Y
    B_c = A + Et_Y + Et_Y.transpose() + Y.transpose() * D * Y

    penalty = (res_norm ** 2) / d
    certificate = arb_mat(B_c.nrows(), B_c.ncols())
    for i in range(B_c.nrows()):
        for j in range(B_c.ncols()):
            certificate[i, j] = B_c[i, j]
    for i in range(B_c.nrows()):
        certificate[i, i] = certificate[i, i] - penalty

    print(f"  штраф d⁻¹‖R_c‖² ≤ {penalty}", flush=True)

    bare = p1.interval_ldlt(B_c)
    if bare["pass"]:
        print(f"  B_c без штрафа: PASS, мин.пивот {str(bare['minimum_pivot']['lower'])[:28]}",
              flush=True)
    else:
        print(f"  B_c без штрафа: {bare['status']} на пивоте {bare.get('failed_pivot_index')}",
              flush=True)

    print("  интервальный LDL^T на B_c − d⁻¹R_c*R_c …", flush=True)
    report = p1.interval_ldlt(certificate)

    print()
    print(f"размер головы          : {B_c.nrows()}")
    print(f"статус                 : {report['status']}")
    if report["pass"]:
        print(f"минимальный пивот      : {report['minimum_pivot']['lower']}")
        print(f"максимальный пивот     : {report['maximum_pivot']['upper']}")
        print()
        print("GLOWER_CORRECTED_HEAD=PASS_ON_FINITE_CUT")
    else:
        print(f"провал на пивоте       : {report.get('failed_pivot_index')}")
        print(f"пивот                  : {report.get('failed_pivot')}")
        print(f"положительных до него  : {report.get('positive_pivots_before_failure')}")
        print()
        code = ("INSUFFICIENT_PRECISION" if report["status"] == "INSUFFICIENT_PRECISION"
                else "NONPOSITIVE")
        print(f"GLOWER_CORRECTED_HEAD={code}")
    print()
    print("НЕ сертификат Q_13^odd ⪰ c₀I: остаток посчитан внутри среза, мод выше N в нём нет.")
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
