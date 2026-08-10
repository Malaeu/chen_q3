#!/usr/bin/env python3
"""Крюк Lock B, шаги 1–2–4 директивы: конечный префикс полной невязки r_k при k > 480.

Директива `GLOWER_FULL_GALERKIN_RESIDUAL_LEDGER_N480` вердикта
`PROSHKA_VERDICT_GLOWER_TAIL_THEOREM_AND_HEAD_DRIFT_2026-08-10` требует девять шагов.
Здесь считаются 1, 2 и 4; шаг 5 (аналитическая огибающая для всех оставшихся `k`)
остаётся математикой и в этот скрипт не входит.

FROZEN_INPUT директивы, воспроизводится дословно:

    m = 13, sector = ODD, c₀ = 1e-58
    head_modes        1..70      → индексы [0, 70)
    finite_tail_modes 71..480    → индексы [70, 480)
    Y_480 = точное интервальное решение D_c·Y = −E на этом разбиении
    d = 1 − c₀

Полная невязка строки `k` (директива, шаг 2):

    r_k = E_k + Σ_{m=71}^{480} D_c(k,m)·Y_m,     k > 480

где `E_k` — связь моды `k` с головой, а `D_c(k,m)` берётся из того же источникового
блока. Печатается профиль `‖r_k‖²`, его форма убывания и частичная сумма — то есть
конечная часть величины `p_480 = d⁻¹·Σ_{k>480}‖r_k‖²` из шага 6.

ЗАЧЕМ ИМЕННО ПОЛНАЯ НЕВЯЗКА. Сырой колоночный бюджет `s_k = ‖E_k‖²` для крюка
бесполезен: измерено `s_k ≈ 50/k²`, значит `Σ_{k>480} s_k ≈ 0.10` — на 54 порядка
больше сертифицированного пола `γ = 1.869e-55`. Вердикт запрещает подмену отдельной
строкой: `FORBIDDEN: raw_E_column_ledger_as_residual`. Смысл `Y` в том, что он гасит
основную часть `E_k`; во сколько раз — этот скрипт и меряет.

ЧТО ЭТО НЕ ДОКАЗЫВАЕТ. Префикс конечен: считаются `k ∈ (480, N]`, моды выше `N` не
входят. Без шага 5 сумма не замыкается, и `p_480` остаётся снизу-неполной. Это НЕ
сертификат и НЕ закрытие крюка.

Read-only.
"""
from __future__ import annotations

import argparse
import importlib.util
import math
import sys
import time
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=200)
    ap.add_argument("--N", type=int, default=960, help="верхний срез: до него считается префикс")
    ap.add_argument("--R", type=int, default=70, help="голова, моды 1..R")
    ap.add_argument("--S", type=int, default=480, help="граница замороженного конечного хвоста")
    ap.add_argument("--c0-exp", type=int, default=58)
    ap.add_argument("--csv", type=str, default="")
    args = ap.parse_args()

    from flint import arb, arb_mat  # noqa: E402

    print(f"Полная невязка, префикс · m=13 odd · N={args.N} · R={args.R} · S={args.S} · "
          f"c₀=1e-{args.c0_exp} · dps={args.dps}", flush=True)

    started = time.time()
    p1 = load_phase1(args.dps, args.N)
    c0 = arb(1) / arb(10) ** args.c0_exp      # урок R6: после установки точности
    d = arb(1) - c0

    builder = p1.CCMArbBuilder()
    _even, odd, _s = builder.parity_blocks()
    n = odd.nrows()
    print(f"  odd-блок {n}×{n} построен за {time.time()-started:.0f} с", flush=True)
    if args.S >= n:
        print("S не меньше размера блока — префикса не существует."); return 2

    R, S = args.R, args.S
    # ---- шаг 1: восстановить Y на замороженном разбиении (R, S) ----
    A = arb_mat(R, R)
    D = arb_mat(S - R, S - R)
    E = arb_mat(S - R, R)
    for i in range(R):
        for j in range(R):
            A[i, j] = odd[i, j]
        A[i, i] = A[i, i] - c0
    for i in range(S - R):
        for j in range(S - R):
            D[i, j] = odd[R + i, R + j]
        D[i, i] = D[i, i] - c0
        for j in range(R):
            E[i, j] = odd[R + i, j]

    started = time.time()
    minus_E = arb_mat(S - R, R)
    for i in range(S - R):
        for j in range(R):
            minus_E[i, j] = -E[i, j]
    Y = D.solve(minus_E)
    print(f"  Y_{S} восстановлен за {time.time()-started:.0f} с "
          f"({Y.nrows()}×{Y.ncols()})", flush=True)

    # ---- шаг 2: полные строки невязки для k > S ----
    started = time.time()
    rows = []
    total = arb(0)
    for k in range(S, n):
        acc = [odd[k, j] for j in range(R)]           # E_k
        for m in range(S - R):
            dkm = odd[k, R + m]                        # D_c(k, m): вне диагонали, c₀ не входит
            for j in range(R):
                acc[j] = acc[j] + dkm * Y[m, j]
        nrm2 = arb(0)
        for j in range(R):
            nrm2 += acc[j] ** 2
        rows.append((k, nrm2))
        total += nrm2
    print(f"  невязки для k ∈ ({S}, {n}] посчитаны за {time.time()-started:.0f} с", flush=True)

    # ---- шаг 4: что видно ----
    print()
    print(f"{'k':>6}   {'‖r_k‖²':>14}   {'‖E_k‖²':>14}   {'гашение':>10}   {'‖r_k‖²·k²':>12}")
    print("─" * 70)
    for k, nrm2 in rows:
        if k in (S, S + 1, S + 10, S + 50, 600, 700, 800, n - 1):
            ek = arb(0)
            for j in range(R):
                ek += odd[k, j] ** 2
            v = float(nrm2.mid())
            e = float(ek.mid())
            ratio = e / v if v > 0 else float("inf")
            print(f"{k:>6}   {v:>14.4e}   {e:>14.4e}   {ratio:>10.2e}   {v*k*k:>12.4e}")

    tot = float(total.mid())
    print()
    print(f"частичная сумма Σ_{{{S}<k≤{n}}} ‖r_k‖²  =  {tot:.6e}")
    print(f"её вклад в p_{S} = d⁻¹·Σ                =  {float((total/d).mid()):.6e}")
    print()
    gamma = 1.869492e-55
    print(f"сертифицированный пол таблицы γ         =  {gamma:.6e}")
    if tot > 0:
        print(f"отношение (частичная сумма)/γ           =  {tot/gamma:.3e}")
    print()
    print("Для сравнения — тот же крюк по СЫРОМУ E (запрещён вердиктом как residual):")
    raw = arb(0)
    for k in range(S, n):
        ek = arb(0)
        for j in range(R):
            ek += odd[k, j] ** 2
        raw += ek
    print(f"  Σ_{{{S}<k≤{n}}} ‖E_k‖² = {float(raw.mid()):.6e}   "
          f"(во сколько раз рыхлее: {float(raw.mid())/tot if tot > 0 else float('inf'):.3e})")

    if args.csv:
        out = Path(args.csv)
        with out.open("w", encoding="utf-8") as fh:
            fh.write("k,r_norm_sq_mid,r_norm_sq_upper\n")
            for k, nrm2 in rows:
                fh.write(f"{k},{float(nrm2.mid()):.6e},{float(nrm2.upper()):.6e}\n")
        print(f"\nпрофиль записан: {out}")

    print()
    print("GLOWER_FULL_RESIDUAL_PREFIX=COMPUTED")
    print("НЕ закрытие крюка: префикс конечен, моды выше N не входят; шаг 5 директивы "
          "(аналитическая огибающая) не выполнен.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
