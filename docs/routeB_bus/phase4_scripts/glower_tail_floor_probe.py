#!/usr/bin/env python3
"""GLOWER preflight, дешёвый зонд: где начинается хвостовой пол μ на odd-секторе.

Вердикт PROSHKA_GLOWER_EXACT_CLOSURE_2026-08-09 требует вход 1 — `D_c ⪰ dI` с явным
`d > 0` на хвосте `T_R`, и объявляет минимальным named gap извлечение константы `R`.
Мифос оценил вилку `R(μ=1) ∈ [2·10², 10⁵]` двумя прокси-оценками и предложил мерить
окном хвостовых мод.

Здесь мерится прямее: для каждого среза `n ≥ n0` проверяется интервальным LDL^T, верно ли

    K_odd[n0:, n0:]  ⪰  μ·I,

то есть держит ли хвост, начинающийся с моды `n0`, пол `μ`. Минимальное такое `n0` —
это и есть численная оценка `R` при данном `μ`, снизу ограниченная нашим обрезанием.

ЧТО ЭТО НЕ ДОКАЗЫВАЕТ. Срез конечен: моды выше `N` не входят, поэтому измеряется
компрессия истинного `T_R`, а не он сам. PASS здесь — свидетельство, а не сертификат
хвоста: для настоящего `D_c ⪰ dI` нужна теорема (Yoshida [33, Lemma 3] либо Suzuki
Theorem 4.3, см. Q8 в PROSHKA_QUEUE.md). FAIL при данном `n0` тоже ничего не убивает —
он говорит лишь, что порог выше этого `n0`.

Матрица строится теми же source-side формулами, что в Phase 1
(`phase1_scripts/ccm_control_cell_penalty.py`), импортом, а не копией — чтобы
расхождение формул было невозможно по построению.

Read-only: репозиторий не меняется, результат печатается в stdout.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
PHASE1 = REPO / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"


def load_phase1(dps: int):
    """Импортировать построитель Phase 1, не выполняя его main()."""
    spec = importlib.util.spec_from_file_location("phase1_cell", PHASE1)
    module = importlib.util.module_from_spec(spec)
    sys.modules["phase1_cell"] = module
    spec.loader.exec_module(module)
    module.ctx.dps = dps
    return module


def progress(done: int, total: int, started: float, label: str) -> None:
    if not sys.stdout.isatty():
        return
    frac = done / total
    eta = (time.time() - started) * (1 - frac) / frac if frac else 0.0
    bar = "#" * int(30 * frac) + "." * (30 - int(30 * frac))
    sys.stdout.write(f"\r[{bar}] {100*frac:5.1f}%  ETA {eta:5.0f}s  {label:<28}")
    sys.stdout.flush()


def tail_holds_floor(odd, n0: int, mu, arb, arb_mat, ldlt) -> tuple[bool, str]:
    """Проверить K_odd[n0:, n0:] − mu·I ⪰ 0 интервальным LDL^T без пивотирования."""
    size = odd.nrows() - n0
    if size <= 0:
        return False, "пустой срез"
    shifted = arb_mat(size, size)
    for i in range(size):
        for j in range(size):
            shifted[i, j] = odd[n0 + i, n0 + j] - (mu if i == j else 0)
    report = ldlt(shifted)
    if report["pass"]:
        return True, str(report["minimum_pivot"].get("lower", "?"))
    return False, f'{report["status"]} @ pivot {report.get("failed_pivot_index", "?")}'


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=60, help="точность Arb (пол ~1, хватает 60)")
    ap.add_argument("--mu", type=float, default=1.0, help="целевой пол хвоста")
    ap.add_argument("--step", type=int, default=10, help="шаг сетки по n0")
    ap.add_argument("--N", type=int, default=None,
                    help="обрезание (по умолчанию 120, как в Phase 1); "
                         "менять, чтобы отличить настоящий порог от артефакта обрезания")
    args = ap.parse_args()

    print(f"GLOWER tail-floor probe · ячейка m=13 · μ={args.mu} · dps={args.dps}", flush=True)
    print("Строю odd-блок source-side формулами Phase 1 …", flush=True)

    p1 = load_phase1(args.dps)
    if args.N is not None:
        p1.N = args.N  # builder читает N при инициализации
    from flint import arb, arb_mat  # noqa: E402  (после настройки ctx)

    started = time.time()
    builder = p1.CCMArbBuilder()
    _even, odd, _samples = builder.parity_blocks()
    print(f"  odd-блок {odd.nrows()}×{odd.ncols()} построен за {time.time()-started:.0f} с", flush=True)

    mu = arb(args.mu)
    grid = list(range(0, odd.nrows(), args.step))
    started = time.time()
    rows = []
    for idx, n0 in enumerate(grid, 1):
        ok, pivot = tail_holds_floor(odd, n0, mu, arb, arb_mat, p1.interval_ldlt)
        rows.append((n0, odd.nrows() - n0, ok, pivot))
        progress(idx, len(grid), started, f"n0={n0} {'PASS' if ok else 'fail'}")
    if sys.stdout.isatty():
        print()

    print()
    print(f"{'n0':>5} {'размер':>7} {'K_odd[n0:,n0:] ⪰ μI':>22}   нижняя граница пивота")
    print("─" * 74)
    first_pass = None
    for n0, size, ok, pivot in rows:
        mark = "PASS" if ok else "fail"
        if ok and first_pass is None:
            first_pass = n0
        print(f"{n0:>5} {size:>7} {mark:>22}   {pivot}")

    print()
    if first_pass is None:
        print(f"НЕТ СРЕЗА с полом μ={args.mu} внутри N={odd.nrows()}.")
        print(f"Значит R(μ={args.mu}) > {odd.nrows()} — вилка Мифоса не сужена снизу этим прогоном.")
        print("GLOWER_TAIL_FLOOR_PROBE=NO_FLOOR_WITHIN_TRUNCATION")
    else:
        print(f"Первый срез с полом μ={args.mu}:  n0 = {first_pass}")
        print(f"Численная оценка R(μ={args.mu}) ≈ {first_pass} для обрезания N={odd.nrows()}.")
        print("GLOWER_TAIL_FLOOR_PROBE=FLOOR_OBSERVED")
    print()
    print("НЕ сертификат хвоста: измерена компрессия T_R, моды выше N не входят.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
