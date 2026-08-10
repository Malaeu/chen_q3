#!/usr/bin/env python3
"""GLOWER ledger: колоночный профиль дрейфа головы + строгая табличная мажоранта.

Контекст. Пивот corrected head падает по `N` (журнал `PHASE4_RESULTS_2026-08-10.md`,
R5: −0.980% / −1.451% / −1.328% на удвоениях, тревога снята при `N = 960`). Падение
предписано алгеброй: поправка `E*D_c⁻¹E` — супремум по растущему хвостовому
подпространству, таблица не может вести себя иначе. Продолжение таблицы запрещено
(`N_extrapolation`). Легальный инструмент о пределе — МАЖОРАНТА, не тренд.

Скрипт делает три яруса.

ЯРУС A — ПРОФИЛЬ (диагностика, эвристика колонок).
    Для каждой хвостовой строки `t` (индексы среза, как в журнале: голова `[:R]`,
    хвост `[R:N]`): `s_t = ‖E[t,:]‖²`, `w_t = s_t/d`. Октавные суммы сравниваются с
    измеренными падениями пивота из журнала. Это ДИАГНОСТИКА: колоночная сумма не
    обязана строго мажорировать падение (перекрёстные члены `D` в ней не учтены);
    её судьба — предмет зарегистрированных ставок, а строгость живёт в ярусе C.

    K6-операционализация (объявлена до счёта, менять запрещено):
      P-L1: для октавы (480, 960] — «ledger объясняет ≥80% падения» ⇔
            БЮДЖЕТ ВАЛИДЕН (Σw ≥ δ строго в интервалах) И ρ = δ/Σw ≥ 0.8.
            Исходы: CONFIRMED / REFUTED_LOOSE (валиден, ρ<0.8) /
                    REFUTED_STRUCTURAL (Σw < δ — перекрёстные члены доминируют).
      P-L3: профиль `w_t` показывает пачки на трансляционной сетке ⇔
            автокорреляция детрендированного log-профиля имеет вторичный пик
            ≥ 0.30 на лаге ≥ 2. Исходы: CONFIRMED / NOT_CONFIRMED.
            Пики печатаются списком — сверка с сеткой log p делается глазами
            и НЕ входит в машинный вердикт (конвенции мод не импортируются).

ЯРУС B — СЕРТИФИКАЦИЯ МИНОРАНТЫ ХВОСТА (строго, интервальный LDLᵀ).
    Для каждого S из лестницы --cert-head: Λ = diag(λ_t) на [S,N),
    λ_t = max(d, τ·(D_c)_tt); проверяется `D_c − Λ ⪰ 0` (τ-лестница вниз
    до чистого μ=1). PASS при S=R заодно ПРОДЛЕВАЕТ R1-замер (μ=1) на
    текущее `N`.

ЯРУС C — ТАБЛИЧНАЯ МАЖОРАНТА С γ-ПОЛОМ (строго).
    M_Λ := A_c − Eᵀ Λ⁻¹ E при разбиении S. Цепочка (все члены — формы):
      для ЛЮБОГО среза N' ∈ (S, N]: D'_c ⪰ Λ' (главная подматрица
      PSD-разности), значит E'ᵀ(D'_c)⁻¹E' ⪯ E'ᵀΛ'⁻¹E' ⪯ EᵀΛ⁻¹E, значит
      corrected head(N') ⪰ M_Λ.
    Лог-лестницей γ = hi·10^(−4k) с уточнением ищется наибольшее γ с
    интервальным сертификатом `M_Λ − γI ⪰ 0`. PASS означает: min-eig
    corrected head ≥ γ для ВСЕХ срезов (S, N] — без тренда, без
    экстраполяции; масштаб γ — эйген-масштаб (~1e-55, соседний с β*), не
    масштаб LDLᵀ-пивотов журнала (~1e-10) — это разные объекты.
    Провал S-ступени = хвостовая энергия почти-нулевого направления за
    модой S ещё велика; первая проходящая ступень измеряет порог S* —
    границу спада хвоста ground-направления (наблюдаемая Input B).
    Для предела остаётся один крюк:
      LOCKB_REMAINDER_HOOK:  Σ_{t>N} s_t/λ_t^{thm} < γ
    — колоночная грань бесконечного остатка, работа теоремы хвоста (Lock B).

ЧТО ЭТО НЕ ДОКАЗЫВАЕТ. Ярус A — эвристика, не грань. Ярусы B–C строги, но
конечны: моды выше `N` не входят ни в Λ, ни в M_Λ; утверждение о пределе
получается только вместе с крюком Lock B. Это НЕ сертификат `Q₁₃^odd ⪰ c₀I`.

Read-only: репозиторий не пишется; --csv пишет профиль в явно указанный файл.

Ориентировочная цена при N=960, лестница S=240,360,480: сборка ~1–3 мин
(dps=300); ярус A — секунды; на каждую ступень S: LDLᵀ яруса B на
(N−S)×(N−S) при dps-tail=40 (720² — десятки минут, чистый Python) и
γ-лестница яруса C (~20 LDLᵀ S×S при полном dps — от минут при S=240 до
~часа при S=480). Гонять под nohup с логом.

Автор: Мифос, 2026-08-10 (протестирован в контейнере на N=100 и N=240 против tip 702e041).
"""
from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from decimal import Decimal
from fractions import Fraction
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
PHASE1 = REPO / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py"

# Пивоты corrected head из журнала PHASE4_RESULTS_2026-08-10.md (commit d1587eeb).
# Точные десятичные строки → arb с ничтожным радиусом.
JOURNAL_PIVOTS: dict[int, str] = {
    120: "2.79613402533503557887e-10",
    240: "2.76873186711502600072e-10",
    480: "2.72855901228750818199e-10",
    960: "2.69234436224724184746e-10",
}


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


def shifted_ldlt(p1, matrix, gamma, arb_mat):
    """Интервальный LDLᵀ для matrix − γI (γ — arb)."""
    n = matrix.nrows()
    shifted = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            shifted[i, j] = matrix[i, j]
    for i in range(n):
        shifted[i, i] = shifted[i, i] - gamma
    return p1.interval_ldlt(shifted)


def certify_floor(p1, matrix, arb, arb_mat, max_calls: int = 30):
    """Наибольшее отделённое γ ≥ 0 с интервальным сертификатом matrix − γI ⪰ 0.

    Масштаб истинного min-eig может быть ~1e-55 (почти-нулевое направление головы),
    поэтому сначала логарифмическая лестница γ = hi·10^(−4k), затем ~6 геометрических
    уточнений. Каждый кандидат проверяется интервальным LDLᵀ — возвращается последний
    ПРОШЕДШИЙ γ, значение строгое. Возврат (γ|None, базовый отчёт)."""
    base = p1.interval_ldlt(matrix)
    if not base["pass"]:
        return None, base
    hi = min(float(matrix[i, i].lower()) for i in range(matrix.nrows()))
    if hi <= 0:
        return arb(0), base
    calls = 0
    g_pass, g_fail = 0.0, hi
    k = 1
    while calls < max_calls:
        g = hi * (10.0 ** (-4 * k))
        if g <= 1e-300:
            break
        rep = shifted_ldlt(p1, matrix, arb(repr(g)), arb_mat)
        calls += 1
        if rep["pass"]:
            g_pass = g
            g_fail = hi * (10.0 ** (-4 * (k - 1))) if k > 1 else hi
            break
        k += 1
    while g_pass > 0 and calls < max_calls and g_fail / g_pass > 1.5:
        g = math.sqrt(g_pass * g_fail)
        rep = shifted_ldlt(p1, matrix, arb(repr(g)), arb_mat)
        calls += 1
        if rep["pass"]:
            g_pass = g
        else:
            g_fail = g
    return (arb(repr(g_pass)) if g_pass > 0 else arb(0)), base


def rolling_median(values: list[float], window: int) -> list[float]:
    half = window // 2
    out = []
    for i in range(len(values)):
        chunk = sorted(values[max(0, i - half): i + half + 1])
        out.append(chunk[len(chunk) // 2])
    return out


def autocorr(series: list[float], max_lag: int) -> list[tuple[int, float]]:
    n = len(series)
    mean = sum(series) / n
    centered = [x - mean for x in series]
    var = sum(x * x for x in centered)
    if var <= 0:
        return []
    result = []
    for lag in range(1, max_lag + 1):
        cov = sum(centered[i] * centered[i + lag] for i in range(n - lag))
        result.append((lag, cov / var))
    return result


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=300,
                    help="точность сборки и яруса C; ярус C живёт на масштабе ~1e-54 (см. журнал)")
    ap.add_argument("--dps-tail", type=int, default=40,
                    help="точность большого LDLᵀ яруса B (пивоты ~0.7, хватает малой)")
    ap.add_argument("--N", type=int, default=960)
    ap.add_argument("--R", type=int, default=70, help="граница головы из Phase 4")
    ap.add_argument("--c0-exp", type=int, default=58, help="c₀ = 10^-c0_exp")
    ap.add_argument("--cert-head", type=str, default="240,360,480",
                    help="лестница границ S сертификационной головы для ярусов B–C, "
                         "через запятую (напр. '240,360,480'); устройство мажоранты, "
                         "Feshbach-голова R не меняется. Слабина мажоранты ~ хвостовая "
                         "энергия почти-нулевого направления за модой S; порог S*, где "
                         "наступает PASS, — измеримая величина (спад хвоста ground-вектора, "
                         "вход Input B).")
    ap.add_argument("--tau", type=float, default=0.5,
                    help="минорантный вес диагонали; 0 = только μ=1 (Λ = d·I)")
    ap.add_argument("--cuts", type=str, default="120,240,480,960",
                    help="срезы журнала для сравнения октав; '' — пропустить ярус A-скоринг")
    ap.add_argument("--skip-tail-cert", action="store_true",
                    help="пропустить большой LDLᵀ яруса B; ярус C тогда берёт Λ = d·I "
                         "БЕЗ свежей сертификации на этом N (печатается кавеат)")
    ap.add_argument("--csv", type=str, default="",
                    help="путь для профиля (n, s_n, w_n); пусто — не писать")
    ap.add_argument("--max-peaks", type=int, default=15)
    args = ap.parse_args()

    from flint import arb, arb_mat  # noqa: E402

    print(f"GLOWER ledger · m=13 odd · N={args.N} · R={args.R} · c₀=1e-{args.c0_exp} · "
          f"τ={args.tau} · dps={args.dps}", flush=True)

    started = time.time()
    p1 = load_phase1(args.dps, args.N)

    # ВАЖНО (урок R6): c₀ считается ПОСЛЕ установки точности.
    c0 = arb(1) / arb(10) ** args.c0_exp
    d = arb(1) - c0

    builder = p1.CCMArbBuilder()
    _even, odd, _s = builder.parity_blocks()
    n = odd.nrows()
    print(f"  odd-блок {n}×{n} построен за {time.time()-started:.0f} с", flush=True)
    if args.R >= n:
        print("R не меньше размера блока — нечего разделять."); return 2

    head, tail = range(args.R), range(args.R, n)
    T = len(tail)
    A = submatrix(odd, head, head, arb_mat)
    D = submatrix(odd, tail, tail, arb_mat)
    E = submatrix(odd, tail, head, arb_mat)          # хвост × голова, как в corrected_head
    for i in range(A.nrows()):
        A[i, i] = A[i, i] - c0
    for i in range(D.nrows()):
        D[i, i] = D[i, i] - c0

    # ---------------- ЯРУС A · профиль ----------------
    print("\nЯРУС A · колоночный профиль", flush=True)
    s = []
    for t in range(T):
        acc = arb(0)
        for j in range(E.ncols()):
            acc += E[t, j] ** 2
        s.append(acc)
    w = [x / d for x in s]
    total_w = sum(w, arb(0))
    print(f"  Σ w_t по хвосту [{args.R}, {n}) ≈ {float(total_w.mid()):.6e} "
          f"(верх {float(total_w.upper()):.6e})", flush=True)

    if args.csv:
        out = Path(args.csv)
        with out.open("w", encoding="utf-8") as fh:
            fh.write("row_index,s_mid,w_mid,w_upper\n")
            for t in range(T):
                fh.write(f"{args.R + t},{float(s[t].mid()):.6e},"
                         f"{float(w[t].mid()):.6e},{float(w[t].upper()):.6e}\n")
        print(f"  профиль записан: {out}", flush=True)

    cuts = [int(c) for c in args.cuts.split(",") if c.strip()] if args.cuts.strip() else []
    cuts = sorted(c for c in cuts if args.R < c <= n and c in JOURNAL_PIVOTS)
    pl1_verdict = "SKIPPED"
    if len(cuts) >= 2:
        print("\n  октава            Σw (интервал‑low)     δ пивота (журнал)     ρ=δ/Σw   бюджет",
              flush=True)
        last_line = None
        for a_cut, b_cut in zip(cuts[:-1], cuts[1:]):
            seg = sum((w[t] for t in range(a_cut - args.R, b_cut - args.R)), arb(0))
            delta = (p1.exact_arb(Fraction(Decimal(JOURNAL_PIVOTS[a_cut])))
                     - p1.exact_arb(Fraction(Decimal(JOURNAL_PIVOTS[b_cut]))))
            strict_valid = (seg - delta).lower() > 0
            strict_invalid = (delta - seg).lower() > 0
            budget = ("VALID" if strict_valid
                      else "INVALID_STRICT" if strict_invalid else "INCONCLUSIVE")
            rho = float(delta.mid()) / float(seg.mid()) if float(seg.mid()) != 0 else float("inf")
            line = (a_cut, b_cut, seg, delta, rho, budget)
            print(f"  ({a_cut:>4},{b_cut:>4}]   {float(seg.lower()):.6e}      "
                  f"{float(delta.mid()):.6e}      {rho:8.3f}   {budget}", flush=True)
            last_line = line
        a_cut, b_cut, seg, delta, rho, budget = last_line
        if budget == "VALID" and rho >= 0.8:
            pl1_verdict = "CONFIRMED"
        elif budget == "VALID":
            pl1_verdict = "REFUTED_LOOSE"
        elif budget == "INVALID_STRICT":
            pl1_verdict = "REFUTED_STRUCTURAL"
        else:
            pl1_verdict = "INCONCLUSIVE_RADIUS"
        print(f"  P-L1 (октава ({a_cut},{b_cut}], порог ρ≥0.8): {pl1_verdict}", flush=True)

    mids = [max(float(x.mid()), 1e-300) for x in w]
    logs = [math.log10(x) for x in mids]
    med = rolling_median(logs, 21)
    detr = [a - b for a, b in zip(logs, med)]
    peaks = [(args.R + t, mids[t]) for t in range(1, T - 1)
             if mids[t] > mids[t - 1] and mids[t] > mids[t + 1] and detr[t] > math.log10(3)]
    peaks.sort(key=lambda x: -x[1])
    top_raw = sorted(((args.R + t, mids[t]) for t in range(T)), key=lambda x: -x[1])[:5]
    print(f"  топ-5 максимумов w_t: " +
          ", ".join(f"{i}:{v:.2e}" for i, v in top_raw), flush=True)
    print(f"\n  пики профиля (>3× локальной медианы), топ-{args.max_peaks}:", flush=True)
    for idx, val in peaks[:args.max_peaks]:
        print(f"    строка {idx:>4}   w ≈ {val:.3e}", flush=True)
    ac = autocorr(detr, min(40, max(2, T // 3)))
    best = max((pair for pair in ac if pair[0] >= 2), key=lambda x: x[1], default=None)
    pl3_verdict = "NOT_CONFIRMED"
    if best and best[1] >= 0.30:
        pl3_verdict = "CONFIRMED"
    if best:
        print(f"  автокорреляция detrended log-профиля: max на лаге ≥2 → "
              f"lag={best[0]}, r={best[1]:.3f}", flush=True)
    print(f"  P-L3 (пачки, порог r≥0.30): {pl3_verdict}", flush=True)

    s_ladder = []
    for tok in args.cert_head.split(','):
        tok = tok.strip()
        if tok:
            v = int(tok)
            v = v if v > args.R else args.R
            v = min(v, n - 10)
            if v not in s_ladder:
                s_ladder.append(v)
    if not s_ladder:
        s_ladder = [args.R]

    verdict_ok = False
    final_code = "MAJORANT_NONPOSITIVE"
    for S in s_ladder:
        if S > args.R:
            head2, tail2 = range(S), range(S, n)
            A = submatrix(odd, head2, head2, arb_mat)
            D = submatrix(odd, tail2, tail2, arb_mat)
            E = submatrix(odd, tail2, head2, arb_mat)
            for i in range(A.nrows()):
                A[i, i] = A[i, i] - c0
            for i in range(D.nrows()):
                D[i, i] = D[i, i] - c0
            T = len(tail2)
        print(f"\n===== S = {S} (Feshbach-голова R={args.R} не меняется) =====", flush=True)

        print(f"ЯРУС B · сертификация D_c ⪰ Λ на [{S}, {n}) (интервальный LDLᵀ)", flush=True)
        lam = None
        lam_tau = None
        if args.skip_tail_cert:
            print("  ПРОПУЩЕН по флагу. Λ = d·I; КАВЕАТ: пол μ=1 на этом N свежим LDLᵀ "
                  "не сертифицирован (журнал даёт его до N=480).", flush=True)
            lam = [d for _ in range(T)]
            lam_tau = 0.0
        else:
            tau_ladder = [args.tau, args.tau / 2, args.tau / 4, 0.0] if args.tau > 0 else [0.0]
            for tau in tau_ladder:
                cand = []
                for t in range(T):
                    grown = arb(repr(tau)) * D[t, t] if tau > 0 else arb(0)
                    cand.append(grown if tau > 0 and (grown - d).lower() > 0 else d)
                started = time.time()
                print(f"  τ={tau}: LDLᵀ({T}×{T}) на D_c − Λ при dps={args.dps_tail} …",
                      flush=True)
                p1.ctx.dps = args.dps_tail
                diff = arb_mat(T, T)
                for i in range(T):
                    for j in range(T):
                        diff[i, j] = D[i, j]
                    diff[i, i] = diff[i, i] - cand[i]
                rep = p1.interval_ldlt(diff)
                p1.ctx.dps = args.dps
                print(f"    {rep['status']} за {time.time()-started:.0f} с", flush=True)
                if rep["pass"]:
                    lam, lam_tau = cand, tau
                    print(f"    мин.пивот {str(rep['minimum_pivot']['lower'])[:28]}",
                          flush=True)
                    if S == args.R and tau >= 0:
                        print(f"  БОНУС: D_c ⪰ Λ ⪰ d·I ⇒ пол μ=1 хвоста [{S},{n}) "
                              f"сертифицирован на N={n}.", flush=True)
                    break
            if lam is None:
                print("  вся τ-лестница провалена, включая τ=0 — противоречит R1 журнала; "
                      "проверить точность/сборку. СТОП.", flush=True)
                final_code = "TAIL_MINORANT_FAILED"
                break

        print(f"ЯРУС C · M_Λ = A_c − EᵀΛ⁻¹E на голове {S}×{S} и γ-пол", flush=True)
        started = time.time()
        H = A.nrows()
        Mmat = arb_mat(H, H)
        for i in range(H):
            for j in range(H):
                Mmat[i, j] = A[i, j]
        for t in range(T):
            inv = arb(1) / lam[t]
            row = [E[t, j] for j in range(H)]
            for i in range(H):
                ri = row[i] * inv
                for j in range(i, H):
                    val = ri * row[j]
                    Mmat[i, j] = Mmat[i, j] - val
                    if j != i:
                        Mmat[j, i] = Mmat[j, i] - val
        print(f"  собрано за {time.time()-started:.0f} с; γ-лестница …", flush=True)
        gamma, rep = certify_floor(p1, Mmat, arb, arb_mat)
        if gamma is None:
            if rep["status"] == "INSUFFICIENT_PRECISION":
                print(f"  M_Λ: пивот {rep.get('failed_pivot_index')} не отличим от нуля "
                      f"при dps={args.dps}; масштаб яруса ~1e-55 — поднять --dps.",
                      flush=True)
                final_code = "MAJORANT_INSUFFICIENT_PRECISION"
            else:
                print(f"  M_Λ: NONPOSITIVE на пивоте {rep.get('failed_pivot_index')} — "
                      f"диагональная миноранта груба на модах ≥ {S}: хвостовая энергия "
                      f"почти-нулевого направления ещё велика. Подъём по S-лестнице.",
                      flush=True)
                final_code = "MAJORANT_NONPOSITIVE"
            continue
        if float(gamma) > 0:
            print(f"  γ-пол сертифицирован: γ = {float(gamma):.3e} "
                  f"(интервальный LDLᵀ M_Λ − γI: PASS)", flush=True)
            print("  справка (двусторонний конверт): верхний Ritz β*₁₂₀=3.0559e-55, "
                  "β*₂₄₀=2.4779e-55 (Phase 2); γ — нижняя сторона на таблице.",
                  flush=True)
        else:
            print("  M_Λ ⪰ 0 подтверждён; положительный γ не отделён "
                  "(поднять --dps или число вызовов).", flush=True)
        print(f"\n  СЛЕДСТВИЕ (строго, без тренда): для всякого среза N' ∈ ({S}, {n}] "
              f"форма на срезе ⪰ c₀, corrected head при разбиении S ⪰ γI, "
              f"γ = {float(gamma):.3e}.", flush=True)
        print(f"  ПОРОГ S* ≤ {S}: диагональной миноранты достаточно с этой моды — "
              f"измеренная граница спада хвоста ground-направления (вход Input B).",
              flush=True)
        print(f"  LOCKB_REMAINDER_HOOK: предел ≥ γ − Σ_(t>{n}) s_t/λ_t^thm; "
              f"крюк закрывает теорема хвоста (Lock B).", flush=True)
        final_code = f"MAJORANT_PASS_TABLE S={S} tau={lam_tau} gamma={float(gamma):.6e}"
        verdict_ok = True
        break

    print(f"\nGLOWER_LEDGER={final_code}")
    print(f"P_L1={pl1_verdict}")
    print(f"P_L3={pl3_verdict}")
    print("\nНЕ сертификат Q_13^odd ⪰ c₀I: Λ и M_Λ конечны, моды выше N не входят; "
          "предел закрывается только вместе с крюком Lock B.")
    return 0 if verdict_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
