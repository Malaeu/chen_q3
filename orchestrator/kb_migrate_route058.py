#!/usr/bin/env python3
"""Внести маршрут 058 `REALZERO_GROUND_DIAGONAL_TO_XI` в таблицу `assembly`.

Источник — мастер-маршрут судьи
`docs/routeB_bus/proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`
(пин `b124fba1`). Восемь ворот полной карты §4 переносятся один-в-один; статусы и
поставщики — из текста маршрута, сверенные с деревом.

ЗАЧЕМ СКРИПТ, А НЕ РУЧНОЙ SQL. Прежние цепи вносились руками, и восстановить, откуда
взялась строка, теперь нельзя. Здесь данные лежат в одном литерале: маршрут можно
перечитать, сверить и пересобрать, а `--check` показывает расхождение с базой, ничего
не меняя.

НЕСУЩИЙ ИНВАРИАНТ МАРШРУТА, который эта цепь обязана удерживать: последовательность
одна. `G_j` (transform конечного ground-вектора) несёт вещественность нулей, `T_j`
(transform пролатного пробника) несёт сходимость к Ξ. Мост переносит сходимость **на
`G_j`**. Цепь «trial сходится, ground вещественен, значит RH» использует две разные
последовательности и запрещена.

Идемпотентен: повторный `--write` заменяет строки той же цепи, чужие не трогает.
"""
from __future__ import annotations

import argparse
import sqlite3
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DB = REPO / "q3.lean.aristotle/aristotle_db/knowledge.db"
CHAIN = "REALZERO_GROUND_DIAGONAL_TO_XI"
RUN_ID = "route058_g2b_proved_2026-08-12"

Q3 = "q3.lean.aristotle/Q3/Proofs/RouteB/"

# step, requirement, required_by, supplied_by, supplier_file, supplier_line, status, note, objects
STEPS: list[tuple] = [
    (0, "точный объект, координата и нормировка зафиксированы",
     "весь маршрут",
     "координаты источника заданы, расписание и нормировка — частично",
     Q3 + "CCMFiniteWeilSourceMatrix.lean", 20, "GAP",
     "G0 OPEN_PARTIAL. Целые узлы источника и полюсы 2*pi*k/L определены; "
     "кофинальное расписание (m_j, N_j) и точная невырожденная нормировка не закреплены.",
     "ccmModeFinite,proposition59Pole,кофинальное расписание,нормировка"),

    (1, "кофинальный конечный simple-even ground-пакет",
     "G2, вход потребителя вещественности",
     "penalty-сертификат (A) · блочное расщепление чётности (B) · GLOWER/Yoshida (C) · "
     "Schur/Feshbach (D) · ранг-инерция (E) · внешняя теорема (F)",
     Q3 + "H2aPenaltyCoercivity.lean", 395, "GAP",
     "G1 OPEN_MAIN_SPECTRAL_FRONT. Нужен пакет (epsilon_j, xi_j, heig, hbottom, hsimple, "
     "hnormalized) на кофинальном пути. Чётность отдельно НЕ поставляется — её выводит "
     "обёртка ..._simple_normalized. Шесть поставщиков-кандидатов, ни один не доведён.",
     "epsilon,xi,heig,hbottom,hsimple,hnormalized,H2a_SimpleEvenGround_FromPenaltyCoercivity"),

    (2, "вещественность нулей лагранжева многочлена ground-строки",
     "G2b",
     "ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized",
     Q3 + "CCMFiniteWeilParity.lean", 161, "READY",
     "Потребитель существует и доказан условно на пакете G1. Внешняя обёртка, hxiEven "
     "выводится внутри. Базис фактора устраняется автоматикой (Probe_QuotientBasis_Auto).",
     "ZerosRealOn,sourceLagrangePolynomial,ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized"),

    (3, "перенос МНОЖЕСТВА нулей с многочлена на преобразование Proposition-5.9",
     "F_j целая с вещественными нулями",
     "Proposition59GroundLagrangeZeroSetBridge",
     Q3 + "Proposition59GroundLagrangeZeroSetBridge.lean", 341, "READY",
     "G2b PROVED 2026-08-12. Exact same-row transfer on Finset.Icc (-(N:Z)) N; "
     "coordinate -L*z/(2*pi); removable-pole, exterior sine-lattice and off-lattice "
     "Cauchy/Lagrange branches; final supplier literally ..._simple_normalized. "
     "УБИТО и не возвращено: Pstar = c_N * многочлен.",
     "proposition59RawTransform,proposition59PoleKernel,dslope,Proposition59GroundLagrangeZeroSetBridge"),

    (4, "та же F_j отслеживает projected prolate trial локально равномерно",
     "G3c",
     "невязка делить на истинный зазор (A) · Feshbach-граф (B) · penalty-overlap (C) · "
     "defect-Gram (D) · low/high split (E) · norm-resolvent Galerkin (F)",
     None, None, "GAP",
     "G3 MAIN_WALL. Главная стена маршрута. Переносится СХОДИМОСТЬ на ground-семью, "
     "не вещественность на trial: вещественность неустойчива к возмущению. Убитое "
     "решение: exact ground equals trial.",
     "FiniteGroundTransformToCCMTrialLocallyUniform,истинный зазор,невязка"),

    (5, "projected trial отслеживает continuum CCM trial",
     "G4",
     "не назначен",
     None, None, "GAP",
     "G3c. Проекция конечного среза на континуальный пробник CCM.",
     "kTrial,centeredPstarFamily,проекционный хвост"),

    (6, "CCM Lemma 7.3: континуальное trial-преобразование сходится к Xi",
     "F_j -> Xi локально равномерно",
     "CCM Lemma 7.3 — доказана в статье, порт в проект отсутствует",
     None, None, "GAP",
     "G4 PAPER_PROVED_PROJECT_IMPORT_OPEN. Это тот же объект, что doc-alias hermfact1: "
     "статус PAPER_PROVED, Lean-порт OPEN. Локально равномерно на замкнутых подполосах.",
     "CCM_Lemma_7_3,centeredXi,локально равномерная сходимость"),

    (7, "zero-escape: вещественные нули аппроксимантов запрещают невещественные у предела",
     "Q3.RH",
     "rh_of_canonical_strip_slots · ZerosApproachOn · ClassicalXiInterface",
     Q3 + "CanonicalRHRouteSkeleton.lean", 177, "READY",
     "G5. Логическое ядро ДОКАЗАНО в крыше: одна фиксированная выбранная семья с "
     "вещественными нулями и нужным пределом даёт Q3.RH. sameCofinalGuard не позволяет "
     "подставить независимую диагональ. Аналитический перенос в крыше доступен.",
     "rh_of_canonical_strip_slots,ZerosApproachOn,Q3.RH,sameCofinalGuard"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="внести (иначе только показать)")
    ap.add_argument("--check", action="store_true", help="сверить с базой, ничего не менять")
    args = ap.parse_args()

    if not DB.is_file():
        print(f"нет базы {DB}", file=sys.stderr)
        return 2

    if args.check:
        con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
        have = {r[0]: r for r in con.execute(
            "select step, requirement, status from assembly where chain=?", (CHAIN,))}
        print(f"в базе шагов цепи {CHAIN}: {len(have)} · в скрипте: {len(STEPS)}")
        for s in STEPS:
            row = have.get(s[0])
            if row is None:
                print(f"  ОТСУТСТВУЕТ  шаг {s[0]}  {s[1][:60]}")
            elif row[2] != s[6]:
                print(f"  СТАТУС РАЗОШЁЛСЯ шаг {s[0]}: база {row[2]} · скрипт {s[6]}")
        extra = set(have) - {s[0] for s in STEPS}
        for e in sorted(extra):
            print(f"  ЛИШНИЙ В БАЗЕ шаг {e}")
        return 0

    print(f"цепь {CHAIN}, шагов {len(STEPS)}:")
    for s in STEPS:
        print(f"  {s[0]}  [{s[6]:<9}] {s[1][:74]}")
    if not args.write:
        print("\nсухой прогон. Внести: --write")
        return 0

    con = sqlite3.connect(DB)
    con.execute("delete from assembly where chain=?", (CHAIN,))
    con.executemany(
        "insert into assembly"
        " (chain, step, requirement, required_by, supplied_by, supplier_file,"
        "  supplier_line, status, note, run_id, objects)"
        " values (?,?,?,?,?,?,?,?,?,?,?)",
        [(CHAIN, s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], RUN_ID, s[8]) for s in STEPS])
    con.commit()
    n = con.execute("select count(*) from assembly where chain=?", (CHAIN,)).fetchone()[0]
    print(f"внесено строк: {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
