#!/usr/bin/env python3
"""cheap-closure-finder — очередь незакрытых шагов по ЦЕНЕ, а не по номеру.

Классификация СТРУКТУРНАЯ: порода определяется тем, ГДЕ существуют упомянутые
объекты, а не тем, какие слова написаны рядом в комментарии.

  объект есть в Mathlib, у шага нет поставщика   -> ПОТЕРЯННОЕ ИМЯ    минуты
  объект уже закрыт READY-шагом другой цепочки   -> СВОЙ ФАКТ          минуты
  все объекты наши и существуют в inventory      -> ПЕРЕХОДНИК         часы
  поставщик не .lean (JSON/лог)                  -> ПОДЪЁМ ИЗМЕРЕНИЯ   недели
  объектов нет ни в inventory, ни в Mathlib      -> НЕНАЙДЕННЫЙ        ???

Инструмент НЕ закрывает шаги. Кандидат становится закрытием только после
прогона Lean — иначе это суррогат по форме.
"""
import collections
import difflib
import functools
import json
import pathlib
import re
import sqlite3
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2] / "q3.lean.aristotle"
DB   = f"file:{ROOT}/aristotle_db/knowledge.db?mode=ro"
MLIB = ROOT / ".lake/packages/mathlib/Mathlib"
INV  = pathlib.Path(__file__).resolve().parent / "inventory_RouteB.json"

COST = {"ПОТЕРЯННОЕ ИМЯ": 1, "СВОЙ ФАКТ": 2, "ПЕРЕХОДНИК": 3, "СБОРКА": 4,
        "ПЕРЕНОС МАШИНЫ": 4, "НУЖНА ТЕОРЕМА": 5, "ПОДЪЁМ ИЗМЕРЕНИЯ": 5,
        "НЕНАЙДЕННЫЙ": 6, "НЕ РАЗМЕЧЕН": 9}

# где искать объект в Mathlib, если он там водится
AREAS = {
    "PosDef": "LinearAlgebra/Matrix/PosDef.lean",
    "PosSemidef": "LinearAlgebra/Matrix/PosDef.lean",
    "Basis": "LinearAlgebra/Dimension/Free.lean",
    "базис": "LinearAlgebra/Dimension/Free.lean",
    "finrank": "LinearAlgebra/Dimension/Finite.lean",
    "eigenspace": "LinearAlgebra/Eigenspace/Basic.lean",
    "charpoly": "LinearAlgebra/Matrix/Charpoly/Basic.lean",
    "Hermitian": "LinearAlgebra/Matrix/Hermitian.lean",
    "Rayleigh": "Analysis/InnerProductSpace/Rayleigh.lean",
    "рэлеев": "Analysis/InnerProductSpace/Rayleigh.lean",
    "Tendsto": "Topology/UniformSpace/UniformConvergence.lean",
    "Integrable": "MeasureTheory/Integral/Bochner/Basic.lean",
}
IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b")


def load_context():
    """Три множества, по которым определяется существование объекта."""
    inv = json.loads(INV.read_text())
    items = inv if isinstance(inv, list) else inv.get("objects", inv.get("items", []))
    ours = {o["name"] for o in items if o.get("name")}
    ours |= {n.split(".")[-1] for n in list(ours)}

    con = sqlite3.connect(DB, uri=True)
    mathlib = {r[0] for r in con.execute("select name from atom")}
    mathlib |= {n.split(".")[-1] for n in list(mathlib)}

    # объекты, уже закрытые READY-шагами: источник породы «СВОЙ ФАКТ».
    # Источник — поле objects, а не проза: имя из note может быть упомянуто
    # в отрицании («не доказано X»), и тогда «закрыт» — ложь.
    closed = {}
    for chain, step, objs in con.execute(
            "select chain, step, objects from assembly where status='READY' and objects is not null"):
        for n in (o.strip() for o in objs.split(",")):
            if n:
                closed.setdefault(n, []).append(f"{chain}:{step}")
    con.close()
    return ours, mathlib, closed


@functools.lru_cache(maxsize=None)
def in_mathlib(name):
    """Существует ли объявление в Mathlib НА ДИСКЕ.

    Нельзя опираться на таблицу atom: там только то, что проект УЖЕ использует.
    Новая лемма выглядела бы несуществующей — ровно та ошибка, из-за которой
    шаг 6 год числился GAP, хотя Matrix.PosDef.one лежала в Mathlib.
    """
    short = name.split(".")[-1]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", short):
        return None
    pat = rf"^\s*(protected |private |noncomputable )*(theorem|lemma|def|abbrev) {re.escape(short)}\b"
    try:
        r = subprocess.run(["rg", "-l", "--no-messages", pat, str(MLIB)],
                           capture_output=True, text=True, timeout=25)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None
    return r.stdout.strip().split("\n")[0].replace(str(MLIB) + "/", "")


def names_in(*texts):
    """Lean-идентификаторы, а не слова: с точкой, подчёркиванием или CamelCase."""
    out = set()
    for t in texts:
        for m in IDENT.finditer(t or ""):
            n = m.group(0)
            if len(n) < 4:
                continue
            if "." in n or "_" in n or (n[0].isupper() and any(c.isupper() for c in n[1:])):
                out.add(n)
    return out


def classify(row, ours, mathlib, closed):
    """СТРУКТУРНАЯ порода: по полю objects и по статусу — не по прозе."""
    chain, step, req, sup, sfile, note, status, objects = row
    evidence = []
    if not objects:
        return "НЕ РАЗМЕЧЕН", ["поле objects пусто — заполни, иначе классификация невозможна"]

    # 1. поставщик не Lean — измерение, а не доказательство
    if sfile and not sfile.endswith(".lean"):
        return "ПОДЪЁМ ИЗМЕРЕНИЯ", [f"поставщик {pathlib.Path(sfile).suffix} — не .lean"]

    names = {o.strip() for o in objects.split(",") if o.strip()}
    ours_hit = sorted(n for n in names if n in ours)
    ml_where = {n: in_mathlib(n) for n in names if n not in ours}
    ml_hit = sorted(n for n, w in ml_where.items() if w)
    closed_hit = sorted(n for n in names if n in closed and n in ours)

    # 2. объект уже закрыт READY-шагом другой цепочки
    other = [n for n in closed_hit if any(not c.startswith(chain[:12]) for c in closed[n])]
    if other:
        for n in other[:3]:
            evidence.append(f"{n} закрыт в {', '.join(sorted(set(closed[n]))[:2])}")
        return "СВОЙ ФАКТ", evidence

    # 3. ЧЕГО-ТО НЕТ — решает раньше, чем наличие остального.
    #    Порода определяется недостающей деталью, не собранными.
    missing = sorted(n for n in names if n not in ours and not ml_where.get(n))
    if missing:
        # опечатка или настоящее отсутствие? Похожее имя — сигнал промаха
        for m in missing[:3]:
            near = difflib.get_close_matches(m, ours, n=1, cutoff=0.75)
            if near:
                evidence.append(f"⚠ '{m}' не найдено, но есть похожее '{near[0]}' — опечатка?")
        if ours_hit or ml_hit:
            evidence.append(f"есть {len(ours_hit)+len(ml_hit)}, НЕТ: {', '.join(missing[:3])}")
            return "СБОРКА", evidence
        evidence.append(f"не существует нигде: {', '.join(missing[:3])}")
        return "НЕНАЙДЕННЫЙ", evidence

    # 4. объект живёт в Mathlib, а поставщика у шага нет
    area_hit = [k for k in AREAS if k.lower() in (req or "").lower()]
    if (ml_hit or area_hit) and not sup:
        if ml_hit:
            evidence.append("в Mathlib: " + ", ".join(f"{n} → {ml_where[n]}" for n in ml_hit[:3]))
        if area_hit:
            evidence.append(f"область: {', '.join(AREAS[k] for k in area_hit[:2])}")
        return "ПОТЕРЯННОЕ ИМЯ", evidence

    # 5. GAP без поставщика при существующих объектах: объекты ОПРЕДЕЛЕНЫ,
    #    но утверждение о них не доказано. Это не переходник — нужна теорема.
    if status == "GAP" and not sup:
        evidence.append(f"объекты определены ({len(ours_hit)+len(ml_hit)}), поставщика нет — "
                        f"утверждение о них не доказано")
        return "НУЖНА ТЕОРЕМА", evidence

    # 6. MISMATCH = обе стороны существуют, разошлись формулировки
    if status == "MISMATCH":
        evidence.append(f"статус MISMATCH: обе стороны есть ({len(ours_hit)} наших, {len(ml_hit)} Mathlib)")
        return "ПЕРЕХОДНИК", evidence

    # 7. все объекты наши и существуют — свинтить готовое
    if ours_hit and not ml_hit:
        evidence.append(f"наши объекты существуют: {', '.join(ours_hit[:3])}")
        return "ПЕРЕХОДНИК", evidence

    evidence.append(f"наши: {len(ours_hit)}, mathlib: {len(ml_hit)}")
    return "ПЕРЕНОС МАШИНЫ", evidence


def declarations(relpath, limit=40):
    """ВСЕ объявления файла. Поиск по имени промахивается: posDef_one vs PosDef.one."""
    p = MLIB / relpath
    if not p.exists():
        return [f"(файл не найден: {relpath})"]
    out = [f"  {relpath}:{i}  {ln.strip()[:88]}"
           for i, ln in enumerate(p.read_text(errors="replace").split("\n"), 1)
           if re.match(r"^\s*(protected\s+|private\s+|noncomputable\s+)*"
                       r"(theorem|lemma|def|abbrev)\s+", ln)]
    return out[:limit] or [f"(объявлений нет в {relpath})"]


def chain_gap_report(con):
    """Фаза 0 леджера разрывов: k-метрика по цепям.

    k = число шагов цепи без подтверждённого поставщика. Цепь с k=1 — золото:
    один шаг до замыкания. Сортировка по k восходяще — это и есть жёсткий срез
    вариантов: сперва туда, где замыкание ближе всего.
    """
    print("=" * 78 + "\nРАЗРЫВЫ ПО ЦЕПЯМ (k = шагов до замыкания)\n" + "=" * 78)
    rows = list(con.execute(
        """select chain,
                  sum(case when status in ('READY','VALIDATION') then 1 else 0 end),
                  sum(case when status not in ('READY','VALIDATION') then 1 else 0 end),
                  count(*)
             from assembly group by chain
             order by sum(case when status!='READY' then 1 else 0 end)"""))
    for chain, ready, k, total in rows:
        marker = "◉ ЗОЛОТО" if k == 1 else ("◎" if k <= 3 else " ")
        print(f"  {marker:9s} k={k:<3d} {chain}  ({ready}/{total} готово)")
    print()


def gap_candidates(con, requirement, objects, limit=4):
    """Фаза 1: слабые рёбра-кандидаты для одного разрыва.

    Текстовое совпадение capability.provides с требованием шага. СЛАБОЕ ребро:
    только кандидат, НЕ замыкание. Сильным ребро делает supplier_preflight /
    fit.py (типовая стыковка в Lean) — совпадение по слову не есть совпадение
    по смыслу, и scope-теги обязаны сходиться (ABSTRACT не закрывает
    COFINAL_FAMILY). Контрпримеры имеют вето.
    """
    words = [w for w in re.findall(r"[A-Za-zА-Яа-я_]{5,}", f"{requirement} {objects or ''}")
             if w.lower() not in ("требуется", "конкретный", "существует")][:6]
    if not words:
        return []
    cond = " OR ".join("lower(provides) LIKE ?" for _ in words)
    params = [f"%{w.lower()}%" for w in words]
    seen, out = set(), []
    for thm, f, prov in con.execute(
            f"select theorem, file, provides from capability where {cond} limit 12", params):
        if thm in seen or thm.endswith(".md"):
            continue
        seen.add(thm)
        score = sum(1 for w in words if w.lower() in (prov or "").lower())
        out.append((score, thm, f, prov))
    out.sort(reverse=True)
    return out[:limit]


def main():
    ours, mathlib, closed = load_context()
    print(f"[контекст] наших объектов {len(ours)} · атомов Mathlib {len(mathlib)} · "
          f"имён в закрытых шагах {len(closed)}\n", flush=True)

    con = sqlite3.connect(DB, uri=True)
    chain_gap_report(con)
    rows = list(con.execute("""select chain, step, requirement, supplied_by,
                               supplier_file, note, status, objects
                               from assembly where status != 'READY' order by chain, step"""))
    tot, marked = con.execute(
        "select count(*), count(objects) from assembly").fetchone()
    candidates = {(r[0], r[1]): gap_candidates(con, r[2], r[7]) for r in rows}
    con.close()
    pct = marked * 100 // tot if tot else 0
    print(f"[покрытие] objects заполнены у {marked}/{tot} шагов ({pct}%)", flush=True)
    if pct < 100:
        print("           непокрытые получают породу НЕ РАЗМЕЧЕН — правило внесения "
              "требует заполнять objects, включая НЕсуществующие объекты\n", flush=True)

    graded = []
    for i, r in enumerate(rows, 1):
        b, why = classify(r, ours, mathlib, closed)
        graded.append((COST[b], b, why, r))
        print(f"[{i}/{len(rows)}] {i*100//len(rows)}% | {b:18s} {r[0][:12]}:{r[1]}", flush=True)

    graded.sort(key=lambda t: (t[0], t[3][0], t[3][1]))
    print("\n" + "=" * 78 + "\nОЧЕРЕДЬ ПО ЦЕНЕ\n" + "=" * 78)
    for b, n in collections.Counter(g[1] for g in graded).most_common():
        print(f"  {b:18s} {n}")

    for cost, b, why, r in graded:
        chain, step, req, sup, sfile, note, status, objects = r
        print(f"\n{'─'*78}\n[{b}]  {chain}:{step}   ({status})\n  {req}")
        for w in why:
            print(f"  ▸ {w}")
        cands = candidates.get((chain, step)) or []
        if cands:
            print("  слабые рёбра-кандидаты (текст, НЕ замыкание — сильным делает fit.py):")
            for score, thm, f, prov in cands:
                print(f"    [{score}] {thm}  {f}")
                print(f"        -> {(prov or '')[:100]}")
        if b == "ПОТЕРЯННОЕ ИМЯ":
            for k in [k for k in AREAS if k.lower() in (req or "").lower()][:2]:
                print(f"\n  ── ВСЕ объявления {AREAS[k]} ──")
                for d in declarations(AREAS[k]):
                    print(d)
            print("\n  ⚠ ОТСЕВ: совпадение по СЛОВУ != совпадение по СМЫСЛУ.")
            print("    genEigenspace = жордановы цепочки (f−μ)^k, НЕ пучок (K,G).")
            print("    Определение кандидата читает человек.")
        if cost <= 2:
            print("  ⚠ Кандидат закрывает шаг ТОЛЬКО после прогона Lean.")


if __name__ == "__main__":
    main()
