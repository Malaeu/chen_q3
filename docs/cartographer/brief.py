#!/usr/bin/env python3
"""brief.py — собрать source-locked пакет из базы для Прошки/Codex.

Отличие от их proshka-brief: тот собирает ЧТО ИЗМЕНИЛОСЬ (коммиты, диффы),
этот — ЧТО СУЩЕСТВУЕТ И НА ЧЁМ СТОИТ (граф состояния из assembly/atom).
Обе штуки нужны, друг друга не заменяют.

  python3 brief.py                      # все цепочки
  python3 brief.py GOAL057              # одна цепочка по префиксу
  python3 brief.py GOAL057 --out /tmp/b.md
"""
import sqlite3, sys, pathlib, datetime, subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
DB = f"file:{ROOT}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"

COST = {"ПОТЕРЯННОЕ ИМЯ": 1, "СВОЙ ФАКТ": 2, "ПЕРЕХОДНИК": 3, "СБОРКА": 4,
        "НУЖНА ТЕОРЕМА": 5, "ПОДЪЁМ ИЗМЕРЕНИЯ": 5, "НЕНАЙДЕННЫЙ": 6}


def head():
    try:
        h = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                           capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        h = "?"
    return h


def main():
    argv = sys.argv[1:]
    out = None
    if "--out" in argv:
        i = argv.index("--out")
        out = pathlib.Path(argv[i + 1])
        argv = argv[:i] + argv[i + 2:]          # выкинуть и флаг, и его значение
    args = [a for a in argv if not a.startswith("--")]
    prefix = args[0] if args else ""

    con = sqlite3.connect(DB, uri=True)
    L = []
    A = L.append

    A("# Состояние графа Q3 — пакет из базы\n")
    A("```yaml")
    A(f"SOURCE: q3.lean.aristotle/aristotle_db/knowledge.db")
    A(f"HEAD: {head()}")
    A(f"GENERATOR: codex_specs/cartographer/brief.py")
    A("ROUTE: CHALLENGER_NOT_RH")
    A("RH_CLAIM: NOT_MADE")
    A("```\n")
    A("Пакет описывает **состояние графа**, не изменения. Каждая строка несёт "
      "`file:line`, проверяемый чтением.\n")

    chains = [r[0] for r in con.execute(
        "select distinct chain from assembly where chain like ? order by chain",
        (f"{prefix}%",))]
    if not chains:
        print(f"нет цепочек с префиксом {prefix!r}", file=sys.stderr)
        return

    A("## Сводка\n")
    A("| цепочка | шагов | READY | незакрыто |")
    A("|---|---|---|---|")
    for ch in chains:
        t, r = con.execute(
            "select count(*), sum(status='READY') from assembly where chain=?", (ch,)).fetchone()
        A(f"| `{ch}` | {t} | {r} | {t - r} |")
    A("")

    for ch in chains:
        A(f"\n## {ch}\n")
        rows = list(con.execute("""select step, requirement, supplied_by, supplier_file,
                                   supplier_line, status, note, objects, required_by
                                   from assembly where chain=? order by step""", (ch,)))
        A("### Закрытые\n")
        for st, req, sup, sf, sl, status, note, objs, rb in rows:
            if status != "READY":
                continue
            loc = f" — `{sf}:{sl}`" if sf and sl else (f" — `{sf}`" if sf else "")
            A(f"- **{st}** {req} · `{sup or '—'}`{loc}")
        A("\n### Незакрытые\n")
        for st, req, sup, sf, sl, status, note, objs, rb in rows:
            if status == "READY":
                continue
            A(f"\n**{st}. {req}**  `{status}`\n")
            if rb:
                A(f"- требуется для: `{rb}`")
            if sup:
                loc = f" (`{sf}:{sl}`)" if sf and sl else ""
                A(f"- поставщик: `{sup}`{loc}")
            else:
                A(f"- поставщика нет")
            if objs:
                A(f"- объекты: {', '.join('`'+o.strip()+'`' for o in objs.split(',') if o.strip())}")
            if note:
                # только последний блок note — он самый свежий
                last = note.split(" | ")[-1].strip()
                A(f"- {last}")

    A("\n## Несущие атомы\n")
    A("Внешние леммы, на которых стоит больше всего файлов RouteB.\n")
    A("| атом | род | файлов |")
    A("|---|---|---|")
    for n, k, c in con.execute("""select name, kind, n_files from atom
        where kind in ('NONVANISHING','TOPOLOGY','LINALG','ANALYSIS')
        order by n_files desc limit 12"""):
        A(f"| `{n}` | {k} | {c} |")

    A("\n## Как проверить\n")
    A("```bash")
    A('DB="file:q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"')
    A('sqlite3 -header -column "$DB" "select step,status,requirement from assembly '
      f"where chain='{chains[0]}' order by step;\"")
    A("```")

    text = "\n".join(L)
    if out:
        out.write_text(text)
        print(f"записано: {out}  ({len(text)} символов, {len(L)} строк)")
    else:
        print(text)
    con.close()


if __name__ == "__main__":
    main()
