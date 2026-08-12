#!/usr/bin/env python3
"""Обогатить атомы описаниями: что каждый атом ЕСТЬ, а не только как он называется.

Шаг 1 конструктора (замысел владельца 2026-08-11): «декомпозировать Lean полностью до
атомов с описанием, что этот атом из себя представляет — с полным описанием».

Без описания атом — это строка. Строку нельзя ни сопоставить с чужой леммой, ни отдать
агенту как задание: `mul_nonneg` и `posIndexAbove` выглядят одинаково безлико. С сигнатурой
и докстрингом атом становится утверждением, о котором можно рассуждать.

Источники, в порядке приоритета:

  1. Mathlib на диске   `q3.lean.aristotle/.lake/packages/mathlib/Mathlib` (100 МБ)
  2. наше дерево        `q3.lean.aristotle/Q3` — для атомов, которые на деле наши
  3. чужое дерево       `--foreign` — их декларации, если атом определён у них

Для каждого атома извлекается: где объявлен (`file:line`), вид (`theorem`/`def`/…),
сигнатура до `:=`, докстринг `/-- … -/` над объявлением, и число мест употребления у нас.

Атомы, которые нигде не нашлись, помечаются `UNRESOLVED` — это либо тактики, либо
нотация, либо имя, разобранное неверно. Их список — самостоятельный результат: он
показывает, где наш разбор до атомов ещё дырявый.

ЧТО ЭТО НЕ ДЕЛАЕТ. Не решает, применим ли атом: докстринг — это пересказ автора, а не
проверка. Правило про суррогат по форме действует.

Read-only: пишет только в `--json`, если указан.
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DB = f"file:{REPO}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"
MATHLIB = REPO / "q3.lean.aristotle/.lake/packages/mathlib/Mathlib"
OURS = REPO / "q3.lean.aristotle/Q3"

KINDS = "theorem|lemma|def|structure|abbrev|instance|class|inductive"


def namespace_at(lines: list[str], line: int) -> str:
    """Восстановить namespace-стек над строкой: `namespace A` … `end A`, плюс `open`-независимо."""
    stack = []
    for k in range(line - 1):
        s = lines[k].strip()
        m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m:
            stack.extend(m.group(1).split("."))
            continue
        m = re.match(r"^end\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m and stack:
            for part in reversed(m.group(1).split(".")):
                if stack and stack[-1] == part:
                    stack.pop()
    return ".".join(stack)


def find_structure_field(name: str, root: Path) -> dict | None:
    """Найти имя как ПОЛЕ СТРУКТУРЫ: строка `  name : тип` внутри `structure X where`.

    ДЕФЕКТ, ПОЙМАННЫЙ 2026-08-12: `kTrial` — поле `CoefficientFamily`
    (`D0CanonicalApproximation.lean:35`), а поиск объявлений ищет только
    `theorem|def|…`. Инструмент объявлял существующий объект `PLACEHOLDER`, то есть
    «ещё не написан». Это ровно та ложь, ради которой введена классификация.
    """
    if not root.is_dir() or "." in name:
        return None
    try:
        r = subprocess.run(
            ["rg", "-n", "--no-heading", rf"^\s+{re.escape(name)}\s*:", str(root)],
            capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None
    for c in r.stdout.strip().split("\n")[:200]:
        try:
            path_s, line_s, body = c.split(":", 2)
            cp, cl = Path(path_s), int(line_s)
            lines = cp.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        # подняться вверх до `structure X where` без пустой строки-разрыва
        owner = None
        for k in range(cl - 2, max(-1, cl - 40), -1):
            t = lines[k].strip()
            m = re.match(r"^(structure|class)\s+([A-Za-z_][A-Za-z_0-9'\.]*)", t)
            if m:
                owner = m.group(2)
                break
            if t and not t.startswith("--") and not t.startswith("/") and ":" not in t \
               and not t.endswith("where"):
                break
        if owner is None:
            continue
        ns = namespace_at(lines, cl)
        return {
            "kind_lean": "field",
            "namespace": ns,
            "owner": owner,
            "file": str(cp.relative_to(REPO)) if str(cp).startswith(str(REPO)) else str(cp),
            "line": cl,
            "signature": f"{owner}.{name} : " + body.split(":", 1)[1].strip()[:200],
            "docstring": "",
        }
    return None


def find_declaration(name: str, root: Path) -> dict | None:
    """Найти объявление ТОЧНО этого полного имени: базовое имя плюс совпадающий namespace.

    ПОПРАВКА 2026-08-11: первая версия искала по базовому имени с `-m 1` и брала первое
    попавшееся. Так `Real.pi` находился как `def pi` из `ContinuousMap` (произведение
    непрерывных отображений), а `Complex.exp` — как степенной ряд из `PowerSeries`.
    Инструмент, дающий правдоподобно неверный ответ, хуже отсутствующего: теперь для
    каждого кандидата восстанавливается namespace-стек и полное имя сверяется с искомым.
    """
    if not root.is_dir():
        return None
    base = name.split(".")[-1]
    want_ns = ".".join(name.split(".")[:-1])
    pat = rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})\s+{re.escape(base)}\b"
    try:
        r = subprocess.run(["rg", "-n", "--no-heading", pat, str(root)],
                           capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None

    cands = r.stdout.strip().split("\n")[:400]
    path = line = lines = None
    for c in cands:
        try:
            path_s, line_s, _ = c.split(":", 2)
            cp, cl = Path(path_s), int(line_s)
            cls = cp.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        ns = namespace_at(cls, cl)
        # объявление могло быть записано и полным именем: `theorem Real.pi ...`
        full_written = re.search(rf"({KINDS})\s+{re.escape(name)}\b", cls[cl - 1]) is not None
        if ns == want_ns or full_written or (not want_ns and not ns):
            path, line, lines = cp, cl, cls
            break
    if path is None:
        return None

    # сигнатура: от объявления до `:=` или `by`, максимум 25 строк
    sig, i = [], line - 1
    while i < min(line - 1 + 25, len(lines)):
        sig.append(lines[i].strip())
        if ":=" in lines[i] or re.search(r"\bby\b\s*$", lines[i]):
            break
        i += 1
    signature = " ".join(sig)
    cut = signature.find(":=")
    signature = (signature[:cut] if cut > 0 else signature).strip()

    # докстринг: блок /-- … -/ непосредственно над объявлением
    doc, j = [], line - 2
    if j >= 0 and lines[j].strip().endswith("-/"):
        while j >= 0:
            doc.insert(0, lines[j].strip())
            if lines[j].strip().startswith("/--"):
                break
            j -= 1
    docstring = " ".join(doc).replace("/--", "").replace("-/", "").strip()

    m = re.match(rf"\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})",
                 lines[line - 1])
    return {
        "kind_lean": m.group(1) if m else "?",
        "namespace": namespace_at(lines, line),
        "file": str(path.relative_to(REPO)) if str(path).startswith(str(REPO)) else str(path),
        "line": line,
        "signature": signature[:600],
        "docstring": docstring[:800],
    }


CYR = re.compile(r"[А-Яа-яЁё]")
PAPER = re.compile(r"(Lemma|Theorem|Prop|Proposition)[_ ]?\d", re.I)


def is_local_binder(name: str) -> bool:
    """Связана ли эта переменная в сигнатуре какой-либо декларации дерева RouteB.

    Ищем по всему дереву, а не в файле-поставщике: `epsilon` связан в сигнатуре
    ПОТРЕБИТЕЛЯ, тогда как поставщик у шага записан другой. Первая редакция проверяла
    только поставщика и пропустила ровно этот случай.

    Паттерн требует, чтобы имя стояло в скобочной группе биндеров и завершалось `:`.
    Ограничений по длине имени НЕТ: они были заплаткой, а не правилом, и делали
    поведение непредсказуемым на границе.
    """
    if "." in name:
        return False
    try:
        r = subprocess.run(
            ["rg", "-q", rf"[({{]\s*(\w+\s+)*{re.escape(name)}(\s+\w+)*\s*:",
             str(OURS / "Proofs/RouteB")],
            capture_output=True, timeout=60)
        return r.returncode == 0
    except Exception:
        return False


def provenance(name: str, resolved: dict | None) -> str:
    """Классифицировать имя по таксономии вердикта `..._HERMFACT1_AUDIT_2026-08-11`.

    ПОРЯДОК ПРОВЕРОК И ПОЧЕМУ ИМЕННО ТАКОЙ.

    1. Проза — кириллица или пробел: пометка в записи, а не имя объекта.
    2. **Объявлено в нашем RouteB — значит декларация, и точка.** Связанная переменная
       не имеет одноимённого `def`/`theorem`/поля в том же дереве; если бы имела, это
       затенение и отдельный дефект. Проверка стоит выше связанности намеренно.
    3. Связано в сигнатурах RouteB, но объявлено где-то ещё (Mathlib, чужой файл) —
       локальная гипотеза с однофамильцем. Так `epsilon` не уезжает в ординалы Веблена.
    4. Разрешилось вне RouteB и нигде не связано — декларация (например `dslope`).
    5. Похоже на ссылку из статьи — теорема первоисточника.
    6. Иначе заглушка.

    ДВЕ ПРЕЖНИЕ РЕДАКЦИИ БЫЛИ НЕВЕРНЫ, обе записаны в самопроверку.
    Первая ставила разрешение выше связанности и подпирала это порогами длины имени.
    Вторая ставила связанность выше всего — и `ccmModeFinite` стал «локальным», потому
    что биндер-паттерн не отличает связывание `(x : T)` от ПРИВЕДЕНИЯ ТИПА
    `(ccmModeFinite N i : ℝ)`. Regex их различить не может; различает происхождение.
    """
    if CYR.search(name) or " " in name:
        return "PROSE"
    if resolved and "Proofs/RouteB" in resolved.get("file", ""):
        return "LEAN_DECL"
    if is_local_binder(name):
        return "LOCAL_HYPOTHESIS"
    if resolved:
        return "LEAN_DECL"
    if PAPER.search(name):
        return "PAPER_THEOREM"
    return "PLACEHOLDER"


SELFTEST = [
    # имя,                                        ожидаемый класс,     почему
    ("epsilon",                    "LOCAL_HYPOTHESIS", "связан в сигнатурах, однофамилец в ординалах Веблена"),
    ("xi",                         "LOCAL_HYPOTHESIS", "связан в сигнатурах, однофамилец в RKHS_rescaling"),
    ("hbottom",                    "LOCAL_HYPOTHESIS", "связан, деклараций нет"),
    ("kTrial",                     "LEAN_DECL",        "ПОЛЕ структуры CoefficientFamily, не theorem/def"),
    ("proposition59RawTransform",  "LEAN_DECL",        "имя содержит 'proposition', но это декларация"),
    ("dslope",                     "LEAN_DECL",        "декларация Mathlib, нигде не связана"),
    ("ZerosRealOn",                "LEAN_DECL",        "наша декларация"),
    ("ccmModeFinite",              "LEAN_DECL",        "объявлена в RouteB; биндер-паттерн ловил ПРИВЕДЕНИЕ (ccmModeFinite N i : ℝ)"),
    ("sourceLagrangePolynomial",   "LEAN_DECL",        "объявлена в RouteB"),
    ("centeredPstarFamily",        "LEAN_DECL",        "объявлена в RouteB"),
    ("CCM_Lemma_7_3",              "PAPER_THEOREM",    "в дереве отсутствует, вид ссылки на статью"),
    ("hermfact1",                  "PLACEHOLDER",      "исторический doc-alias: ноль .lean во всём репозитории"),
    ("FiniteGroundTransformToCCMTrialLocallyUniform", "PLACEHOLDER", "ещё не написана"),
    ("кофинальное расписание",     "PROSE",            "пометка, не имя"),
]


def selftest(foreign: Path | None) -> int:
    """Прогнать классификатор на именах с ИЗВЕСТНЫМ ответом.

    Инструмент, который нельзя проверить, нельзя и починить: до этой проверки обе
    правки классификатора вносились вслепую и обе оказались с собственными ошибками.
    """
    print("САМОПРОВЕРКА классификатора — 11 имён с известным ответом")
    print()
    bad = 0
    for name, want, why in SELFTEST:
        found = None
        for root in (MATHLIB, OURS, foreign if foreign else Path("/nonexistent")):
            found = find_declaration(name, root) or find_structure_field(name, root)
            if found:
                break
        got = provenance(name, found)
        ok = got == want
        bad += not ok
        mark = "OK " if ok else "ПРОВАЛ"
        print(f"  {mark} {name[:46]:<46} {got:<17} {why}")
        if not ok:
            print(f"       ожидалось {want}"
                  + (f", адрес {found['file']}:{found['line']}" if found else ", адреса нет"))
    print()
    print(f"провалов: {bad} из {len(SELFTEST)}")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0, help="сколько атомов обработать (0 = все)")
    ap.add_argument("--kinds", default="",
                    help="только эти наши kind через запятую, напр. NONVANISHING,ANALYSIS,LINALG")
    ap.add_argument("--foreign", default="", help="корень чужого дерева, третий источник")
    ap.add_argument("--chain", default="",
                    help="разобрать объекты цепи из assembly, а не атомы Mathlib "
                         "(например REALZERO_GROUND_DIAGONAL_TO_XI)")
    ap.add_argument("--json", default="")
    ap.add_argument("--selftest", action="store_true",
                    help="прогнать классификатор на именах с известным ответом и выйти")
    args = ap.parse_args()

    if args.selftest:
        fr = Path(args.foreign).expanduser().resolve() if args.foreign else None
        return selftest(fr)

    con = sqlite3.connect(DB, uri=True)
    if args.chain:
        # Объекты маршрута — НЕ атомы Mathlib: это наши декларации и имена ещё не
        # написанных теорем. Разбор тот же (где объявлено, сигнатура, докстринг), но
        # `kind` здесь означает шаг цепи, а `n_files` теряет смысл и ставится в 0.
        rows = con.execute(
            "select step, objects, supplier_file from assembly where chain=? order by step",
            (args.chain,)).fetchall()
        seen, atoms = set(), []
        for step, objs, sup in rows:
            for o in (objs or "").split(","):
                o = o.strip()
                if not o or o in seen or "=" in o:
                    continue
                seen.add(o)
                atoms.append((o, f"шаг {step}", 0, sup))
        if not atoms:
            print(f"в цепи {args.chain} нет разбираемых имён", file=sys.stderr)
            return 2
    else:
        q = "select name, kind, n_files from atom"
        if args.kinds:
            ks = ",".join("'" + k.strip() + "'" for k in args.kinds.split(",") if k.strip())
            q += f" where kind in ({ks})"
        q += " order by n_files desc"
        if args.limit:
            q += f" limit {args.limit}"
        atoms = con.execute(q).fetchall()

    foreign = Path(args.foreign).expanduser().resolve() if args.foreign else None
    print(f"атомов к разбору: {len(atoms)}")
    print(f"источники: Mathlib {'есть' if MATHLIB.is_dir() else 'НЕТ'} · "
          f"наше дерево {'есть' if OURS.is_dir() else 'НЕТ'} · "
          f"чужое {'есть' if foreign and foreign.is_dir() else 'нет'}")
    print()

    out, stats = [], {"mathlib": 0, "ours": 0, "foreign": 0, "unresolved": 0}
    prov_stats = {}
    for idx, row in enumerate(atoms, 1):
        name, kind, n_files = row[0], row[1], row[2]
        supplier = row[3] if len(row) > 3 else None
        rec = {"name": name, "our_kind": kind, "our_n_files": n_files}
        found = None
        for src, root in (("mathlib", MATHLIB), ("ours", OURS),
                          ("foreign", foreign if foreign else Path("/nonexistent"))):
            d = find_declaration(name, root) or find_structure_field(name, root)
            if d:
                found = (src, d)
                break
        prov = provenance(name, found[1] if found else None)
        rec["provenance"] = prov
        prov_stats[prov] = prov_stats.get(prov, 0) + 1
        # Адрес выдаётся ТОЛЬКО для настоящих деклараций. Локальная гипотеза и проза
        # адреса не имеют: любой найденный для них file:line — ложный друг.
        if prov == "LEAN_DECL" and found:
            rec.update(found[1]); rec["source"] = found[0]; stats[found[0]] += 1
        else:
            rec["source"] = prov
            stats["unresolved"] += 1
            if found:
                rec["rejected_match"] = f"{found[1]['file']}:{found[1]['line']}"
        out.append(rec)
        if sys.stdout.isatty() and idx % 10 == 0:
            frac = idx / len(atoms)
            bar = "#" * int(30 * frac) + "." * (30 - int(30 * frac))
            sys.stdout.write(f"\r[{bar}] {100*frac:5.1f}%  {name[:34]:<34}")
            sys.stdout.flush()
    if sys.stdout.isatty():
        print()

    print()
    print(f"  найдено в Mathlib   : {stats['mathlib']}")
    print(f"  найдено у нас       : {stats['ours']}")
    print(f"  найдено в чужом     : {stats['foreign']}")
    print(f"  НЕ РАЗРЕШЕНО        : {stats['unresolved']}   ← дыры нашего разбора до атомов")
    if prov_stats:
        print()
        print("── провенанс (таксономия вердикта HERMFACT1_AUDIT) ──")
        for k in sorted(prov_stats):
            print(f"  {k:<18} {prov_stats[k]}")
        rej = [r for r in out if r.get("rejected_match")]
        if rej:
            print()
            print(f"  ОТВЕРГНУТО ложных совпадений: {len(rej)}")
            for r in rej[:6]:
                print(f"    {r['name']:<24} {r['provenance']:<18} было бы {r['rejected_match']}")
    print()

    with_doc = [r for r in out if r.get("docstring")]
    print(f"  с докстрингом       : {len(with_doc)} из {len(out)}")
    print()
    print("── примеры разобранных атомов ──")
    for r in with_doc[:5]:
        print(f"  {r['name']}  [{r['our_kind']} · {r['source']}]")
        print(f"    {r['file']}:{r['line']}")
        if r.get("signature"):
            print(f"    сигнатура: {r['signature'][:110]}")
        print(f"    описание : {r['docstring'][:110]}")
        print()

    if args.json:
        Path(args.json).write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"JSON: {args.json}")

    print("Докстринг — пересказ автора, не проверка применимости. Перед употреблением "
          "открыть file:line.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
