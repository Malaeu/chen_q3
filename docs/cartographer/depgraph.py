#!/usr/bin/env python3
"""depgraph — настоящий граф зависимостей живого дерева, из исходников.

Зачем: каталог `capability` несёт requires/provides ПРОЗОЙ (замер 2026-08-20:
477 из 478 requires и 1165 из 1172 provides — человеческий текст, пересечение
токенов НОЛЬ). Ходить по нему нельзя. Граф в `aristotle_proofs.db` тоньше:
308 внутренних рёбер на 3757 лемм.

Что делает: читает .lean живого фронта, собирает объявления и их тела, и
строит рёбра «объявление A упоминает объявление B в своём теле». Это не
пересказ и не аннотация — это то, что написано в источнике.

Что считает поверх графа:
  КОНУС КРЫШИ   что реально нужно `rh_of_canonical_strip_slots` (обратный обход)
  ГЛУБИНА       длина самой длинной цепи внутри конуса
  РАЗРЕЗЫ       точки сочленения конуса: узлы, чьё удаление рвёт связь с крышей.
                Это ОПОРЫ, вычисленные из ядра, а не объявленные нами
  СИРОТЫ        доказанное, до чего крыше нет дела

Ограничения, названные прямо:
  * рёбра лексические: имя в теле = ребро. Совпадение имён с Mathlib или
    упоминание в комментарии дадут ложное ребро. Имена нашего дерева длинные
    и различимые, поэтому шум мал, но он НЕ НОЛЬ.
  * граф описывает ПОСТРОЕННОЕ, а не возможное. Он отвечает на вопрос
    «на чём стоит крыша», а не «каким путём дойти до недоказанного».
    Планирования вперёд здесь нет и быть не может: модели действий у нас нет.
  * `sorry`-ные и незакрытые узлы в граф входят как обычные.

Запуск:  python3 depgraph.py [--root PATH] [--target ИМЯ] [--json OUT]
Ничего не пишет в репозиторий без --json.
"""
import argparse
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO / "q3.lean.aristotle" / "Q3" / "Proofs"
DEFAULT_TARGET = "rh_of_canonical_strip_slots"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|structure|abbrev|instance)\s+([A-Za-z_][A-Za-z_0-9'\.]*)",
    re.M)
COMMENT_LINE = re.compile(r"--.*$", re.M)
COMMENT_BLOCK = re.compile(r"/-.*?-/", re.S)


def strip_comments(text: str) -> str:
    """Комментарии выкидываем: упоминание имени в доке — не зависимость."""
    text = COMMENT_BLOCK.sub(" ", text)
    return COMMENT_LINE.sub(" ", text)


def collect(root: Path):
    """Возвращает (decls, bodies): имя -> (файл, строка), имя -> текст тела."""
    decls, bodies = {}, {}
    for path in sorted(root.rglob("*.lean")):
        if "PrimeCert" in str(path):        # январский музей, read-only
            continue
        raw = path.read_text(encoding="utf-8", errors="replace")
        clean = strip_comments(raw)
        marks = [(m.start(), m.group(2)) for m in DECL.finditer(clean)]
        for i, (pos, name) in enumerate(marks):
            end = marks[i + 1][0] if i + 1 < len(marks) else len(clean)
            line = raw.count("\n", 0, pos) + 1
            decls[name] = (str(path.relative_to(REPO)), line)
            bodies[name] = clean[pos:end]
    return decls, bodies


IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9'.]*")


def build_edges(decls, bodies, min_name=4):
    """Ребро A -> B: тело A упоминает B. Своё имя не считаем.

    `min_name` отсекает короткие имена (`C`, `w`, `hm`). Первый прогон
    2026-08-20 без этого фильтра поставил `C` и `w` в верх списка разрезов:
    однобуквенное объявление ловится в каждом теле, где есть такая локальная
    переменная. Это ложные рёбра, и они забивают сигнал.

    Токенизируем тело и пересекаем с множеством имён — линейно по тексту.
    Альтернатива через одну большую регулярку квадратична и на нашем дереве
    не заканчивается (проверено 2026-08-20).

    Имена с точками (`Foo.bar`) ловим и целиком, и по последнему сегменту:
    в теле оно может стоять как `Foo.bar`, так и просто `bar` внутри
    namespace.
    """
    names = {n for n in decls if len(n.rsplit(".", 1)[-1]) >= min_name}
    tail = defaultdict(set)          # последний сегмент -> полные имена
    for n in names:
        if "." in n:
            tail[n.rsplit(".", 1)[1]].add(n)

    uses = defaultdict(set)
    for name, body in bodies.items():
        found = set()
        for tok in IDENT.findall(body):
            if tok in names:
                found.add(tok)
            elif tok in tail and len(tail[tok]) == 1:
                found |= tail[tok]          # однозначный хвост — берём
        found.discard(name)
        if found:
            uses[name] = found
    return uses


def cone(target, uses):
    """Обратный обход: всё, на что опирается target, транзитивно."""
    seen, order = set(), []
    dq = deque([target])
    while dq:
        cur = dq.popleft()
        if cur in seen:
            continue
        seen.add(cur)
        order.append(cur)
        for d in sorted(uses.get(cur, ())):
            if d not in seen:
                dq.append(d)
    return seen, order


def depth(target, uses, inside):
    """Длина самой длинной цепи от target вниз (мемоизация, защита от циклов)."""
    memo, stack = {}, set()

    def go(n):
        if n in memo:
            return memo[n]
        if n in stack:                       # цикл — не углубляемся
            return 0
        stack.add(n)
        kids = [d for d in uses.get(n, ()) if d in inside]
        memo[n] = 1 + max((go(k) for k in kids), default=0)
        stack.discard(n)
        return memo[n]

    return go(target), memo


def cut_vertices(target, uses, inside):
    """Узлы, без которых часть конуса теряет связь с крышей.

    Прямой способ, дорогой но честный: убираем узел, пересчитываем конус,
    смотрим кто отвалился. |inside| у нас невелик, так что это допустимо.
    """
    base, _ = cone(target, uses)
    out = []
    for node in sorted(inside):
        if node == target:
            continue
        pruned = {k: {d for d in v if d != node} for k, v in uses.items()}
        pruned.pop(node, None)
        after, _ = cone(target, pruned)
        lost = base - after - {node}
        if lost:
            out.append((node, len(lost)))
    out.sort(key=lambda t: -t[1])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(LEAN_DIR))
    ap.add_argument("--target", default=DEFAULT_TARGET)
    ap.add_argument("--json", default=None)
    ap.add_argument("--cuts", type=int, default=15, help="сколько разрезов печатать")
    ap.add_argument("--min-name", type=int, default=4,
                    help="минимальная длина имени; короткие дают ложные рёбра")
    a = ap.parse_args()

    root = Path(a.root)
    if not root.exists():
        sys.exit(f"нет каталога: {root}")

    decls, bodies = collect(root)
    uses = build_edges(decls, bodies, min_name=a.min_name)
    edges = sum(len(v) for v in uses.values())

    print(f"объявлений в дереве:  {len(decls)}  (имена короче {a.min_name} как ЦЕЛИ рёбер отброшены)")
    print(f"рёбер (A упоминает B): {edges}")
    print(f"узлов с исходящими:    {len(uses)}")

    if a.target not in decls:
        sys.exit(f"\nцель '{a.target}' в дереве не найдена")

    inside, _ = cone(a.target, uses)
    print(f"\nКОНУС КРЫШИ '{a.target}'")
    f, l = decls[a.target]
    print(f"  объявлена: {f}:{l}")
    print(f"  опирается на: {len(inside) - 1} объявлений (транзитивно)")

    d, memo = depth(a.target, uses, inside)
    print(f"  глубина самой длинной цепи: {d}")

    orphans = set(decls) - inside
    print(f"\nСИРОТЫ (доказано, но крыше не нужно): {len(orphans)}")

    cuts = cut_vertices(a.target, uses, inside)
    print(f"\nРАЗРЕЗЫ — узлы, чьё удаление отрывает часть конуса ({len(cuts)}):")
    for name, lost in cuts[:a.cuts]:
        f, l = decls[name]
        print(f"  {lost:5d} потеряно · {name}")
        print(f"          {f}:{l}")
    if len(cuts) > a.cuts:
        print(f"  … и ещё {len(cuts) - a.cuts}")

    if a.json:
        Path(a.json).write_text(json.dumps({
            "target": a.target,
            "declarations": len(decls),
            "edges": edges,
            "cone_size": len(inside) - 1,
            "depth": d,
            "orphans": len(orphans),
            "cuts": [{"name": n, "lost": c, "file": decls[n][0],
                      "line": decls[n][1]} for n, c in cuts],
        }, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\nJSON: {a.json}")


if __name__ == "__main__":
    main()
