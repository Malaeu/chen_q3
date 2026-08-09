#!/usr/bin/env python3
"""Property Descent: вытащить атомы (внешние Mathlib-леммы) из доказательств RouteB.

Атом = идентификатор, который вызывается в теле доказательства, но НЕ определён
внутри проекта. То есть внешнее свойство, на которое мы опираемся.
"""
import json, re, sys, collections, pathlib

ROOT = pathlib.Path("/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle")
INV = pathlib.Path("/Users/emalam/GitHub/codex_specs/cartographer/inventory_RouteB.json")
FILES = sorted((ROOT / "Q3/Proofs/RouteB").glob("*.lean"))

# свои объекты — из инвентаря картографа
own = set()
inv = json.loads(INV.read_text())
items = inv if isinstance(inv, list) else inv.get("objects", inv.get("items", []))
for o in items:
    n = o.get("name") if isinstance(o, dict) else None
    if n:
        own.add(n)
        own.add(n.split(".")[-1])
print(f"[инвентарь] своих объектов: {len(own)}", flush=True)

# идентификатор Lean: буквы/цифры/_/'/. — берём всё, потом фильтруем
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

# служебные слова Lean/тактики — не атомы
NOISE = set("""theorem lemma def abbrev structure instance example noncomputable private
protected open namespace end section variable universe import set_option attribute
by exact apply refine intro intros have show from fun let in with at using this
simp simpa rw rwa unfold change calc constructor rcases obtain cases induction
match do return if then else fun_prop norm_num omega ring linarith nlinarith
push_neg field_simp positivity decide native_decide trivial rfl sorry
Type Prop Sort ℂ ℝ ℤ ℕ Set Matrix Module Complex Real Finset Filter
forall exists and or not iff true false True False Or And Not Iff
deriving where mutual partial unsafe macro syntax notation infixl infixr prefix
all_goals any_goals first repeat try skip focus case next swap
gcongr bound aesop tauto exfalso absurd congr subst symm trans
""".split())

def body_of(text):
    """тела доказательств: всё после := by до конца блока (грубо, по отступам)"""
    out = []
    lines = text.split("\n")
    inproof = False
    for ln in lines:
        if re.search(r":=\s*by\s*$|:=\s*by\s", ln):
            inproof = True
            out.append(ln.split(":=", 1)[-1])
            continue
        if inproof:
            if ln.strip() == "" or (ln and not ln[0].isspace() and not ln.startswith("--")):
                if ln and not ln[0].isspace():
                    inproof = False
                    continue
            out.append(ln)
    return "\n".join(out)

atom_use = collections.defaultdict(set)   # атом -> {файлы}
total = len(FILES)
for i, f in enumerate(FILES, 1):
    if i % 20 == 0 or i == total:
        print(f"[{i}/{total}] {i*100//total}% | {f.name}", flush=True)
    txt = f.read_text(errors="replace")
    body = body_of(txt)
    for m in IDENT.finditer(body):
        name = m.group(0)
        short = name.split(".")[-1]
        if name in NOISE or short in NOISE:
            continue
        if name in own or short in own:
            continue
        if len(name) < 4 or name[0].isupper() and "." not in name and short in NOISE:
            continue
        # отсекаем локальные гипотезы h..., односимвольные, числа
        if re.fullmatch(r"h[A-Za-z0-9_']{0,12}", name):
            continue
        if "." not in name and "_" not in name:
            continue
        atom_use[name].add(f.name)

print(f"\n[итог] уникальных внешних атомов: {len(atom_use)}", flush=True)
rows = sorted(atom_use.items(), key=lambda kv: -len(kv[1]))
out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "atoms.json")
out.write_text(json.dumps(
    [{"atom": a, "n_files": len(fs), "files": sorted(fs)} for a, fs in rows],
    ensure_ascii=False, indent=1))
print(f"[записано] {out}", flush=True)
print("\n=== ТОП-40 самых нагруженных атомов ===", flush=True)
for a, fs in rows[:40]:
    print(f"{len(fs):4d}  {a}", flush=True)
