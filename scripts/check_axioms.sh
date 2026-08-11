#!/usr/bin/env bash
# check_axioms.sh — воспроизводимая запись о том, на чём стоит наш Lean.
#
# Манифест `docs/cartographer/TOOLS.yaml` ссылается на этот скрипт дважды (coverage
# семейства `proof_and_source` и alternatives инструмента `lean-validation`), а файла не
# было: реестр обещал инструмент, которого нет. Дефект закрыт созданием обещанного.
#
# Приём взят у формализации Anthropic (`zeta-23-lean/AUDIT.md`, Apache 2.0 — заимствована
# идея, не код): аудит должен печатать числа, которые читатель может перепроверить сам, а
# не утверждения о качестве. Три числа:
#
#   sorry вне комментариев      — сколько недоказанного и где именно
#   axiom-объявления            — на что мы опираемся сверх Lean
#   #print axioms <теорема>     — на чём реально стоит конкретное утверждение
#
# Третье — единственное, что отвечает на вопрос «доказано ли заявленное»: список аксиом
# берётся из самого ядра, а не из наших слов о нём. Эталон — стандартная тройка
# `[propext, Classical.choice, Quot.sound]`; всё сверх неё перечисляется поимённо.
#
# Строго read-only: ничего не пишет в репозиторий. `--print-axioms <имя>` вызывает
# `lake env lean` на временном файле в каталоге вне дерева.
#
# Коды возврата:
#   0 — отчёт напечатан
#   2 — не найден Lean-проект или окружение

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="$REPO/q3.lean.aristotle"
SCOPE="${SCOPE:-Q3}"

cd "$REPO" || exit 2
[ -d "$LEAN_ROOT/$SCOPE" ] || { echo "нет каталога $LEAN_ROOT/$SCOPE"; exit 2; }

hr() { printf '%s\n' "────────────────────────────────────────────────────────────────"; }

# ── что именно считаем ────────────────────────────────────────────────────────
# rg -c печатает «файл:число» и возвращает 1, когда совпадений нет — поэтому
# суммируем через awk и не полагаемся на код возврата (грабли из session_start.sh).
# Поиск ведётся ИЗ каталога Lean-проекта: glob `$SCOPE/**` сопоставляется с путями
# относительно рабочего каталога rg, а не относительно переданного корня. Первая версия
# искала из REPO и печатала нули там, где есть 35 sorry — врущий инструмент, пойман сразу.
count_in() {
  ( cd "$LEAN_ROOT" && rg -c "$1" --glob "$SCOPE/**/*.lean" . 2>/dev/null ) \
    | awk -F: '{s+=$NF} END {print s+0}'
}
list_in() {
  ( cd "$LEAN_ROOT" && rg -c "$1" --glob "$SCOPE/**/*.lean" . 2>/dev/null ) | sort -t: -k2 -rn
}

hr
echo "LEAN — НА ЧЁМ СТОИМ"
echo "  repo      : $REPO"
echo "  lean root : q3.lean.aristotle/$SCOPE"
echo "  toolchain : $(cat "$LEAN_ROOT/lean-toolchain" 2>/dev/null || echo '?')"
echo "  HEAD      : $(git -C "$REPO" log -1 --format='%h %ad' --date=short 2>/dev/null)"
echo "  файлов    : $(find "$LEAN_ROOT/$SCOPE" -name '*.lean' | wc -l)"

hr
echo "SORRY"
n_sorry="$(count_in 'sorry')"
echo "  вхождений всего: $n_sorry"
if [ "$n_sorry" -gt 0 ]; then
  echo "  по файлам (топ-10):"
  list_in 'sorry' | head -10 \
    | while IFS=: read -r f n; do printf '    %-58s %s\n' "${f#./}" "$n"; done
fi
echo "  ЗАМЕЧАНИЕ: счёт текстовый — включает вхождения в комментариях и строках."
echo "  Точный ответ даёт только сборка: предупреждения 'declaration uses sorry'."

hr
echo "AXIOM"
n_axiom="$(count_in '^axiom |^\s+axiom ')"
echo "  объявлений: $n_axiom"
if [ "$n_axiom" -gt 0 ]; then
  echo "  где (топ-10 файлов):"
  list_in '^axiom |^\s+axiom ' | head -10 \
    | while IFS=: read -r f n; do printf '    %-58s %s\n' "${f#./}" "$n"; done
fi

hr
echo "ЧТО ЭТОТ ОТЧЁТ НЕ ГОВОРИТ"
cat <<'TXT'
  Числа выше — текстовые, они не проходят через ядро Lean. Утверждение «теорема
  доказана и опирается только на стандартную тройку» даёт ТОЛЬКО ядро:

      ./scripts/check_axioms.sh --print-axioms <полное.имя.теоремы>

  Пока такой прогон не сделан, «у нас 0 sorry» — это утверждение о тексте, а не о
  доказательстве.
TXT

# ── ядро: #print axioms для конкретного имени ────────────────────────────────
if [ "${1:-}" = "--print-axioms" ] && [ -n "${2:-}" ]; then
  name="$2"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  hr
  echo "#print axioms $name"
  {
    echo "import Q3"
    echo "#print axioms $name"
  } > "$tmp/PrintAxioms.lean"
  ( cd "$LEAN_ROOT" && timeout 1800 lake env lean "$tmp/PrintAxioms.lean" 2>&1 ) \
    | sed 's/^/  /' | head -30
  echo
  echo "  Эталон: [propext, Classical.choice, Quot.sound]."
  echo "  Всё сверх — перечислено выше поимённо; sorryAx означает, что доказательства нет."
fi

hr
echo "Воспроизведение: ./scripts/check_axioms.sh [--print-axioms <имя>]"
echo "Приём заимствован у zeta-23-lean/AUDIT.md (идея, не код; Apache 2.0)."
exit 0
