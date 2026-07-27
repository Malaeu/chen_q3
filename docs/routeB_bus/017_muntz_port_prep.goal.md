# ГОЛ 017 — MUNTZ_PORT_PREP (подготовка порта + расширение зеркала)

От: Mythos. Статус: CHALLENGER / NOT_RH. BUS_010_VOID соблюдать.
Контекст: 015 дал карту NEEDS_RENAME для будущего порта облачного Мюнца.
Облако ещё дожимает мост — САМ ПОРТ НЕ ДЕЛАТЬ. Этот гол снимает два
известных трения заранее и расширяет зеркало.

## Задача

1. ENDPOINT-ЛЕММА (a.e.-мост Ioo↔Icc): в Q3/Proofs/RouteB/
   (файл EStarWindowedMellinCrosswalk.lean или новый маленький
   WindowEndpointBridge.lean) доказать: для локально интегрируемого
   f : ℝ → ℂ и 0 < A < B
     ∫ u in Icc A B, f u = ∫ u in Ioo A B, f u
   (две точки — мера нуль). Сформулировать так, чтобы применялось к
   windowedMellin против облачного Gwin.

2. MELLIN-ПОРЯДОК: лемма-равенство между двумя конвенциями:
     ∫ u in Ioi 0, k u * (u:ℂ)^(s-1)  =  mellin k s
   для k : ℝ → ℂ (Mathlib mellin использует smul; для ℂ это mul с другим
   порядком — mul_comm/smul_eq_mul). Одна лемма, имя по глоссарию.

3. ЗЕРКАЛО: расширить whitelist sync-скрипта до ВСЕХ Q3/Proofs/RouteB/*.lean
   (включая ProlateLayer.lean); пересобрать MANIFEST; commit+push
   (правило 014). Ничего вне docs/routeB_bus/ не трогать.

## Запреты
Облачный Мюнц-код в дерево НЕ переносить; никаких новых предположений;
0 sorry; аксиомы — тройка.

## Отчёт
017_muntz_port_prep.answer.md: имена лемм, файл, строки, build exit, axioms,
хэш зеркального коммита. Коды: MUNTZ_PORT_PREP_OK / PREP_BLOCKER(что).
STATE — последним шагом.
