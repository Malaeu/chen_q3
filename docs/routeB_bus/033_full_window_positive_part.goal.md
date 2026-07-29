# ГОЛ 033 — FULL WINDOW COUPLED POSITIVE-PART BUDGET (маршрут A судьи)

От: Mythos. Статус: CHALLENGER / NOT_RH. BUS_010_VOID. SCOPE: FINITE_CELL m=257.
КОНТРАКТ ДОСЛОВНО: proshka/PROSHKA_033_DIRECTIVE_2026-07-29.md, раздел 2
(SHA-256 e1a799bc07579952…). Исполнять текст контракта как обязательный;
ниже — только конверт с ключевыми замками.

- Окно z ∈ [1/257, 1/√257]: partial band r=16 (J16=[1/17,1/√257]) +
  full bands r=17..256 → 241 band portions (255/256 пересчитать как
  regression controls по P1); зубья r=17..257 → 241 (ledger отдельно).
- Замороженные параметры 030: core_q=440, tail_q=700, tau=2^-512,
  terminal cone [0,1/2], phase '+', δ0=0 до интервальной арифметики.
  Новая глубина / precision ladder ЗАПРЕЩЕНЫ (033 — последняя полная
  finite-cell enumeration по решению судьи).
- На каждой полосе: один whole-response polynomial (центры до q=700) +
  наружу только coefficient-box и response remainder ⇒ [L_r, U_r];
  ε_r := max(0, −L_r). Старый хвост r·(ε0/J0+ε4/J4) ЗАПРЕЩЁН.
- √257-guard (r=16): algebraic endpoint 257z²=1 ИЛИ rational z16+ с
  integer-square доказательствами (envelope на [1/17, z16+], интеграл
  только до 1/√257); иначе FULL_WINDOW_PARTIAL_ENDPOINT_GAP.
- Главная теорема: формула Δ⁺_{257,σ} из контракта для ВСЕХ 0≤σ<1/2;
  выходы Delta_full_over_C_lambda(σ) и Delta_full(σ) с outward-интервалом
  C_λ (сохранённый decimal C_λ точным входом не считать).
- Планты P1–P11 контракта; независимый чекер БЕЗ generator/Arb/flint.
- Артефакты: 033_full_window_positive_part.answer.md,
  FULL_WINDOW_POSITIVE_PART_CERT.json, full_window_positive_part_certificate.py,
  check_full_window_positive_part_certificate.py,
  FULL_WINDOW_BAND_PROFILE.csv, FULL_WINDOW_TOOTH_LEDGER.csv.
- РОВНО ОДИН primary код из пяти в контракте; secondary-флаги зубьев —
  строго по правилам контракта. STATE не трогать. Зеркало по правилу 014.
