# REENTRY GATE A — TWO TRACK CONTRACTS (owner decision 2026-08-27)

Прекоммит по шаблону судьи; ремонта под результаты не будет.

```yaml
TRACK_ID: TRACK1_PRIME_KERNEL_POWER_SAVING_DIRECT
SOURCE_LOCKED_OBJECT: >-
  Stieltjes-остаток R_k точной оконной прайм-суммы
  2*sum_{n=2}^{m_k} (Lambda(n)/sqrt n) * C_n(S(D_k v), S(q_k))
  после вычета psi~x главного члена (отчёт 49c3b916 §4, blob 3d940d96);
  C_n из sourcePrimeContinuousSesquilinearForm
  (D0PstarPrimeAmbientSesquilinearForm.lean:150); ядро K_pair — модовые
  перекрытия пары.
EXACT_SCOPE: >-
  выбранное Ferrers-семейство, m_k = k+2, все фиксированные
  0 <= sigma < 1/2; произвольный единичный v в конечном носителе клетки.
EXACT_QUANTIFIERS: >-
  EXISTS sigma_0 > 0, C > 0: FORALL-eventually k на прекоммитном хвосте,
  FORALL единичный v: |R_k(v)| <= C * m_k^(-sigma_0) * sqrt(m_k) *
  polylog(m_k) — степенная экономия против чебышёвского конверта 4*sqrt(m).
NORMALIZATION: >-
  star-first скалярное произведение; L^(-1/2) в трансформе; веса
  2*Lambda(n)/sqrt(n); окно I_m с мерой d*u — всё с диска, без
  переопределений.
COFINAL_SCHEDULE: "m_k = k+2; хвост phi n = n + k0 (узел 3b0832ac); второй хвост запрещён"
PRESERVES: "знаковый W02+Arch-Prime; центр-якорь; beta-момент; все файрволы"
DROPS: "ничего"
OLD_FATAL_BYPASSED: >-
  никакой — дорожка поставляет отсутствующий supplier, поименованный в
  карантинном gap EXACT_SELECTED_PRIME_KERNEL_POWER_SAVING; консюмер не
  трогается.
WHY_THIS_IS_NOT_ANOTHER_WRAPPER: >-
  не переименовывает консюмер и не строит нового представления; впервые
  за фазу целью является сам недостающий аналитический вход как прямой
  prove/refute объект.
MINIMAL_THEOREM_FACING_OUTPUT: >-
  PAPER-неравенство с sigma_0 и полным прогоном экспонент — ЛИБО
  поименованное препятствие — ЛИБО минимальный леджер допущений с ценами.
DISCRIMINATOR:
  PASS: SELECTED_PRIME_KERNEL_POWER_SAVING_PAPER_PROVED
  FAIL: SELECTED_PRIME_KERNEL_POWER_SAVING_OBSTRUCTED_OR_CONDITIONAL
KILL_CONDITION: >-
  доказательство требует запрещённого входа (RH/эквиваленты, глобальная
  позитивность Вейля, искомая сходимость, сам rate) или любой post-hoc
  смены объекта/нормировки/schedule/retained subspace/compact class/verifier.
REOPEN_CONDITION: >-
  только PASS этого блока даёт замороженному коридору право на
  reentry-адъюдикацию.
LEAN_AUTHORIZED: false
NUMERICS_AUTHORIZED: false
EXPECTED_CLOSES:
  - EXACT_SELECTED_PRIME_KERNEL_POWER_SAVING (или его невозможность-как-сформулировано)
EXPECTED_OPENS: [] # в исходе (c) — только поимённые допущения леджера
KILL_POWER: 10/10
COST: 9/10
```

```yaml
TRACK_ID: TRACK2_ARISTOTLE_ASSET_BANKING
SOURCE_LOCKED_OBJECT: >-
  набор PAPER_PASS-тождеств, запинованных вердиктами:
  (a) граф-пакет: C = Q(K - eps I)Q + P положительно определён;
      d^(-1) xi - q = -C^(-1) r; тождество ошибки трансформы;
      скалярный перенос вещественных нулей [вердикты 4a576dd5, 1189f702];
  (b) P59-резольвента: (D - zeta(z) I) h(z) = c(z)*eta с
      zeta = -zL/(2pi), c = (sqrt L/pi) sin(zL/2); формула (M-a)kappa;
      целое продолжение через полюса [вердикт 1189f702 §2];
  (c) penalty-slack: конверт (I- и Gram-версии) + Schur-тождество
      s_min = r*(B - bI)^(-1) r [вердикт edfedd82];
  (d) порты: centering <= ||Xi(0)||/sqrt(c*) из якорного тождества;
      kernelL2 <= C_sigma * lambda^sigma * sqrt(L) общим числителем
      [вердикт 6a47f79c].
EXACT_SCOPE: >-
  конечно-клеточные тождества на литеральных носителях выбранного
  семейства; НИКАКИХ кофинальных кванторов и rate-утверждений.
EXACT_QUANTIFIERS: >-
  по-тождественные конечные утверждения (FORALL P k / FORALL z и т.п.),
  без пределов.
NORMALIZATION: "как в исходных файлах, без переопределений"
COFINAL_SCHEDULE: "N/A — family-параметрические конечные утверждения без пределов"
PRESERVES: "всё"
DROPS: "ничего"
OLD_FATAL_BYPASSED: "никакой — явно НЕ reentry-заявка; банковка активов"
WHY_THIS_IS_NOT_ANOTHER_WRAPPER: >-
  не вводит ни одного нового оценочного объекта — только формализация уже
  адъюдицированных тождеств.
MINIMAL_THEOREM_FACING_OUTPUT: >-
  зелёные Lean-узлы с чистой тройкой аксиом по каждому тождеству +
  Aristotle-сабмишен-манифест с SHA-пинами (состав и формулировки
  финализирует судья).
DISCRIMINATOR:
  PASS: по-узловой kernel-green
  FAIL: узел не зелёный (без семантических последствий для маршрута)
KILL_CONDITION: >-
  любой сабмишен, протаскивающий rate/кофинальный квантор без явной
  авторизации фрагмента судьёй.
REOPEN_CONDITION: "отсутствует — дорожка не основание reentry ни при каком исходе"
LEAN_AUTHORIZED: >-
  true, по-узлово после фиксации состава судьёй (полный гейт: lake env
  lean; lake build; полная сборка; q3_check; hole-scan; чистая тройка;
  source record v7)
NUMERICS_AUTHORIZED: false
EXPECTED_CLOSES:
  - формализационный долг граф/P59/penalty/портов (консюмеры уже в корпусе)
EXPECTED_OPENS: []
KILL_POWER: "N/A (банковка)"
COST: 4/10
```

ОБЩИЙ ДИСКРИМИНАТОР REENTRY (прекоммит): коридор размораживается ТОЛЬКО
при Track 1 = PASS; Track 2 ни при каком исходе не основание reentry;
смешение дорожек запрещено; stop-rule на обёртки действует внутри обеих.
