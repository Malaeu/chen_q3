# STATUS: TRY_ACTUAL_THETA_ODD2LOW_INCOMPLETE
```yaml
OPERATIVE_CLASS: TRY_ACTUAL_THETA_ODD2LOW_INCOMPLETE
REQUEST_ID: REQ-2026-09-12-ODD2LOW
BOUNDARY_ID: GOAL058_ACTUAL_THETA_ODD2_WHOLE_LOW_NODE_REMAINDER
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c
ACCEPTED_DELTA_COMMIT: 877d4eaaa7ebf587906561a930833e76d9acb134
REQUEST_COMMIT: f843c3743b629387fa4e39654735823129e92551
REQUEST_BLOB: 02db439ac1fc2ebac3a7feb354ebf8e63bb88726
REQUEST_SHA256: fdf8d07ab354190a028440611dcb2fe99bcd5e797d7633a9de0316f833d2b062
REQUEST_OUTCOME: INCOMPLETE
RESULT_SCOPE: NO_NEW_ACTUAL_THETA_SIGN_CERTIFICATE
BYTE_INTEGRITY: MATCHED
SOURCE_FRAME_HASHES_MATCHED: 35
FULL_SEMANTIC_READ_COMPLETED_IN_THIS_ATTEMPT: false
WHOLE_LOW_PROVED: false
WHOLE_LOW_REFUTED: false
GLOBAL_ODD2_PROVED_BY_THIS_RESPONSE: false
ACTUAL_THETA_NEGATIVE_WITNESS: NOT_OBTAINED
NEW_SOURCE_CERTIFICATE: NONE
ABSTRACT_IDENTITY_CHECK: EXACT_RATIONAL_CONTROLS_ONLY
NEW_INDEPENDENT_ACCEPTANCE: NOT_PERFORMED
LEAN_VERIFIED: false
REPOSITORY_WRITES: none
RUNTIME_STATE_CHANGED: false
NO_DELTA_COUNTER:
  request_initial: 0
  proposed_on_incomplete_closeout: 1
  machine_changed: false
PX_RH_CLAIM: NOT_MADE
```

Ы. Полный знак на **LOW1–LOW3** в этой попытке не установлен. Отрицательный свидетель исходного ядра не получен. Ниже сохранены точный остаток задачи и алгебраическая проверка нового представления. **Это незавершённый отчёт, не доказательство полного ODD2.**

## 0. Граница завершённости

Байтовая целостность запроса и всех 35 встроенных источников проверена; полный манифест находится в приложении A. Проверка хешей не означает содержательного приёма доказательств.

Полное содержательное чтение всех 35 источников и новый вычислительный сертификат в этой попытке не завершены. Поэтому этот файл не объявляет выполнение всех требований запроса. Принятые результаты ниже используются в том объёме, который указан контролирующим запросом; нового независимого аудита им не приписывается.

После прерванной части работы не получен наблюдаемый результат нового исходного интервального расчёта. В документе нет придуманного покрытия, числа листьев, положительного минимума или отрицательной ячейки. Единственный новый машинный контроль — точная рациональная проверка алгебраического тождества на искусственных контрольных матрицах; это не расчёт theta.

## 1. Неизменённый объект и принятые входы

Во всём документе
\[
F(x)=\Phi(x)=e^{5x/2}r(e^{2x}),\quad A=\|F\|_2,\quad f=F/A,
\]
\[
r(t)=2\sum_{n\ge1}(2\pi^2n^4t-3\pi n^2)e^{-\pi n^2t},
\qquad r(1/t)=t^{5/2}r(t).
\]
\[
V(s,t)=\int_0^\infty(s+t+2v)f(s+v)f(t+v)\,dv,
\quad K(s,t)=V(s,t)-V(s,-t),
\]
\[
\Delta(x,y)=K(x,x)K(y,y)-K(x,y)^2,
\quad \mathcal K=A^2K,\quad\mathcal D=A^4\Delta.
\]

**Сырой масштаб** означает использование \(F\) вместо \(f\); это умножение формы на \(A^2>0\), не смена источника.

Из контролирующего запроса сохраняются: положительность элементов \(K\) на положительной четверти; весь ODD2 при \(\min(x,y)\ge1\); весь max-node хвост \(\max(x,y)\ge5\); origin-квадрат \(0<x,y\le1/4\); смешанные полосы \(x\ge2,0<y\le1/4\) и \(x\ge3/2,0<y\le1/256\); ранее принятые AX/DG. Их доказательства в этом проходе не заменяются новыми утверждениями.

Источник этих статусов — сам запрос и источники S20, S24, S30, S31–S35 согласно приложению A. Области не расширяются по численной похожести.

## 2. Весь неоплаченный остаток

Работаем с порядком \(x>y>0\). Не закрытая этим ответом область — вся область запроса:
\[
\boxed{\begin{aligned}
\mathrm{LOW1}:&\quad0<y\le1/256,&&1/4<x<3/2,\\
\mathrm{LOW2}:&\quad1/256<y\le1/4,&&1/4<x<2,\\
\mathrm{LOW3}:&\quad1/4<y<1,&&y<x<5.
\end{aligned}}
\tag{L1}
\]
Из неё по-прежнему вычитаются принятые AX/DG. Для неупорядоченных пар добавляется транспонированная область. Границы \(y=1/256\) и \(y=1/4\) распределены именно так, как в (L1). Граница \(x=5\), верхние границы принятых смешанных полос и область min≥1 не потеряны: они оплачены соответствующими принятыми теоремами. Диагональ \(x=y\) имеет точное значение \(\Delta=0\), но знак её делённого продолжения остаётся отдельным обязательством там, где он ещё не принят.

Новых исключённых исходных ячеек нет. Поэтому нет скрытого списка непроверенных панелей: **остаток — всё (L1) за вычетом только ранее принятых AX/DG.**

## 3. Проверенное представление без деления округлённого нуля

### 3.1. Одновременно убираем оси и масштаб \(F\)

Положим \(u=x^2\), \(v=y^2\) и
\[
P(u,v)=\frac{\mathcal K(\sqrt u,\sqrt v)}
 {\sqrt{uv}\,F(\sqrt u)F(\sqrt v)}.
\tag{L2}
\]
При нулевом аргументе используется гладкое продолжение, не численное деление. Оно существует: \(\mathcal K\) гладка и нечётна по каждому исходному аргументу, а \(F\) гладка, чётна и положительна. В частности,
\[
\frac{\mathcal K(x,y)}{xy}
 =\int_0^1\int_0^1\mathcal K_{12}(ax,by)\,da\,db.
\tag{L3}
\]
Полученная функция чётна по \(x,y\) и допускает гладкую запись в квадратных координатах на замкнутой положительной четверти. Здесь достаточно конечной гладкости для указанных ниже производных. Положительные разделимые множители в (L2) сохраняют знак всех двухузловых определителей и допускают произвольные комплексные коэффициенты.

### 3.2. Диагональное сокращение — точное тождество

Пусть \(h=u-v\). Определим
\[
a=P(v,v),
\quad b=\int_0^1P_1(v+\theta h,v)\,d\theta,
\]
\[
c=\int_0^1\int_0^1
P_{12}(v+\theta h,v+\eta h)\,d\theta\,d\eta.
\tag{L4}
\]
Основная теорема анализа и симметрия \(P\) дают
\[
P(u,v)=a+hb,
\qquad P(u,u)=a+2hb+h^2c.
\]
Следовательно,
\[
\boxed{P(u,u)P(v,v)-P(u,v)^2=h^2(ac-b^2).}
\tag{L5}
\]
Оба исчезающих члена сокращаются до округления. В исходной нормировке:
\[
\boxed{
\Delta(x,y)=x^2y^2(x^2-y^2)^2
 f(x)^2f(y)^2\,[ac-b^2].
}
\tag{L6}
\]
**Это тождество, не утверждение положительности.** Оно не использует IC и не требует положительности подынтегральной матрицы.

На диагонали \(u=v\) имеем
\[
a=P(v,v),\qquad b=P_1(v,v),\qquad c=P_{12}(v,v).
\]
Иными словами, исчезающий множитель \((x^2-y^2)^2\) удалён аналитически.

### 3.3. Две границы в исходных обозначениях

Пусть \(\kappa_{\rm raw}=\mathcal K_{12}(0,0)\). Для
\[
\mathscr R(x,y)=
\frac{\Delta(x,y)}{x^2y^2(x^2-y^2)^2f(x)^2f(y)^2}
\]
получаются точные продолжения
\[
\mathscr R(x,0)=
\frac{\kappa_{\rm raw}\mathcal K(x,x)-\mathcal K_2(x,0)^2}
{x^6F(x)^2F(0)^2},
\tag{L7}
\]
\[
\mathscr R(t,t)=
\frac{\mathcal K(t,t)\mathcal K_{12}(t,t)-\mathcal K_1(t,t)^2}
{4t^6F(t)^4}.
\tag{L8}
\]
В (L7) и (L8) утверждается равенство, а не новый знак. Разделение оси, диагонали и самого origin-corner сохраняется. В остатке (L1) большой узел отделён от нуля числом \(1/4\); совпадение обоих узлов с нулём не требуется заново доказывать.

## 4. Где остановилась попытка

Первый неоплаченный знак в новом представлении:
\[
\boxed{a(u,v)c(u,v)-b(u,v)^2\ge0
\quad\text{на всём образе (L1) в квадратных координатах}.}
\tag{L9}
\]
Положительность \(a\) следует из принятой положительности диагонали. Нужного сравнения \(c\ge b^2/a\) из полного источника в этом ответе не получено.

Применять здесь неравенство Коши–Буняковского без независимо построенного положительного скалярного произведения нельзя. Величины \(a,b,c\) определены через исходное знаковое ядро; из записи (L4) не следует, что они являются скалярными произведениями трёх нужных профилей в положительном пространстве.

Отдельные верхние оценки абсолютных производных \(P\) дают лишь ограниченность \(b,c\). Они не дают нижней оценки \(ac-b^2\). Заменить это отсутствующее сравнение гипотезой «\(P\) положительно определено» означало бы предположить целевой знак.

**NO_PROGRESS_TAUTOLOGY:** объявлять (L9) новой решённой задачей или новым положительным поставщиком нельзя. Это ODD2 после точного устранения вырождений. Представление устраняет конкретную алгебраическую потерю, но само не уменьшает неоплаченную исходную область.

Родительский неудачный расчёт с независимыми интервальными включениями диагонали и смешанного квадрата не продолжался увеличением прежнего лимита. Нового theta-покрытия по (L4)–(L9) не выполнено. Поэтому ни один положительный либо отрицательный численный вывод для actual theta в этом документе не заявляется.

## 5. Предсказание и проверка инструмента

Перед новой алгебраической проверкой зарегистрировано: точное устранение факторов оси/диагонали сохранит знак, но не предоставит сам знак theta. Алгебраическая часть подтверждена выводом (L3)–(L6). Часть о theta остаётся незакрытой и не оценивается как успешное предсказание её положительности.

Проверка инструмента использует искусственные матрицы
\[
M_h(r)=\begin{pmatrix}
1&1+h\\1+h&1+2h+(1+r)h^2
\end{pmatrix},
\qquad\det M_h(r)=r h^2.
\]
Для \(r=1/4,0,-1/4\) и \(h=1,1/2,2^{-1000}\) точная рациональная арифметика различает положительный, нулевой и отрицательный делённые определители. Отрицательный контроль \(r=-1/4\) — искусственный, **не** отрицательный свидетель theta. При точном \(h=0\) исходный определитель всегда нулевой; дискриминатором является продолженная величина \(r\), а не повторное измерение этого нуля.

Полный код и полный вывод контроля находятся в приложении B. Он подтверждает только правильность алгебры и направления знакового теста; не универсальный квантор по исходным узлам.

## 6. Точный отрицательный свидетель, если знак будет отрицательным

Для исходной пары положительных узлов \(x,y\) положим
\[
a_0=K(x,x)>0,\quad b_0=K(x,y),\quad d_0=K(y,y).
\]
Для любых комплексных коэффициентов
\[
(c_1,c_2)^*K_2(c_1,c_2)
=a_0\left|c_1+\frac{b_0}{a_0}c_2\right|^2
+\frac{\Delta(x,y)}{a_0}|c_2|^2.
\tag{L10}
\]
Если будет получена строгая верхняя огибающая \(U(\Delta)<0\), точный свидетель задаётся коэффициентами
\[
(c_1,c_2)=(-b_0/a_0,1).
\]
Его значение равно \(\Delta/a_0<0\). На четырёх исходных узлах с нечётными коэффициентами форма равна удвоенной (L10). В этом ответе гипотеза \(U(\Delta)<0\) не установлена ни для одной actual-theta пары.

## 7. Карта представлений и границы их применения

| Представление | Проверяемый объект | Разрешающая сила | Стоимость и риск | Статус |
|---|---|---|---|---|
| Делённая матрица (L4) | \(ac-b^2\) на полном остатке | При полном нижнем бюджете закрывает весь LOW, включая ось/диагональ | Нужны совместные оценки полного источника, а не независимые широкие интервалы | Тождество выведено; исходный знак не установлен |
| Прямой Schur-остаток с Taylor-моделью | \(K_{yy}-K_{xy}^2/K_{xx}\), после аналитического удаления известных нулей | Может дать точный исходный отрицательный свидетель или полный положительный бюджет | Примерно средняя/высокая вычислительная стоимость; главное — совместная зависимость коэффициентов | В этой попытке не выполнен |

Это варианты представления оставшейся задачи, не новые поручения и не разрешение на очередной неограниченный перебор. Выбор первого представления не делает его необходимым условием для всех возможных доказательств ODD2.

## 8. Dependency epistemics и реестр утверждений

```yaml
DOWNSTREAM_CONSUMER: ACTUAL_THETA_GLOBAL_ODD2
ACTUAL_CONSUMER_REQUIREMENT: Delta(x,y) >= 0 for all positive real x,y
ORIGINAL_REQUESTED_OBJECT: WHOLE_LOW1_LOW2_LOW3_REMAINDER
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
NECESSITY_SCOPE: full LOW remainder together with the accepted complement is equivalent to global ODD2
KNOWN_WEAKER_INTERFACES:
  - exact nonnegative Schur residual on the same whole remainder
  - lower envelope for the entire divided determinant in L9
  - an independent positive representation retaining the full original kernel
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: cancellation-preserving divided representation, not a new source sign theorem
KILL_SCOPE: NONE
KILL_EVIDENCE_KIND: NONE
REOPEN_TRIGGER: completed semantic intake and a recheckable source-specific bound for L9 or an equivalent full-consumer expression
DISCRIMINATOR:
  axis: kappa_raw*Kraw(x,x)-Kraw_2(x,0)^2
  diagonal: Kraw(t,t)*Kraw_12(t,t)-Kraw_1(t,t)^2
  interior: exact Schur residual or a rigorous enclosure of L9
```

| Утверждение | Scope | Verifier | Точный статус |
|---|---|---|---|
| Целостность запроса и 35 кадров | FINITE_CELL | PAPER | Байтовая проверка выполнена; не математический приём |
| Принятые min≥1, max≥5, origin-quarter, смешанные полосы, AX/DG | ABSTRACT | CONDITIONAL | Наследуются из запроса с их точными границами |
| Равенства (L2)–(L8), (L10) | ABSTRACT | PAPER | Алгебраические/дифференциальные выводы; нового Lean-приёма нет |
| Искусственные проверки знака | FINITE_CELL | PAPER | Точная рациональная арифметика; не actual theta |
| Неотрицательность (L9) на LOW | ABSTRACT | CONDITIONAL | Не доказана, не предположена |
| Глобальный ODD2 | ABSTRACT | CONDITIONAL | Не закрыт данным ответом |
| IC, большие нечётные матрицы, чётный сектор, полный V/Q, RH | ABSTRACT | CONDITIONAL | Повышения статуса нет |

## 9. Meta closeout

**Что стало точнее:** указан единый делённый объект, в котором исчезающие множители оси и диагонали удалены до интервального расчёта. Выведены обе граничные формулы и точный отрицательный вектор на случай строгого отрицательного знака.

**Что закрыто для actual theta:** новых узловых семейств нет. Полная LOW-область не уменьшилась. Полный семантический приём пакета в этой попытке также не завершён.

**Что убито:** никакая исходная теорема, никакое семейство маршрутов и никакая actual-theta ячейка не объявлены отрицательными. Искусственная отрицательная матрица используется только как контроль инструмента.

**Что не повторять:** продолжение старого независимого интервального вычитания с увеличенным бюджетом; повышение компактности или отсутствия найденного свидетеля до доказательства; объявление (L9) новой положительной структурой.

**Текущий минимальный вход:** полный нижний бюджет для (L9) на (L1), включая указанные продолжения. Недостающий результат не скрыт в новом названии.

```yaml
PROGRESS_CLASS: NO_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
STATUS_OF_CURRENT_SOURCE_SIGN_ATTEMPT: INCOMPLETE
SOURCE_SIGN_DELTA: NONE
COUNTER_INITIAL: 0
COUNTER_PROPOSED_ON_INCOMPLETE_CLOSEOUT: 1
COUNTER_RESET: false
COUNTER_MACHINE_WRITE: false
OWNER_OR_ROUTE_PROMOTION: none
NEXT_TASK_ASSIGNED: none
```

Нет нового независимого приёма. Нет Lean-источника, компиляции, коммита, очереди или записи состояния. Этот документ не заменяет требуемое полное доказательство.

## Приложение A. Побайтовый манифест всех источников

```json
[
  {
    "index": 1,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_JOINT_TAIL.md",
    "bytes": 10500,
    "lf": 227,
    "sha256": "2643695929014d3c7bab32aa05c1e560aa91328a909963f5741346727e1d0fb6",
    "git_blob": "bdf7b5c7d8dcc3e638c593b8e44216346c317ed7",
    "request_header_line": 172
  },
  {
    "index": 2,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_COMPACT_LOCALIZATION.md",
    "bytes": 8292,
    "lf": 179,
    "sha256": "ff3a515fd259b1e2b7e22d98f3aa0faba196e9217c65fa384ed666bcedc03648",
    "git_blob": "192c3a7d34a4a877bd3a1f7392602c2977748101",
    "request_header_line": 402
  },
  {
    "index": 3,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_ORIGIN_CORNER.md",
    "bytes": 9392,
    "lf": 205,
    "sha256": "1b507d7c22480de44e4215131d34c3d1f8211b3715556fa7d96aa55cf97a7b2a",
    "git_blob": "513a5f0e10574cc33a2a63e1e2a6c5ba0e6ae2bd",
    "request_header_line": 584
  },
  {
    "index": 4,
    "path": "docs/Codex/certificates/ODD2_ORIGIN_JET_20260912.py",
    "bytes": 5248,
    "lf": 109,
    "sha256": "8faa791349fba23f76c9b2394f8c9bfd2a73c81b25f3f50ae109f05e4c34f1d1",
    "git_blob": "1ba06d99286e3a12edf646435b3c9503e551566b",
    "request_header_line": 792
  },
  {
    "index": 5,
    "path": "docs/Codex/certificates/ODD2_ORIGIN_JET_20260912.json",
    "bytes": 2398,
    "lf": 73,
    "sha256": "4c543719a6b2e8330be6b82a705470b4bfac425c07aed9db137b1083cf30ae07",
    "git_blob": "cc8c16a741e0b7ba3acfdd8dc04e1ef68e6c861e",
    "request_header_line": 904
  },
  {
    "index": 6,
    "path": "docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODDCURV_OWNER_CONTINUATION_2026-09-12.md",
    "bytes": 39236,
    "lf": 651,
    "sha256": "2281280161631905987633e895c34e980470bbeda517e3bc4c1df2ce2d0e9833",
    "git_blob": "de30b40f14f5da45d0f775119c2a45f854cd7beb",
    "request_header_line": 980
  },
  {
    "index": 7,
    "path": "docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODDCURV_2026-09-12.md",
    "bytes": 52645,
    "lf": 831,
    "sha256": "3309c6fb3f5c3a0e20979c14b9a36471e753feed18a42017b4f211fafe6ea840",
    "git_blob": "dc2e5b6dced9828f2bb5713b2d7a740230624357",
    "request_header_line": 1634
  },
  {
    "index": 8,
    "path": "docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md",
    "bytes": 37796,
    "lf": 467,
    "sha256": "14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc",
    "git_blob": "de9578084446baecfbb2a316d7bda3da817c8c01",
    "request_header_line": 2468
  },
  {
    "index": 9,
    "path": "docs/routeB_bus/proshka/PROSHKA_HODGE_WEIL_NEGATIVE_WITNESS_REVIEW_2026-09-12.md",
    "bytes": 38721,
    "lf": 507,
    "sha256": "8f51bfb60f4221c53d094bd901fb5bdcff26568331dca69d6a5ee276b3476f04",
    "git_blob": "8bf5df96f7dd8d19d5d6f54afb650d35a6585a55",
    "request_header_line": 2938
  },
  {
    "index": 10,
    "path": "docs/Codex/REPORT_2026-09-12_HODGE_WEIL_INTAKE.md",
    "bytes": 6268,
    "lf": 130,
    "sha256": "693a555b3fea5eebddb0c21b3ebe2da4591f6b67a83d3f428033ae23b4555789",
    "git_blob": "dad3da901c4da1cc6b0a29a7bead0c5dfe2e156a",
    "request_header_line": 3448
  },
  {
    "index": 11,
    "path": "docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md",
    "bytes": 15303,
    "lf": 335,
    "sha256": "1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282",
    "git_blob": "b8b5a1a8739c946f75340f3115616d6f9ba5b40e",
    "request_header_line": 3581
  },
  {
    "index": 12,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_ORIGIN_EXPLICIT_RADIUS.md",
    "bytes": 7117,
    "lf": 174,
    "sha256": "ffc8e2cb7fbd28d1cbb657d1a28accec074d6ecaf7fb4c384c88f659d2036775",
    "git_blob": "44ede2ca5d937e11185ad8ac9a492356d7026295",
    "request_header_line": 3919
  },
  {
    "index": 13,
    "path": "docs/routeB_bus/proshka/PROSHKA_THETA_TOTAL_POSITIVITY_SOURCE_TEST_2026-09-12.md",
    "bytes": 50632,
    "lf": 842,
    "sha256": "654c1a3bfe0a4eb570adce71c6d62d7b97deca110765de79a7776dd6878b5bd7",
    "git_blob": "39158fadc2d0f9a7f0e173230a7e76f83e64ed73",
    "request_header_line": 4096
  },
  {
    "index": 14,
    "path": "docs/Codex/REPORT_2026-09-12_THETA_TN_INFINITY_INTAKE.md",
    "bytes": 6476,
    "lf": 130,
    "sha256": "ae39ab4cbbfae7ad8c04b61dfb9828c6e9efa0247a538da72e4bd3e748de3790",
    "git_blob": "3ef9deb005426ac2cab236b2b034ef2ec0d4aadc",
    "request_header_line": 4941
  },
  {
    "index": 15,
    "path": "docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2COMPACT_2026-09-12.md",
    "bytes": 71971,
    "lf": 1159,
    "sha256": "819511db9d46801e87b54e728faf7c55e7ce21e4e20e48d9d95d49a71b175e07",
    "git_blob": "c3679dba810674116f3d92892b4630555f56dd49",
    "request_header_line": 5074
  },
  {
    "index": 16,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2COMPACT_INTAKE.md",
    "bytes": 6786,
    "lf": 138,
    "sha256": "28ade6ecde8d9327328ec42bde5c6a1ac8c0e5c0cb285a838db985fda01da133",
    "git_blob": "dbf6f7fdf2b4ca646c327c01ab0c47b5febedbd0",
    "request_header_line": 6236
  },
  {
    "index": 17,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_REGIONAL_MIN1_GAP3.md",
    "bytes": 7974,
    "lf": 202,
    "sha256": "9d568cc75aa42d2e9ee30cee62869eafa9f93bea825ddbcbe8bf6afb16011050",
    "git_blob": "d6e2f9f9c5f65794d026a1d08783d03ac3851818",
    "request_header_line": 6377
  },
  {
    "index": 18,
    "path": "docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2EFFECTIVE_2026-09-12.md",
    "bytes": 73274,
    "lf": 1060,
    "sha256": "06a009eae972027f01f8e0e2d096b7a1e6a453e7b03e55f4a5b7cbd217a29f94",
    "git_blob": "b3d015093a1052a090c475d970bef72b5c45a9b3",
    "request_header_line": 6582
  },
  {
    "index": 19,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2EFFECTIVE_INTAKE.md",
    "bytes": 8418,
    "lf": 166,
    "sha256": "af008a34ad1bd1e4419272797ee7422653005011167a5744defd53d382a3f672",
    "git_blob": "4c77d81917de5d304dce946a3e9d95c5ef7a24e8",
    "request_header_line": 7645
  },
  {
    "index": 20,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_ORIGIN_QUARTER_BOX.md",
    "bytes": 12595,
    "lf": 264,
    "sha256": "d694654cf04951289ccf49cb828a8fbcce24ad07d70ab3823ea7c7ebe3ab2f72",
    "git_blob": "4b5d8a66dec1460c181313cc36857169e95eddfc",
    "request_header_line": 7814
  },
  {
    "index": 21,
    "path": "docs/Codex/certificates/ODD2_ORIGIN_BOX_20260912.py",
    "bytes": 8050,
    "lf": 176,
    "sha256": "545f60cd85a38ee81c01fbfe498e5ab0b6709f5fa2b5f0564d456425510b9b7c",
    "git_blob": "6b5bf72e4cfa45c8bcd69db5fcb5de1f8a09f0e3",
    "request_header_line": 8081
  },
  {
    "index": 22,
    "path": "docs/Codex/certificates/ODD2_ORIGIN_BOX_20260912.json",
    "bytes": 35577,
    "lf": 546,
    "sha256": "6bd7ad33745defe18d111c731cc04c669db3c480d6b8c1282ef782e21f77cbb0",
    "git_blob": "def5e9f9eed6b409cc6cbdbb1a1b8d78b13ddef7",
    "request_header_line": 8260
  },
  {
    "index": 23,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_SMALL_NODE_EFFECTIVE_TAIL.md",
    "bytes": 8807,
    "lf": 204,
    "sha256": "918ebee2be455792c45012d852c23126907dcbdb3a72233a24b80928f268f138",
    "git_blob": "43f531622a2fdbb8d4407d04613031b6717328e4",
    "request_header_line": 8809
  },
  {
    "index": 24,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_SMALL_NODE_TAIL5.md",
    "bytes": 14193,
    "lf": 335,
    "sha256": "088cfa2fcaa28a3d7d17e7e4da7f59722561907f5e177d2dc47b08bff4557766",
    "git_blob": "2da1ee621e0706c44b88269a3cf610ee8d03cea6",
    "request_header_line": 9016
  },
  {
    "index": 25,
    "path": "docs/Codex/certificates/SOURCE_HCURV_20260912.py",
    "bytes": 2127,
    "lf": 31,
    "sha256": "73cc93f0fbe6bb44526ed1e44d8adfc46772d79814a6227a0b9fb508d1c13aaa",
    "git_blob": "0e47957b86112c2fa8eb76743f6edbb2c9b1b424",
    "request_header_line": 9354
  },
  {
    "index": 26,
    "path": "docs/Codex/certificates/SOURCE_HCURV_20260912.json",
    "bytes": 9764,
    "lf": 171,
    "sha256": "ee0d03ac11775bdc3f96519077ab0c1f0617852098b573b71764c11c2e964dd2",
    "git_blob": "c67229c5564281fbe505259836f4ab5fa88c9340",
    "request_header_line": 9388
  },
  {
    "index": 27,
    "path": "docs/Codex/certificates/ODD2_TAIL5_RATIONAL_20260912.py",
    "bytes": 1693,
    "lf": 37,
    "sha256": "73c2451678d2b6bdbcfe4abf97765797ca549792a9efa2b7c0e70fbdd9aa9722",
    "git_blob": "139cf3047a40614af862684e65f7cc35e6c33222",
    "request_header_line": 9562
  },
  {
    "index": 28,
    "path": "docs/Codex/certificates/ODD2_TAIL5_RATIONAL_20260912.json",
    "bytes": 3025,
    "lf": 147,
    "sha256": "22607dffe096d373fd57bc929f4653fa9f7f6f75cbb8addf6bd2903ecac67329",
    "git_blob": "31d923b9f1f98e5cc0b65fd4c990c3f4359320a8",
    "request_header_line": 9602
  },
  {
    "index": 29,
    "path": "docs/Codex/certificates/SOURCE_HCURV_PREREG_20260912.txt",
    "bytes": 817,
    "lf": 12,
    "sha256": "205430e9146c55213ccf06fb82832ec662748610d39589c57809f4b6ad752328",
    "git_blob": "4346bf6ed8a451c57d736b8ae9f9896c8e725c30",
    "request_header_line": 9752
  },
  {
    "index": 30,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2_MONOTONE_MIXED_AXIS.md",
    "bytes": 8482,
    "lf": 200,
    "sha256": "b7f054579aba17cf6747b1116bbf3d59bc111deb36580d299abcc5819aae0bc6",
    "git_blob": "8185a7dc0e11cc16a6b112ccc371b8cc460a2283",
    "request_header_line": 9767
  },
  {
    "index": 31,
    "path": "docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2STRIP_2026-09-12.md",
    "bytes": 108317,
    "lf": 1808,
    "sha256": "063ecc08ce1671fcaa944c980c36c4899f97caa1d65473c2db974222d27bed3b",
    "git_blob": "38cadbfe9f66d4080e80a7ef1a81273250e18989",
    "request_header_line": 9970
  },
  {
    "index": 32,
    "path": "docs/Codex/REPORT_2026-09-12_ODD2STRIP_INTAKE.md",
    "bytes": 8954,
    "lf": 174,
    "sha256": "4b1347395248f0e1c46d4df43cfb6c60a0f9dad7adbd2628e040dd0d344f9fde",
    "git_blob": "776f4006196b6fc72def237900f58983e3f23def",
    "request_header_line": 11781
  },
  {
    "index": 33,
    "path": "docs/Codex/certificates/ODD2_STRIP_20260912.py",
    "bytes": 13862,
    "lf": 324,
    "sha256": "f6c03177e0f91e52d1fb6080fcb63d4f71306d3da9d4a7de700a7dbf9268517a",
    "git_blob": "714d3bf1ddba47e81f22d8ed1994a9352f9a5350",
    "request_header_line": 11958
  },
  {
    "index": 34,
    "path": "docs/Codex/certificates/ODD2_STRIP_20260912.json",
    "bytes": 11068,
    "lf": 128,
    "sha256": "d8d8da5f902a122954c972bbc86f003b9f5fa91e7199b0e42ff4cdfbda179bdb",
    "git_blob": "08004e6ce8fb3dbd4df62c9a92a7a33f3077b15b",
    "request_header_line": 12285
  },
  {
    "index": 35,
    "path": "docs/Codex/certificates/ODD2_STRIP_REPLAY90_20260912.json",
    "bytes": 648,
    "lf": 16,
    "sha256": "e0c969fae600495fd6b2453e6fe176967f8da6ece671be7ce9fe3f832f5242b5",
    "git_blob": "72d57286e4a2c570a3319c154cb2ca6bf10104cb",
    "request_header_line": 12416
  }
]
```

## Приложение B. Воспроизводимый контроль тождества

Сохрани код как `odd2low_divided_identity_control.py` и выполни `python3 odd2low_divided_identity_control.py`. В имени файла нет подстановок переменных. Проверяются только искусственные матрицы.

```python
from fractions import Fraction as Q
for r in [Q(1,4), Q(0), Q(-1,4)]:
    for h in [Q(1), Q(1,2), Q(1,2**1000)]:
        a=Q(1); b=Q(1); c=Q(1)+r
        p00=a
        p01=a+h*b
        p11=a+2*h*b+h*h*c
        determinant=p00*p11-p01*p01
        assert determinant == h*h*(a*c-b*b)
        assert determinant/(h*h) == r
        print(str(r), h.denominator.bit_length(), 'PASS_EXACT_IDENTITY')
```

Полный машинный результат:

```json
[
  {
    "control": "positive",
    "h_denominator_bits": 1,
    "divided_determinant": "1/4",
    "exact_identity": true
  },
  {
    "control": "positive",
    "h_denominator_bits": 2,
    "divided_determinant": "1/4",
    "exact_identity": true
  },
  {
    "control": "positive",
    "h_denominator_bits": 1001,
    "divided_determinant": "1/4",
    "exact_identity": true
  },
  {
    "control": "zero",
    "h_denominator_bits": 1,
    "divided_determinant": "0",
    "exact_identity": true
  },
  {
    "control": "zero",
    "h_denominator_bits": 2,
    "divided_determinant": "0",
    "exact_identity": true
  },
  {
    "control": "zero",
    "h_denominator_bits": 1001,
    "divided_determinant": "0",
    "exact_identity": true
  },
  {
    "control": "negative",
    "h_denominator_bits": 1,
    "divided_determinant": "-1/4",
    "exact_identity": true
  },
  {
    "control": "negative",
    "h_denominator_bits": 2,
    "divided_determinant": "-1/4",
    "exact_identity": true
  },
  {
    "control": "negative",
    "h_denominator_bits": 1001,
    "divided_determinant": "-1/4",
    "exact_identity": true
  }
]
```
