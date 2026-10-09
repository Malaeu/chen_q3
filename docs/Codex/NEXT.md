# Q3 — где мы и что дальше

Единственная точка продолжения на любой машине: `git pull` → прочитать этот файл → работать.
Обновлять в каждом рабочем коммите (заменой, не дописыванием). Максимум ~80 строк.
При закрытии ворот, фазы или вилки — сразу обновить «Дорожную карту» в том же коммите.
Режим: простой (owner instruction 2026-09-25, control §1 precedence).

Updated: 2026-10-07 · Codex Mac after Linux handoff883a1fa8. Read `../literature/openai_math_2026-10-07/COMPARATOR_VERIFICATION.md` (Linux ZF78 check report) and `../literature/openai_math_2026-10-07/linux_needle_scan/REPORT.md` (moment candidate, no SP gain). Mac retains main execution; Direct Shift Q1 processed.

## Цель
Дойти до `PX_RH_CLAIM` — заявления «RH доказана». Всё направлено на него.
Цель в Lean: `RiemannHypothesis.riemannHypothesis : RiemannHypothesis`
(`q3.lean.aristotle/comparator/Challenge.lean`, Mathlib `RiemannHypothesis`).

Claim делается, только когда он действительный — все условия сразу:
1. Lean-доказательство цели собирается на чистом клоне, Comparator проходит.
2. Ни одного `sorry`; `#print axioms` показывает только propext, Classical.choice, Quot.sound.
3. Независимые проверки (разные модели и люди) раз за разом не находят ни одной ошибки.
4. Владелец объявляет claim.
До этого статус честный: RH ещё не доказана. Это состояние, а не цель.

## Стратегия (владелец, 2026-09-25): сначала бумага, потом Lean
1. Сначала закрываем МАТЕМАТИЧЕСКИ, на бумаге, все недостающие звенья цепи до RH — вместе с Прошкой.
   На это тратим время и токены.
2. Lean сейчас — только если без него дальше никакая математика не идёт
   (например, шаг держится на конечной проверке, которой верим только после kernel-check).
   То, что уже можно формализовать, но не блокирует бумагу, — откладываем.
3. Когда вся цепь закрыта на бумаге — формализация в Lean, Comparator, проверки, claim.
4. Проверки делаем, когда без них нельзя двигаться (ошибка на бумаге дороже, чем проверка).

## Дорожная карта
Прежняя программа: Route B → Goal058, крыша `rh_of_real_zero_family_tendsto_centeredXi` (одна семья F: вещественные нули + F → Ξ).
Все звенья, статусы, последний доказанный результат и убитое — только в `docs/Codex/PAPER_CHAIN.md` (не дублировать здесь).
Коротко: закрыто на бумаге 8 из 14 (G2, G2b, hentire, G5 — Lean; G4 — статья CCM; hmode, hχ/hθ, selected-shell G3c — бумага);
ядро открыто: G1 (простота/чётность основного состояния) и G3 (tracking), плюс итоговая сборка; G3c и selected-shell crosswalk G4 проверены при HMODE/chi.

## Следующий шаг — полный CCM: рост отрицательного дна
После записанных тупиков source-transfer, direct localization и weak overlap выбран новый
условный потребитель на ТОЙ ЖЕ полной K_m, m=N, L=log m, исходный eventual schedule.
Активная ветка: полный CCM → SP → исключение off-critical zeros → RH; SP открыт.
1. Ответ10 и собственное усиление проверены: если есть ноль .5+delta+i gamma, delta>0, то
   lambda_min(K_m)≤−c m^delta/(log m)^(2delta) на каждой достаточно поздней ячейке.
   Это условная альтернатива, а не найденный ноль и не доказательство RH.
2. Достаточная открытая цель SP: для каждого eta>0 доказать
   lambda_min(K_m)≥−C_eta m^eta eventually. Старые G1/G3 этим не закрыты.
3. Ответ1 новой фазы проверен: causal A даёт равномерную оценку в норме прообраза,
   но carrier-wide возврат этой нормы убит верхней модой даже с D_arch.
   Для F=(I−R)Z, F=VM, Y=V*XV осталось оценить сверху
   D=M^-1[M,[M,Y]]M^-1: <f,Df>≤D_arch(f)+C_eta m^eta||f||² на полном V_m.
   Достаточно неограниченной подпоследовательности для каждого eta. Эта оценка OPEN.
   Ответ3 проверен: полный floor −cA−C sqrt(m)L³ exp(−.001(L/log L)^(1/3)), все моды и cross terms оплачены.
   Это выигрыш любой степени log, но exponent 1/2−o(1), не SP. Следующий шаг: signed Hilbert commutator против фактического diagonal slack.
4. Ответ4 проверен: на ker Lsrc (codim≤C m/L^5) floor −C L^10 log L; endpoint jets сохранены.
   При r≥2epsilon точный regular block положителен; остаётся actual Schur размерности≤C m/L^5.
   Ответ5 проверен: полный high-zero tail при T=mL² имеет norm≤3e6/sqrtL; старый jet-majorant убит.
   Endpoint-only блок точного Schur положителен; его coupling сохранён. Остался знак low off-line rows.
   Двусторонний sandwich даёт faithful Z(s)=L0(G_low+sI)^-1 L0*; Z(C_eta m^eta)≤I OPEN.
   Ответ6: fixed shifted-xi observation lift и gamma-neutralized positive kernel убиты в точной форме.
   Своя проверка: exceptional-only Hardy defect уже RH-equivalent; norm-transfer STALLED.
   Ответ7: blind packet gluing убит; доказана отрицательная дальняя корреляция actual arithmetic packets.
   Ответ8: Type-I часть оплачена; остаток O(m^1/4 polylog) — не floor, Type-II signed pairing OPEN.
   Ответ9: centered long-alpha component оплачена O(m^5/12 polylog); short-alpha/long-prime OPEN.
   Ответ10: wheel/powers-of-two оплачены; weighted even-shift aggregate STALLED.
   Rollover1: long-free collapse и quadrature проверены; subpolynomial TV остатка убит.
   Rollover8 проверен: весь convexity-loss tail ≤(18logQ+24)/sqrtQ; signed prime drift OPEN. Magnitude/convexity route STALLED; fixed-height pinning на shrinking windows не усиливает front-loading. Нужен source-specific lower bound.
   Доказательства: `SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md`, `HARDY_DEFECT_OWN_ATTEMPT_2026-10-06.md`.
Доказательства, один независимый проход и решение о смене фазы:
`../routeB_bus/source_observability_2026-09-28/NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md`.
Никаких предположений RH, positivity, polynomial gap или missing overlap.

## Прошка
По запросу владельца 06.10: конкретный U=min Rayleigh span{c(G),c(G'')} и нечётный secular sign
остаются OPEN. Для m=8 строго сертифицировано нечётное R<U; m=12,16 пока численные.
Конечный сертификат не опровергает хвост. Прошка дал явный нечётный upper envelope B_m,
e^(Cm/log m) B_m→0 для каждого C>0; сравнение U_m>B_m на неограниченной исходной семье OPEN.
Пакет, воспроизводимый probe и точный незакрытый шаг: `../routeB_bus/source_observability_2026-09-28/ODD_TRIAL_SIGN_2026-10-06.md`.
- Старый Missing T7 Lemma завершён **10/10**, новых вопросов туда нет. Нижний overlap не получен.
- [Proof of CCM Growth](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ac54396-d878-83eb-ae29-35d2bdd2262b): **10/10 получены и проверены; чат исчерпан**. SP OPEN. Forced rollover той же фазы; пакет `PROSHKA_GROWTH_ROLLOVER_PACK_2026-10-07.txt`, аудит `PARITY_PRIME_AUDIT_2026-10-06.md` в bus. Новый [Execute Multilinear Source Test](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac58a1c-1568-83ed-95d0-857526e2b6cb): **10/10 получены и проверены; чат исчерпан**. Proper-power signed drift имеет vanishing tail; mixed product convolution точно сокращается с forcing. Остался net prime-prefix correlation с полной предысторией; Stieltjes/Selberg и exact Mobius quadrature проверены: нового знака нет; correction меняет знак. Q10 joint pairing точно вернул исходную prime discrepancy с коэффициентом 1; STALLED. Новый чат **Execute Joint Probe Calculation**, Q1/10 получен и проверен: good-principal sector O_A(Z^-A), все subsets; exact nonprincipal remainder OPEN. Своя маска не равна дополнению. Q2/10 получен и проверен: exact common-lattice kernel, valuation-one cancellation только на (1,1), обязательные (2,2) terms; full tuple residue nonzero как integrand, не lower bound. Full low gain OPEN. Q3/10 получен и проверен: exact Mobius dispersion/CRT и coherent zero mode; entry-only diagonal3/32 неверна, cross-cofactors сохранены. Full signed gain OPEN; своя free-cofactor попытка проверена: termwise gain только e<Z3/32, cutoffZ1/4 не оплачен. Q4/10 получен и проверен: full double completion/parity switch; cubic-only fixed-S import убит, even covariance27/16 не full bound. Свой direct long-divisor sieve даёт cofactor RMS Z^-1/8 с actual local weights; полный outer triangle budget83/96 недостаточен. Q5/10 получен и проверен: полный periodic zero Gram имеет budget1/6; joint(H,f) даёт Type-II7/12, full low3/16 не улучшен. Следующий шаг — full completed A_m B_m^J pairing, все физические сектора вместе; Q6/10 получен и проверен: all-mark Euler cancellation, полный core/dual kernel и ramified Fourier projector; selfdual branch остаётся, full gain OPEN. Собственный полный resonance s=c,n=h² имеет O_B(Z^-B); остальные triples OPEN. Owner redirect: сначала ПРЯМОЙ импорт внешнего ZF78 в старые Q3 consumers. Условно проверены full CCM floor -m^(3/8+eps), Suzuki Psi_3/8>=0 и снижение tracking target до любого a>3/16; Linux сообщает успешный Comparator для zeta7/8, см. COMPARATOR_VERIFICATION.md и его границы доверия. См. DIRECT_Q3_THEOREM_TRANSFER.md; internal mixed-period ветка отложена; SHIFT_DESCENT_OWN_ATTEMPT.md: точный inverse shift проверен, bounded remainder не оплачивает знак, actual signed descent OPEN; Q7 не отправлен; новая фаза [Paper derivation estimate](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac647d1-c258-83ed-bf5b-fe98fe331ecf), Q1 получен и проверен14:04UTC: eta5/16 entropy tail и clipped-cell bracket; signed integral OPEN, компенсация возвращает коэффициент1; Q2 не отправлен; generic dual и strict-order Mellin не дали sign supplier (POSITIVE_SOURCE_DUAL_CONTROL.md, STRICT_ORDER_MELLIN_ATTEMPT.md); scalar descent отложен. Full CCM moment schedule проверен: old-block integral + new-mode M_p(C)+G_p, G_p>=0; Q_p не компенсирует prime slope jumps. FULL_CCM_MOMENT_SCHEDULE.md: CCM moment Q1 получен15:23UTC и проверен: полный background increment >=L/64 Pnew-5000/(mL)I; signed adaptive prime-pole correlation OPEN. CCM_MOMENT_Q01_CONCLUSION.md; своя CCM_SPECTRAL_COMMUTATION_ATTEMPT.md проверена: full-credit substitution возвращает delta moment; spectral gauge не оплачивает residual; Q2 получен16:32UTC и проверен: exact two-channel resolvent pairing, суммируемый truncation return при H=(m+1)²; central signed integral OPEN, floor без улучшения (CCM_MOMENT_Q02_CONCLUSION.md); своя Schur/spectral-averaging попытка проверена: старый спектр и two-sided jump сохранены, averaging возвращает endpoint moment без знака (CCM_SCHUR_SPECTRAL_ATTEMPT.md); Q3 получен08.10 01:28UTC и проверен: completed zero-residue return и summable tail2000 C_N M^-13/8; retained signed energy OPEN, floor без улучшения (CCM_MOMENT_Q03_CONCLUSION.md); свой physical-window transport проверен: edge leakage>=c/log m, zeroextension H1-energy infinite; signed adaptive form OPEN (CCM_PHYSICAL_WINDOW_TRANSPORT.md); Q4 получен08.10 и независимо проверен: boundary form PASS, bulk/SP OPEN; CCM_MOMENT_Q04_CONCLUSION.md. Own flat-direction extension PASS: full basis costs sqrt(d), k-direction return sqrt(k); no bulk gain (CCM_FLAT_DIRECTION_EXTENSION.md). Q5 получен17:30UTC, полностью прочитан и независимо PASS: short-source high moment и partial cyclic bound с НЕоценённым long remainder; полный floor/SP без улучшения. CCM_MOMENT_Q05_CONCLUSION.md; Own one-sided test независимо PASS: negative S moment эквивалентен positive actual V moment с paid short cost; synthetic m3/8 spike убивает generic-envelope closure. CCM_ONE_SIDED_LONG_MOMENT_TEST.md; Q6 получен и независимо проверен: unsigned total-variation budget KILLED(shape), signed moment OPEN; CCM_MOMENT_Q06_CONCLUSION.md. Свой restricted prime receiver проверен, верхняя prime spectral оценка OPEN; Q7 не отправлен; CCM_TRANSPORT_QUADRATURE_CONTROL.md: positive T6 charge не polylog даже при точной signed quadrature; actual Lambda block OPEN; CCM_RESTRICTED_FREQUENCY_TEST.md: projected high modes survive, Guth–Maynard large-values map insufficient; Q7 получен19:48UTC и независимо PASS: standalone atomic projected budget убит, joint Z_E/actual-W OPEN; CCM_MOMENT_Q07_CONCLUSION.md; Q8 получен и независимо PASS: полный joint return улучшен до O(m^(alpha+2beta)), отдельный composite sign C5/SP OPEN; CCM_MOMENT_Q08_CONCLUSION.md; собственные reflection/heat тесты независимо PASS: unrestricted atomic sign не переносится, полный Gaussian return o(1), compressed sign OPEN (CCM_COMPOSITE_REFLECTION_TEST.md, CCM_COMPOSITE_HEAT_RETURN.md); Q9 получен21:56UTC и независимо PASS: обе частотные части >=sqrt(m)/(16epsilon) на actual Pe0, отдельная negative-frequency плата убита; совместный знак C5/SP OPEN, auxiliary small-divisor claims не приняты (CCM_MOMENT_Q09_CONCLUSION.md); своя long-Mobius проверка независимо PASS: H_mu=D_prime-E_short, |E_short|<=(10+8|omega|)sqrt(R), H_mu эквивалентна RH; смена scalar representation без нового выигрыша (CCM_LONG_MOBIUS_PRIMITIVE_TEST.md); Q10 получен22:47UTC и независимо PASS: условная на ZF78 полная long-divisor оболочка O(m^(3/8)L²log(3L)), явные fixed constants и все возвраты; показатель3/8 не улучшен, c*epsilon/SP/RH OPEN (CCM_MOMENT_Q10_CONCLUSION.md); чат10/10 исчерпан, нового запроса нет; своя fixed-prime Gram проверка независимо PASS: D_s>=0, ||D_s||>=log(q)/(4pi²log m), polynomially-small compression return убит только в этой форме; полный q-resolvent сохраняет все степени до P, но positive-real identity не даёт верхнюю оценку signed shifted sum; этот shortcut STALLED, source-weighted знак OPEN (CCM_FIXED_PRIME_COMPRESSION_TEST.md); adaptive-weight alias return не нашёл mapped supplier, Laporta Thm1 требует недоказанную Delange-сходимость (CCM_ONE_SIDED_LONG_MOMENT_TEST.md); source-тест t=1/100000: P3-P7 независимо PASS условно на source lemmas; все d-бюджеты и low3/16−t/4 перенесены с явной оплатой rho(d), kappa_m=max(3/4,2beta*-1); principal B1-B7/C1 проверены в условном exact-identity интерфейсе (PRINCIPAL_BOX_PERTURBATION.md). PERTURBED_HIGH_TRANSPORT.md H1-H7 независимо проверяет полный условный перенос: exact identity, clipped counts, nonprincipal high и общий порядок, m0=758303/8812800000>0. Source Q7/10 получен09.10 около00:14UTC, полный оригинал прочитан; независимые проверки условного kappa>=2/3 возврата и полного budget frontier PASS. Предел fixed-b после возврата .87495715035054, free-b .87495701942010; итерация настройки STALLED, не impossibility actual probe. Следующий вход — inverse moment gain Q7(44) около r=1.1234 с переносом(45); sparse-image off-diagonal(47) и все scale/profile returns OPEN. SOURCE_Q07_CONCLUSION.md; own SPARSE_AMPLIFIER_MASK_TEST.md A1–A4 независимо PASS: a-average лишь маска w_P(nn′), не новая фаза; full sparse supremum A4 OPEN; A5–A6 reverse identity независимо PASS: E_sup и P*B эквивалентны до P^epsilon, без нового gain (после Q8, не отправлено). Source Q8/10 получен09.10 01:16UTC, полный оригинал прочитан; независимые аудиты PASS: conditional large-gcd gain G^-5/6 и малые масштабы оплачены, exact cubic-Gauss kernel/tails и full return проверены. Остался Q8(32): small-gcd верхнемасштабная signed correlation(24), OPEN; SOURCE_Q08_CONCLUSION.md. Own Q08_DUAL_ROW_CANONICAL_TEST.md D1–D4 независимо PASS: canonical Gauss import и f² repair не проходят width; joint centered supplier OPEN. Source Q9/10 получен и независимо проверен: formal diagonal exact zero, double return coefficient1; auxiliary long-divisor tail условно оплачен. SOURCE_Q09_CONCLUSION.md; root4435 finite checks PASS. Q8(32)/Q9(37) OPEN; свой Q09_INTEGRATED_SIEVE_RETURN.md I1–I5 независимо PASS: infinite t-tail нулевой после полного интеграла, exact reciprocal-zeta replacement; individual FE removes Gauss phase but no gain. Gao–Zhao first-moment pair mapping missing; next joint Euler-corrected estimate, Q10 не отправлен. sigma_t=7/8−1/400000 не принят как безусловная новая граница; собственный sparse-band receiver независимо PASS: любой фиксированный M=m^alpha, 0<alpha<1, сохраняет off-critical witness на исходной K_m; prime top bound OPEN (CCM_SPARSE_BAND_RECEIVER.md); вывод: `../literature/openai_math_2026-10-07/Q06_OWN_CONCLUSION.md`; состояние: `../literature/openai_math_2026-10-07/PROSHKA_PENDING.md`. Alias-return OpenAI 722 manuscripts: `../literature/openai_math_2026-10-07/REPORT.md`; scalar compensation проверена: возвращает unselected source + boundary; fixed low estimate упирается в 7/8. `PARAMETER_BUDGET.md`: старый relaxed барьер5/6 не full low: Q7 с rho даёт минимум13/15; раньше него high frontier около.874957, нужен новый joint estimate. RH/SP OPEN; 7/8 не закрывает RH.
- Owner Ramanujan/density test: `../literature/openai_math_2026-10-07/CCM_DENSITY_PAIRING_TEST.md`, independent PASS: exact full-source pairs; positive derivative-cost certificate too large; square Ramanujan density matches large primes and has controlled smooth upper-block quadrature for R²<=log(m)/8. Sparse-band extension independently PASS: R=m^beta allowed when alpha+2beta<1, model error O_T(m^-T); C_R=log R+O(1) (CCM_SPARSE_RAMANUJAN_QUADRATURE.md). Full smooth density term independently bounded <=16 by fixed-P rank-two differentiation (CCM_LOG_DENSITY_CANCELLATION.md); full quadrature improved in Q8 to O(m^(alpha+2beta)), endpoints included (CCM_MOMENT_Q08_CONCLUSION.md; prior CCM_FULL_RAMANUJAN_RETURN.md); small arguments and proper powers paid; exact D_R=small+powers-C_comp, lower composite bound OPEN (CCM_COMPOSITE_SIGN_TARGET.md), no SP gain.
- Открытые вопросы, убитое и текущий фронт — только в `PAPER_CHAIN.md` (здесь не дублировать).

## Правила работы (владелец, 2026-09-28)
Для этого репо сильнее глобальных правил Codex (`~/.codex/AGENTS.md` §§3, 5, 6, 9) и старого control.
1. Вопрос Прошке — рабочее сообщение, не outbound artifact: без review-цикла, без записей
   intent / dispatch / confirm / receipt. Один коммит на вопрос — после ответа: запрос + ответ + вывод вместе.
2. Сито перед вопросом: своя попытка уже сделана; вопрос называет звено `PAPER_CHAIN` и какой ответ
   изменит план; не повторяет убитое. Пока ответ не отработан — следующего вопроса по тому же звену нет.
3. Одна линия атаки — механизм из «Текущий фронт» в `PAPER_CHAIN`. Смена механизма — только после
   записанного убийства или тупика (одной строкой в «Убито»).
4. Независимая проверка (один проход) — только для вывода, который меняет статус звена (закрыто/убито).
5. Размеры: `PAPER_CHAIN.md` ≤ 200 строк, `NEXT.md` ≤ 120, запись в `PROSHKA_QUEUE.md` ≤ 5 строк.
   SHA, ID ходов, пути ревьюеров — только в файле ответа в bus. `AGENTS_LEDGER` и состояния
   prepared/attempted/observed/… не вести.
6. Бухгалтерия, которая не меняет математику, — не делать. Сомневаешься — спроси владельца одной строкой.

## Не повторять
- Сверка 06.10: мост projected trial→Ξ на |Im z|<1/2 уже записан условно на принятое PAPER HMODE; проверен source crosswalk, не свежая Lean-сборка. См. `../routeB_bus/source_observability_2026-09-28/CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md`; ground tracking G3 остаётся открыт.
- Owner recovery, старые launch/ingest/publication (RESUME `Do not repeat`) — не переигрывать.
- Не подменять оценки selected Ferrers packet явными гауссовыми пределами; не дифференцировать C0-сходимость.
- Не отправлять повторно уже отправленные запросы Прошке.

## Конец фазы
конец фазы = scripts/phase_end.sh
Одна команда: `scripts/phase_end.sh "что сделано"` (журнал → Lean-проверка → полка → литература → статистика → commit → push → readback).
Перед ней дописать в `docs/Progress_Log.md` запись `## <дата> — <что нашли>` с полями:
Развилка · Выбрали · Почему · Что отвергли · Инсайты · Блокеры · Иглы Зингера · Следующий ход · Адреса · Чей вердикт.
Без записи скрипт останавливается; обход владельца: `--no-log`.
Литература: скрипт сам ищет arXiv/Crossref и X (посты, новости) по строкам `- lit:`.
Агент (Claude Code) в конце фазы дополнительно прогоняет те же запросы через scite `search_literature`
и Consensus `search` и сохраняет находки в `docs/literature/scan_<дата>_agent.md` (заголовок, DOI, цитата, зачем нам).
Запросы для поиска литературы (правьте по текущему фронту):
- lit: prolate spheroidal wave functions Riemann xi zeros
- lit: Ferrers functions Sturm-Liouville eigenvalue asymptotics uniform
- lit: Fokas unified transform Riemann zeta
- lit: Hurwitz theorem zeros real entire functions locally uniform limit

## Жёсткие линии (не обсуждаются)
Без `sorry`; без собственных `axiom`; только три стандартные аксиомы Lean (см. Цель п.2);
недоказанное не называть доказанным; claim — только по условиям из «Цели»;
одновременно работает одна машина (какая — решает владелец).
