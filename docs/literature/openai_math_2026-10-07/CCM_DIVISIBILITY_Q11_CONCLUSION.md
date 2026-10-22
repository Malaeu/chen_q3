# Q11: точный перенос построен; семейство раздельных бюджетов отсечено

2026-10-22. Исходная полная CCM; bounded PAPER audit, не Lean.

## Получение и воспроизведение

После одного явно разрешённого владельцем повтора Q11 завершился естественно:
Worked for36m29s, Response complete, 19:35UTC. Stop не нажимался.
Полный оригинал PROSHKA_CCM_DIVISIBILITY_ENERGY_TRANSFER_Q11_VERDICT_2026-10-22.md
прочитан и побайтно совпадает с Downloads: 86560bytes,1217LF,
SHA256 76fab7238da767d1e54f2d254932f0664bb670596f0d9adaa7f99629f04e34b7.
Запрос:155127bytes,2513LF,
SHA256 195b50976e9683815d0e98e6f3719efdd91218ef77c951a6f790057a6b34fcda,
SOURCE_HEAD e008fc963e751c0b9ddb7054066b039597642e0c; все9 тел/хешей совпали.

Root извлёк неизменённые Python/registration/expected JSON и воспроизвёл
3027 точных контролей в ccm_divisibility_q11_checks. exact_results.json
семантически совпадает с expected_results.json, включая хеши кода и регистрации.
Исходное independent_review=NOT_RUN сохранено: это статус авторского запуска.
Последующий независимый readonly q11_verdict_audit: bounded PAPER PASS §§2–9,
существенных дефектов не найдено. Проверены целые m, край d=m, uniform fixed
 epsilon/A, обе диагонали невидимых рёбер, constant144 и исходный P.
Уточнение §9: поля v_n продолжить нулём вне [0,L]; f там нуль, активная форма
не меняется. Оригинальный файл не исправлялся. Upstream receiver принят как
вход, не переаудирован целиком. Lean/Arb/спектр полной CCM: новых запусков0.

## Проверенная математика и точный scope

Для a_d=Lambda(d)/sqrt(d), W=sum_{2<=d<m}a_d и r_f(h)=integral conj(f(t))f(t+h):

 S[f]=2 Re sum a_d r_f(log d).

Whole-function lift (J_v f)_n(u)=v_n f(u+log n), sum||v_n||²=1,
сохраняет физическую L2-норму точно. Это не старый sampling lift.
При kappa_d=sum_n <v_n,v_nd> исходный оператор возвращается полностью:

 S[f]=delta_v||f||²-E_v[f]+R_v[f], E_v>=0,
 |R_v[f]|<=r_m(v)||f||², r_m(v)=2 sum a_d|1-kappa_d|.

Все простые степени и смешанные члены сохранены. При d>=m нет физического
перекрытия, но обе графовые диагонали остаются в E_v и delta_v.
Ключевой результат — точная цена всего семейства сертификатов:

 delta_v+r_m(v)-2W
 = E_{<m}(v)+D_{>=m}(v)
   +2 sum a_d(|1-kappa_d|+Re(kappa_d)-1) >= 0.

При N=1 достигается равенство. Поэтому inf_{N,v}(delta_v+r_m(v))=2W,
асимптотически 4sqrt(m) по PNT. Увеличение графа и подбор постоянного профиля
не улучшают степень этого способа: отбросить E_v и отдельно оплатить |R_v|.
Это НЕ нижняя граница S, T_{>R} или спектра CCM и НЕ запрет всех переносов.

Совместная делительная обязанность sum Lambda(d)|kappa_d|²<=sum log(n)||v_n||²
верна и для Hilbert-valued профилей. Полный divisor box действительно даёт
r_m<=144 при K=ceil(sqrt(m)), но delta_v имеет порядок m^(3/2).
Следовательно малая ошибка сама по себе ничего не оплачивает.
На исходном P полный остаток имеет оба знака при N<=m^A: сигнал >=c/log²N.
Это исключает бесплатное объявление остатка неположительным, но не subpower
upper bound. Позиционно зависимые поля также сохраняют норму; incoming
inequality верна a.e. Буквальное восстановление всех рёбер снова дорого;
aggregate one-sided comparisons этим не исключены.

Полный безусловный возврат остаётся S<=2W P<=12sqrt(m)P.
T_{>R} получает малоделительный возврат один раз; K получает arch fee.
Q03 conditional3/8 на ZF78 не улучшен и не стал безусловным.
eta(epsilon)->0, SP, G1/G3, RH: OPEN. CF22/PySR: PARKED_REOPENABLE.

## Откат и продолжение goal

Откат до раздельной оплаты R_v и отбрасывания E_v, а также до требования
точного совпадения каждого ребра. Не оптимизировать N,v в исключённом
семействе и не отправлять автоматический Q12 с переименованным R_v-E_v.
Условие R_v-E_v<=нужный бюджет само эквивалентно прежней трудности.

Следующий bounded discriminator: прежде чем выбирать новый перенос,
проверить, может ли зависимость профиля от положения менять именно
сжатую совместную форму на исходном P без требования kappa_d(t)=1
порёберно. Вход — полная identity §9; стоимость обеих диагоналей и всего
остатка обязательна. Успех — количественная оценка совместной формы,
не новая запись identity; неудача — точное препятствие выбранному классу.
Сначала проверена полка: ask.sh --defer-external 'CCM divisibility energy
aggregate projection' вернул INCOMPLETE (q3_docs freshness failure),
kb.py search divisibility — no hits. Это не отсутствие поставщика во всём
репозитории; индекс не ремонтировался в этом цикле. Перед выбором класса
нужна адресная сверка уже имеющихся projected Mellin и rank-two тестов,
чтобы не повторить projection-only shortcut. Новая оценка не объявлена.

CLOSES: Q11 response intake/reproduction/audit; cap-plus-absolute-return
certificate family excluded as a source of sub-half-power improvement.
OPENS: source-aware aggregate comparison on original P; quantitative input absent.
AUTOPSY: dropped=COUPLING; note=Discarding graph energy and separately bounding the full defect restores the old half-power budget.
Native goal last observed blocked; API has no resume operation. Owner explicitly
resumed scoped work; mathematical objective remains unachieved, not complete.
No Q12 sent. Full original, controls and local sampling discriminator retained.
