# STATUS: TRY_MOCK_MODULAR_THETA_SHADOW_RETURN

```yaml
OPERATIVE_CLASS: TRY_MOCK_MODULAR_THETA_SHADOW_RETURN
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_REQUEST_FOR_RAMANUJAN_STYLE_COMPLETION
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_COMMIT: 70662bc531e7b90158cf7d0fd3dc415f3bd927eb
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PASSIVE_SECTION_KINK_BUDGET_2026-11-03.md
SOURCE_BLOB: d00a55c75448d0bf4d4da4aceb24a3b37f8fef2f
SOURCE_SHA256: f079197e61b57b2e3cf8c36f6cfed35b95912f7efc6691d938eb7f64ae7759a9
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
ACTUAL_MOCK_OBJECT: ZAGIER_HURWITZ_CLASS_NUMBER_SERIES_WEIGHT_3_OVER_2
IS_ORIGINAL_RAMANUJAN_MOCK_THETA: false
COMPLETION: EXPLICIT_NONHOLOMORPHIC_INCOMPLETE_GAMMA_SERIES
SOURCE_RETURN: SHADOW_TO_THETA_TO_XI_TO_LOG_DERIVATIVE_TO_INVERSE_LAPLACE
DIRECT_EQUALITY_G_EQUALS_MOCK_FORM: NOT_CLAIMED
FIXED_SHADOW_HOLOMORPHIC_ADDITION_CHANGES_G: false
NEW_PASSIVITY_OR_RH_PROOF: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
VERIFIER: PAPER
IMPORTED_MODULARITY: THEOREM_ZAGIER_NOT_REPROVED
NUMERICAL_PRECISIONS: [45, 65]
NUMERICS: DIAGNOSTIC_NOT_INTERVAL_CERTIFICATION
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_EXECUTED: false
ROUTE_STATE_CHANGED: false
```

## 0. Что именно сделано

Ы. Построено точное представление нашей пружины через настоящую mock-модулярную форму с явной добавкой. Выбрана не произвольная исходная mock-тета-функция Рамануджана, а форма Загира веса 3/2: ее тень является ровно тета-функцией, из которой получается исходная zeta.

Это НЕ равенство g(t)=H(t)+R(t). Переменные, аналитические классы и операции различны. Точный возврат нелокален и содержит логарифмическую производную. Полученная цепочка сохраняет gamma-фактор, полюсы и все prime powers; она не дает нового знака (P).

Важный результат попытки: добавление любой допустимой голоморфной формы при фиксированной тени НЕ МЕНЯЕТ g. Нельзя настроить знак исходной пружины таким свободным добавлением. Это ограничение данного shadow-based представления, а не запрет иных theta-lifts или всей mock-модулярной техники.

## 1. Источники, конвенции и импорты

R0. Полный локальный файл источника, указанный в header, имеет 41902 bytes; SHA-256 и Git blob пересчитаны и совпали с закрепленным удаленным blob. Прочитаны полная форменная нормировка и различие source/Schur/inverse-kinks. Новый результат не использует положительный сертификат log(3) как предпосылку.

P1. S. Zwegers, Mock Theta Functions, thesis, arXiv:0807.4834. Использован abstract для точного смысла completion: holomorphic mock part плюс nonholomorphic theta-period. Не импортируется theorem о нашей g.

P2. D. Zagier, Nombres de classes et formes modulaires de poids 3/2, C. R. Acad. Sci. Paris A 281 (1975), 883--886, Theorem 2 на p.884. Первичный скан p.883--884 прочитан визуально. Он поставляет модульное преобразование используемой completion.

P3. K. Bringmann, S. Ehlen, M. Schwagenscheidt, On the modular completion of certain generating functions, arXiv:1804.07589v1, Example 2.3(i), eq.(2.4), p.7. Сверены коэффициенты и shadow -theta/(16*pi). PDF-текст прочитан; web-screenshot этой страницы вернул Cache miss. Первичная формула P2 независимо просмотрена, и ее нормировка переведена ниже.

P4. M. Suzuki, arXiv:2206.03682v4, eqs.(1.1)--(1.8), Theorem 1.1. Первые две страницы PDF просмотрены скриншотами. Арифметическое определение и transform identity импортируются как THEOREM; положительная Hilbert-реализация НЕ импортируется без RH.

P5. DLMF 25.4: стандартная нормировка xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2. Theta-Mellin identity ниже выводится непосредственно.

URLs:
```text
https://arxiv.org/abs/0807.4834
https://people.mpim-bonn.mpg.de/zagier/files/scanned/NombresDeClassesEtFormesModulaires/fulltext.pdf
https://arxiv.org/pdf/1804.07589v1
https://arxiv.org/pdf/2206.03682v4
https://dlmf.nist.gov/25.4
```

Различаем: tau=x+iy, y>0 — модулярная переменная; q=exp(2*pi*i*tau); s — Mellin-переменная xi; u — Laplace-переменная, Re u>1/2; t — физическая логарифмическая координата пружины. Модулярный y не является длиной окна L. Исходные N=m, L=log(m), физическая L2-метрика не меняются.

## 2. Настоящая mock-форма и явная добавка

**[ABSTRACT | PAPER; A/I/F; modularity THEOREM P2.]** Пусть H(n) — числа классов Гурвица: взвешенное число SL2(Z)-классов положительно определенных целочисленных бинарных квадратичных форм дискриминанта -n, с обычными весами автоморфизмов. Непримитивные формы включены. H(0)=-1/12 и H(n)=0 при n=1,2 mod 4.

Определим

    Hplus(tau) = -1/12 + sum_(n>=1) H(n) q^n
               = -1/12 + q^3/3 + q^4/2 + q^7 + q^8 + ... .       (1)

Нужная добавка не подбирается по спектру:

    R(tau) = 1/(8*pi*sqrt(y))
       + 1/(4*sqrt(pi)) sum_(n>=1)
           n Gamma(-1/2,4*pi*n^2*y) q^(-n^2).                   (2)

Здесь Gamma(a,v)=integral_v^infinity exp(-r) r^(a-1) dr; ее аргумент v>0. Завершение

    Hhat(tau) = Hplus(tau)+R(tau)                               (3)

является гармонической формой Маасса веса 3/2 на Gamma_0(4), с соответствующим полувесовым множителем. Это теорема Загира, не новый результат и не одна из первоначальных функций Рамануджана веса 1/2.

Нормировка из первичного P2: beta(v)=(16*pi)^-1 integral_1^infinity r^(-3/2)exp(-vr)dr, и R=y^(-1/2)sum_(n in Z)beta(4*pi*n^2*y)q^(-n^2). Нулевой член дает 1/(8*pi*sqrt(y)); объединение n и -n дает (2).

Для y>=y0>0 ряд (2) и нужные производные сходятся локально равномерно. Например, модуль n-го ненулевого члена не превосходит

    exp(-2*pi*n^2*y)/(32*pi^2*n^2*y^(3/2)).                     (4)

Это следует из Gamma(-1/2,v)<=v^(-3/2)exp(-v). Полный хвост после N ограничен геометрической суммой с отношением не больше exp(-2*pi*(2N+3)*y). Поэтому операции с рядом не формальны.

## 3. Тень: точный коэффициент и связь с геометрией целых

Чтобы не путать с римановой xi, обозначим оператор Bruinier--Funke через D_k:

    D_k F(tau)=2i*y^k*conjugate(partial F / partial conjugate(tau)).

Он антилинеен. Непосредственно из (2):

    D_(3/2) Hhat = -theta/(16*pi),
    theta(tau)=sum_(n in Z)q^(n^2).                           (5)

**Доказательство [ABSTRACT | PAPER; A/LA].** Голоморфная часть исчезает. Производная нулевого члена R дает -1/(16*pi). При B=4*pi*n^2,

    d/dy Gamma(-1/2,By)=-B^(-1/2)y^(-3/2)exp(-By).

После умножения на n/(4*sqrt(pi)), сопряжения и 2i*y^(3/2) n-й член дает -q^(n^2)/(8*pi). Сумма есть (5). Локальная равномерная сходимость оправдана (4).

Таким образом, геометрическая информация находится не в произвольной аналогии: H(n) считает бинарные формы, а theta считает точки одномерной целой решетки. Но знак Schur-ядра пока не следует ни из одного из этих двух подсчетов.

## 4. Полный возврат к той же xi и к той же пружине

**[ABSTRACT | PAPER; F/I/A, E на возврате логарифмической производной.]** Из completion извлечем

    Theta_H(X)=-16*pi*(D_(3/2)Hhat)(iX/2)
             =sum_(n in Z)exp(-pi*n^2*X),   X>0.             (6)

Фактор 1/2 в iX/2 обязателен из-за q=exp(2*pi*i*tau).

Для Re s>1 можно интегрировать положительно/абсолютно сходящийся ряд:

    (1/2) integral_0^infinity (Theta_H(X)-1) X^(s/2-1)dX
       =pi^(-s/2)Gamma(s/2)zeta(s).                         (7)

Это term-by-term integral каждого exp(-pi*n^2*X). Poisson identity дает Theta_H(X)=X^(-1/2)Theta_H(1/X). Разделение (7) при X=1 поэтому дает целую функцию

    X_H(s)=1/2 + s(s-1)/4 * integral_1^infinity
          (Theta_H(X)-1)[X^(s/2)+X^((1-s)/2)]dX/X
          =xi(s).                                         (8)

Интеграл справа локально равномерно сходится для всех комплексных s благодаря экспоненциальному убыванию theta-tail. На Re s>1 равенство проверено из (7), затем продолжается аналитически. Константа 1/2 и s(s-1) сохраняют нормировку и полюсную компенсацию.

Теперь при Re u>1/2:

    integral_0^infinity g_zeta(t) exp(-u*t)dt
       =-X_H'(1/2+u)/(u^2 X_H(1/2+u)).                    (9)

Это P4,(1.2), с g=-Psi. В частности, для t>0 и любого c>1/2:

    g_zeta(t)= -1/(2*pi*i) integral_(c-i*infinity)^(c+i*infinity)
          exp(u*t) X_H'(1/2+u)/(u^2 X_H(1/2+u)) du.        (10)

На этой вертикали X_H не имеет нулей: аргумент zeta имеет вещественную часть >1. Логарифмическая производная растет не быстрее O(log(2+|u|)); после деления на u^2 интеграл абсолютно сходится. (10) возвращает исходную непрерывную g, затем используем четное продолжение. Никакого перехода через неизвестные нули здесь нет.

Таким образом, точное представление задачи:

    Hplus + R -> D_(3/2) -> theta -> Mellin xi
              -> logarithmic derivative -> inverse Laplace g -> K_g. (11)

Это доказанное равенство объектов, но НЕ положительно-сохраняющий фактор и НЕ изометрия норм. Оно не заменяет окно theta-пространством.

Проверка всех арифметических частей на Re s>1:

    X_H'(s)/X_H(s)
       =1/s+1/(s-1)-log(pi)/2+psi(s/2)/2
          -sum_(n>=2)Lambda(n)n^(-s).                     (12)

Поэтому полюсы, gamma и все prime powers в (9)--(10) сохранены. Добавлять gamma/pole terms второй раз после (12) было бы двойным учетом. После возврата g производные меры mu_f с endpoint-массами и исходные A_m остаются теми же.

## 5. Что получилось при попытке добавить свободную поправку

### 5.1. Фиксированная тень: строгая невидимость голоморфных добавок

**Лемма [ABSTRACT | PAPER; A/LA].** Пусть F голоморфна на верхней полуплоскости. Тогда

    D_(3/2)(Hhat+F)=D_(3/2)Hhat.                            (13)

Следовательно, вся цепочка (6)--(11) дает ТОЧНО ТЕ ЖЕ xi, g, K_g и дополнения Шура. Если нужно сохранить модульное преобразование, F дополнительно берется из допустимого пространства голоморфных/слабо голоморфных форм того же веса и множителя. Сам вывод (13) не требует модульности F.

Доказательство: partial_bar F=0; применить определения. Обратно, две C1-completion с одинаковой тенью отличаются голоморфной функцией. Значит, это весь класс свободных поправок с фиксированной тенью.

Нельзя превратить данный bridge в новый знак посредством подгонки Hplus. Более того, оператор D_(3/2) уничтожает всю Hplus: пока используется только этот bridge, ее числа классов не участвуют в новом неравенстве. Для настоящего выигрыша потребовалось бы использовать дополнительную структуру ПОЛНОЙ Hhat в другом доказанном source-return, не просто применить тень.

### 5.2. Прямая подстановка g(t)=Hhat(tau(t)) не работает

**[ABSTRACT | PAPER; A/E/I; obstruction only to this theorem-shape.]** Hhat вещественно-аналитична внутри верхней полуплоскости. Ее композиция с аналитической кривой tau(t), остающейся внутри, и гладкими аналитическими нормировками вещественно-аналитична. Но у полного g_zeta

    g'_+(log(p^k))-g'_-(log(p^k))=log(p)/p^(k/2)>0.        (14)

Поэтому непосредственное равенство g с таким interior restriction невозможно. Это не запрет интегральных преобразований, негладких обратных преобразований или граничных значений. Наш (10) как раз использует разрешенный нелокальный возврат.

### 5.3. Модулярность не есть положительность

Форма (3) вполне может иметь отрицательные значения: при y->infinity,

    Hhat(iy)=-1/12+1/(8*pi*sqrt(y))+O(exp(-2*pi*y)) -> -1/12.

Это не контрпример (P), а предупреждение, что modular completion не является общим positive-kernel projector.

Если вместо представления изменить сам источник, g_new=g+r, то

    K_g=K_(g+r)-K_r.                                      (15)

Положительность K_(g+r) не доказывает положительность K_g без контроля вычитаемой K_r. Нельзя назвать неизвестную коррекцию shadow и тем самым оплатить ее знак.

## 6. Судьи: исходная RH-ветка и посаженная четверка

**RH-ветка [COFINAL_FAMILY | CONDITIONAL; A/LA].** Если RH верна, возвращенное из (11) ядро имеет прежнюю положительную нулевую Gram-реализацию. Новый положительный делительный lift или растущий внешний множитель не введены. Это точное прохождение условного судьи, не доказательство его предпосылки.

**w-мир [COFINAL_FAMILY | PAPER for defined control, with positive baseline; A/LA].** Пусть Xi_0(z)=xi_0(1/2-iz) — положительный чисто точечный baseline, и

    P_w(z)=[(z^2-w^2)(z^2-conjugate(w)^2)]^nu,
    w=gamma+i*eta, gamma=2*pi/log(2), 0<eta<1/2.

Нормировка

    xi_w(s)=xi_0(s)*P_w(i*(s-1/2))/P_w(i/2)

сохраняет отражение s->1-s, вещественный тип и значения при s=0,1, если они были нормированы у baseline. Однако ее logarithmic derivative получает ненулевую добавку и

    g_w(t)-g_0(t)=4nu Re[(cos(w*t)-1)/w^2].                 (16)

При L_k=k log(2), a_w=Re(1/w^2)>0 и S0=sum nu_gamma/gamma^2:

    2Psi_w(L_k)<=4S0-8nu*a_w[cosh(eta*L_k)-1] -> -infinity. (17)

Один достаточно малый фиксированный старый узел имеет положительный Gram благодаря неизмененному ведущему локальному h log(1/h). Его Schur-остаток не превосходит отрицательной новой диагонали (17).

Этот мир НЕ может быть получен из той же тени theta путем свободной голоморфной добавки: лемма (13) тогда сохранила бы g_0, а не (16). Объявлять unchanged Hhat моделью w-мира было бы нарушением source-matching. С другой стороны, одни симметрия, целость и нормировка xi сами проходят w-контроль и не дают (P). Новый mock-объект не устраняет этот тест.

## 7. Что остается недоказанным и две допустимые формы дальнейшего представления

Нужный источник-согласованный Weyl-объект после (11):

    Q_H(z)=i X_H'(1/2-iz)/X_H(1/2-iz)=Q_zeta(z).           (18)

Его голоморфность и Herglotz-положительность во всей верхней полуплоскости не следуют из теоремы о (3). Доказательство такого свойства дало бы исходный знак. Оно здесь не получено. Постановка (P) и source comparison C-V T_delta^-1 V*>=0 остаются прежними.

| Представление | Что сохраняет | Дискриминатор / сила / цена |
|---|---|---|
| Полная Hhat в automorphic/theta pairing, а не только ее тень | Возможную дополнительную геометрию классов | Требуется точное равенство исходной W[f] и нового pairing с доказанным знаком; сила высокая, аналитическая цена высокая; пока только кандидат |
| Нативное Mellin completion (12), затем source-first Weyl-kernel | Все точные Lambda, gamma, полюсы | Проверка Herglotz-знака и planted poles; цена проверки низкая, положительный глобальный supplier отсутствует |

Это две формы представления одной цели, а не список новых обязательных подзадач. Не объявляется существование уже построенного positive theta-lift.

DISCRIMINATOR: для любой заявленной положительной модели сравнивать ее Weyl-функцию с (18), включая нормировку, полюсы и gamma-член. При нуль-согласованном конечном sign-test нужен точный положительный фактор/сертифицированный нижний envelope; увеличение dps не заменяет глобальный квантор. В w-мире локальная точка около planted pole или (17) должна давать отрицательный контроль.

## 8. Проверки и судьба предрегистрации

До исполнения записаны M1--M5; исходная запись и код ниже сохранены в этом одном файле. 45/65 dps — floating diagnostics, НЕ интервальная сертификация.

- M1 CONFIRMED: shadow коэффициент, включая нулевой член; ошибка при 65 dps <3.72e-68.
- M2 CONFIRMED: generator tau->tau/(4tau+1) с множителем (4tau+1)^(3/2); относительная ошибка <1.49e-66 на трех точках. Полная теорема модульности импортирована из P2, а не доказана тремя точками.
- M3 CONFIRMED: xi и ее logarithmic derivative из разрезанного Mellin-integral; ошибки <1.40e-66 на четырех тестовых параметрах.
- M4 CONFIRMED: holomorphic gauge не меняет shadow; проверка добавкой q. q здесь тест голоморфности, НЕ заявленный модулярный элемент того же веса.
- M5 CONFIRMED: сумма всех Lambda(n)n^(-s), n<=4096, при s=3.5+1.25i; ошибка 3.3069620964e-10 меньше независимой границы 3.2476209726e-9. Хвост оценен через integral_N^infinity log(x)x^(-Re s)dx.

Прямая inverse-Laplace численно не интегрировалась. Ее source-return доказан аналитически из (8)--(12) и THEOREM P4. (P), полные CCM-спектры, интервальная инерция, Lean не проверялись. Никакого независимого агента-аудитора не было.

## 9. K8A, closeout и запись в репозиторий

DOWNSTREAM_CONSUMER: исходная пассивность (P) / source-matched Herglotz-класс.
ACTUAL_CONSUMER_REQUIREMENT: глобальный односторонний знак, а не только функциональное уравнение.
ORIGINAL_REQUESTED_OBJECT: mock-функция с добавкой, сохраняющая исходную пружину.
ORIGINAL_OBJECT_IS: NOT_NECESSARY для consumer; здесь получено точное нелокальное представление через (3).
KNOWN_WEAKER_INTERFACES: любой прямой исходный Schur-знак либо прежний достаточный нижний пол.
FAILURE_TYPE: NO_DERIVATION для нового положительного знака.
EPISTEMIC_STATUS: RESEARCH_DEBT для (P); никакой route-family death.
REOPEN_TRIGGER: положительное pairing полной Hhat с точным возвратом исходной формы и бюджетом всех correction terms.
NOVELTY_AXIS: новая для данного батча явная mock-packaging и проверка ее невидимого holomorphic freedom; известная теория Загира не выдается за новую.

Что стало точнее: конкретная completion (2) и точная нормировка возврата (11) вместо свободной добавки. Что исключено: прямое отождествление негладкой g с interior mock-form; настройка g через holomorphic addition при фиксированной тени. Область обоих препятствий — указанные THEOREM_SHAPES, не вся mock-техника. Глобальный арифметический знак не продвинут.

MEMORY: target=PASSIVE_SECTION_P; operator=REPRESENTATION_SHIFT; result=REPRESENTATION_PROGRESS; invariant=source-return must include shadow/Mellin/log-derivative and all poles; forbidden_move=call modular completion a positivity certificate or tune holomorphic part at fixed shadow to change g; next_decisive_test=full-form positive pairing with exact source-matching, not another shadow identity.

Одна CODEX DIRECTIVE: проверить (2),(5),(8)--(13) и область obstruction (14) как единый source-return; не повышать статус (P) после подтверждения формул.

Запись: только docs/routeB_bus/proshka/PROSHKA_VERDICT_RAMANUJAN_MOCK_COMPLETION_2026-11-03.md, ветка proshka_inbox_2026-10-31. Предыдущие вердикты и route-state не редактируются. Commit SHA сообщается после удаленной записи и проверки в ответе; сам файл не содержит рекурсивный SHA собственного коммита. Lean-файлов нет, ожидаемый axiom profile неприменим.

### Повтор вычислений

WORKDIR: корень репозитория. Извлечь единственные блоки после BEGIN_REGISTRATION и BEGIN_REPLAY в одну временную папку и исполнить check.py через uv; положительный вывод меняет только статус воспроизведения нормировок, НЕ (P).

```bash
uv run --with mpmath python - <<'PY'
from pathlib import Path
import re, subprocess, sys, tempfile
p = Path('docs/routeB_bus/proshka/PROSHKA_VERDICT_RAMANUJAN_MOCK_COMPLETION_2026-11-03.md')
t = p.read_text()
r = Path(tempfile.mkdtemp(prefix='mock-return-'))
for marker, lang, name in [('BEGIN_REGISTRATION','json','registration.json'), ('BEGIN_REPLAY','python','check.py')]:
    match = re.search(r'<!-- '+marker+r' -->\s*```'+lang+r'\n(.*?)\n```', t, re.S)
    if match is None:
        raise RuntimeError('Missing replay block: '+marker)
    (r/name).write_text(match.group(1)+'\n')
subprocess.run([sys.executable, str(r/'check.py')], check=True)
PY
```

## 10. Предрегистрация и полный replay-код

<!-- BEGIN_REGISTRATION -->
```json
{
  "task":"RAMANUJAN_MOCK_COMPLETION_SOURCE_RETURN",
  "registered_before_tests":true,
  "predictions":[
    {"id":"M1","claim":"Finite nonholomorphic correction has shadow -(1+2*sum(q^(n*n)))/(16*pi), including the constant mode."},
    {"id":"M2","claim":"The complete Zagier series satisfies the Gamma0(4) generator tau -> tau/(4*tau+1) with the weight 3/2 factor."},
    {"id":"M3","claim":"The split theta Mellin integral reconstructs xi(s) and xi'(s)/xi(s), including the gamma and pole terms."},
    {"id":"M4","claim":"Adding a holomorphic function does not change the extracted shadow; this is not a positivity gain."},
    {"id":"M5","claim":"The right-half-plane log derivative reproduces the full von Mangoldt sum within the explicit truncation tail."}
  ],
  "sign_claim":"NONE",
  "numerics":"DIAGNOSTIC_NOT_INTERVAL_CERTIFICATION"
}
```

<!-- BEGIN_REPLAY -->
```python
"""Normalization diagnostics only; not interval or RH certification.
Run: uv run --with mpmath python check.py
"""
from __future__ import annotations
from fractions import Fraction
from math import isqrt
from pathlib import Path
import json
import time
import mpmath as mp

ROOT = Path(__file__).resolve().parent
assert (ROOT / 'registration.json').exists(), 'Register predictions before tests.'

def hurwitz(n: int) -> Fraction:
    if n == 0:
        return Fraction(-1, 12)
    if n % 4 in (1, 2):
        return Fraction(0)
    result = Fraction(0)
    for a in range(1, isqrt(n // 3) + 1):
        for b in range(-a, a + 1):
            if (b*b + n) % (4*a):
                continue
            c = (b*b + n) // (4*a)
            if c < a or ((abs(b) == a or a == c) and b < 0):
                continue
            result += Fraction(1, 3) if a == b == c else Fraction(1, 2) if b == 0 and a == c else Fraction(1)
    return result

HS = [hurwitz(n) for n in range(1001)]
assert [HS[n] for n in (0,3,4,7,8,12)] == [Fraction(-1,12),Fraction(1,3),Fraction(1,2),Fraction(1),Fraction(1),Fraction(4,3)]

def theta(tau, N=30):
    return 1 + 2*mp.fsum(mp.exp(2j*mp.pi*n*n*tau) for n in range(1, N+1))

def correction(tau, N=30):
    y = mp.im(tau)
    if y <= 0:
        raise ValueError('tau must be in the upper half-plane.')
    return 1/(8*mp.pi*mp.sqrt(y)) + mp.fsum(
        n/(4*mp.sqrt(mp.pi))*mp.gammainc(-mp.mpf('0.5'),4*mp.pi*n*n*y,mp.inf)
        * mp.exp(-2j*mp.pi*n*n*tau) for n in range(1,N+1))

def holomorphic_part(tau):
    q = mp.exp(2j*mp.pi*tau)
    # Horner avoids unnecessary exponentiation; coefficients are exact rationals.
    acc=mp.mpc(0)
    for h in reversed(HS):
        acc=acc*q+mp.mpf(h.numerator)/h.denominator
    return acc

def completed(tau):
    return holomorphic_part(tau)+correction(tau)

def bf_operator(fun, tau):
    x,y=mp.re(tau),mp.im(tau)
    dx=mp.diff(lambda u: fun(u+1j*y),x)
    dy=mp.diff(lambda v: fun(x+1j*v),y)
    return 2j*y**mp.mpf('1.5')*mp.conj((dx+1j*dy)/2)

def xi_mellin(s,N=10):
    def moment(v):
        return mp.fsum((mp.pi*n*n)**(-v/2)*mp.gammainc(v/2,mp.pi*n*n,mp.inf)
                       for n in range(1,N+1))
    return mp.mpf('0.5')+s*(s-1)/2*(moment(s)+moment(1-s))

def xi_direct(s):
    return s*(s-1)/2 * mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def logder_direct(s):
    return 1/s+1/(s-1)-mp.log(mp.pi)/2+mp.digamma(s/2)/2+mp.diff(mp.zeta,s)/mp.zeta(s)

def lambda_table(N):
    out=[mp.mpf(0)]*(N+1)
    prime=[True]*(N+1)
    for p in range(2,N+1):
        if not prime[p]:
            continue
        for k in range(p*p,N+1,p):
            prime[k]=False
        k=p
        while k<=N:
            out[k]=mp.log(p)
            k*=p
    return out

def fmt(x):
    return mp.nstr(x,22)

def run(dps):
    mp.mp.dps=dps
    results={'dps':dps,'classification':'DIAGNOSTIC_NOT_INTERVAL_CERTIFICATION'}
    ts=[mp.mpc('0.2','0.7'),mp.mpc('-0.1','1.1'),mp.mpc(0,'0.8')]
    results['M1_shadow_errors']=[fmt(abs(bf_operator(correction,t)+theta(t)/(16*mp.pi))) for t in ts]
    results['M2_modular_relative_errors']=[fmt(abs(completed(t/(4*t+1))-(4*t+1)**mp.mpf('1.5')*completed(t))/max(1,abs(completed(t/(4*t+1))))) for t in ts]
    ss=[mp.mpc(2),mp.mpc(3),mp.mpc('0.5','3'),mp.mpc('-1','2')]
    results['M3_xi_errors']=[fmt(abs(xi_mellin(s)-xi_direct(s))) for s in ss]
    results['M3_logder_errors']=[fmt(abs(mp.diff(xi_mellin,s)/xi_mellin(s)-logder_direct(s))) for s in ss]
    # This is the analytic invariance control, not a claim that q itself is a modular form.
    results['M4_holomorphic_gauge_errors']=[fmt(abs(bf_operator(lambda z:correction(z)+mp.exp(2j*mp.pi*z),t)-bf_operator(correction,t))) for t in ts]
    N=4096
    lam=lambda_table(N)
    s=mp.mpc('3.5','1.25'); sig=mp.re(s)
    truncated=mp.fsum(lam[n]*n**(-s) for n in range(2,N+1))
    err=abs(-mp.diff(mp.zeta,s)/mp.zeta(s)-truncated)
    tail=mp.mpf(N)**(1-sig)*(mp.log(N)/(sig-1)+1/(sig-1)**2)
    results['M5_prime_sum_error']=fmt(err)
    results['M5_prime_sum_tail_upper']=fmt(tail)
    results['M5_tail_pass']=bool(err<tail)
    assert max(map(mp.mpf,results['M1_shadow_errors']))<mp.mpf('1e-35')
    assert max(map(mp.mpf,results['M2_modular_relative_errors']))<mp.mpf('1e-35')
    assert max(map(mp.mpf,results['M3_xi_errors']))<mp.mpf('1e-35')
    assert max(map(mp.mpf,results['M3_logder_errors']))<mp.mpf('1e-35')
    assert max(map(mp.mpf,results['M4_holomorphic_gauge_errors']))<mp.mpf('1e-35')
    assert results['M5_tail_pass']
    return results

if __name__=='__main__':
    start=time.monotonic(); out=[]
    for j,dps in enumerate((45,65),start=1):
        out.append(run(dps))
        elapsed=time.monotonic()-start
        eta=elapsed/j*(2-j)
        print('['+'#'*(10*j)+'-'*(20-10*j)+f'] {j}/2 ETA {eta:.1f}s',flush=True)
    path=ROOT/'results.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
```
