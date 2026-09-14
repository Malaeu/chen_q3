# STATUS: KILL_NAMED_BROWNIAN_EMBEDDING
```yaml
OPERATIVE_CLASS: KILL_NAMED_BROWNIAN_EMBEDDING
REQUEST_ID: REQ-2026-09-13-BROWNIANHODGE
BOUNDARY_ID: GOAL058_ACTUAL_THETA_BROWNIAN_PRIMITIVE_TRANSFER
REQUEST_COMMIT: 3f057975d59adcd9b61a3585c8f293624ba742ae
REQUEST_BLOB: 311885a13b27dcd7573d1855fb91e2f6809f0e70
REQUEST_SHA256: f40965ea88f8ae000af0e31b3e26d7310c2abf8a09bea89a07d8ae4990a1b93d
SOURCE_BASE: 59c7f0eceaf250d5b6d866965bc56c18b0a661bd
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
CANDIDATE: CONDITIONAL_HALF_ENERGY_Q_PRIMITIVE_PROFILE
EXACT_MAP: J_x = P_alpha k_x; alpha = 1/4
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: ANALYTIC_STRICT_CORRELATION_MISMATCH_AT_EXPLICIT_NODE_PAIRS
KILL_EVIDENCE_REF: "This artifact, (28)-(31), nodes (15,15+log(2)) and (-15-log(2),-15)"
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS_NAMED_IDENTITY: MATHEMATICALLY_DEAD_AT_STATED_SCOPE
GENERAL_PRIMITIVE_TRANSFER: UNRESOLVED
FIRST_UNPAID_TRANSITION: SOURCE_SPECIFIC_FORM_PRESERVING_MAP_TO_THE_FULL_V
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROOF_STATE: NEW_PAPER_DERIVATION_PENDING_INDEPENDENT_ACCEPTANCE
LEAN_VERIFIED: false
ACTUAL_V_NEGATIVE_WITNESS: false
GLOBAL_IC: OPEN_UNCHANGED
GLOBAL_ODD2: OPEN_UNCHANGED
ALL_ORDER_SOURCE_SIGN: OPEN_UNCHANGED
PX_RH_CLAIM: NOT_MADE
PRODUCTION_ADMISSION: false
SOURCE_SIGN_NO_DELTA:
  inherited: 4
  proposed_after_independent_intake: 5
  applied_to_state: false
PUBLICATION_BRANCH: codex_mac/math-proshka-20260912
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_BROWNIANHODGE_2026-09-13.md
```

AUTOPSY: dropped=OBJECT_IDENTITY; note=The projected conditional-half-energy profiles have normalized H_alpha correlation at least 19/20 at both explicit tail pairs, whereas the same-source full V_f correlation is below 17/20. Positive diagonal normalization cannot repair the mismatch.

## 1. Решение и область результата

**Проверен один кандидат:** точная Q-примитивная проекция предложенного в запросе условного профиля. Его область определения и примитивность правильны. Однако он не сохраняет смешанные элементы исходного V_f, даже с произвольными положительными множителями при каждом узле.

Для каждой пары
\[
(x_1,x_2)=(r,r+\log2)
\quad\text{либо}\quad
(x_1,x_2)=(-r-\log2,-r),\qquad r\ge15,
\tag{1}
\]
доказаны **полные аналитические**, а не численно подогнанные оценки
\[
\rho_{\mathrm{Br}}(x_1,x_2)>\frac{19}{20},
\qquad
0<\rho_V(x_1,x_2)<\frac{17}{20}.
\tag{2}
\]
Здесь rho означает элемент ядра, поделённый на квадратный корень произведения его диагоналей. Следовательно, верхняя огибающая дефекта равенства строго отрицательна:
\[
\rho_V-\rho_{\mathrm{Br}}<-\frac1{10}.
\tag{3}
\]
Это **отказ вложения**, не отрицательность исходной формы. После единственной нормировки, полностью совпадающей с диагоналями V, остаток также не является положительным: на явном нормированном двухузловом векторе он меньше -1/5. Такая поправка не может быть суммой независимо положительных форм. Не исключены другие вложения и другие разложения, оставляющие положительный диагональный резерв.

Все новые утверждения ниже — **PAPER-кандидаты**, ожидающие независимой проверки; вычислительная проверка касается только точной арифметики и алгебраических контролей. Знак V на всех узлах не доказан. `[COFINAL_FAMILY][PAPER]`

## 2. Прочитанные источники и нормировки

**R0.** Управляющий запрос по указанному пользователем commit прочитан целиком: 9895 UTF-8 bytes, 123 LF, final LF, CR 0. Его SHA-256 и blob находятся в заголовке.

**S1.** `docs/Codex/REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md` в том же commit: 10647 bytes / 206 LF; SHA-256 `accbbc050d41c54cf09927571b24106f2a6a6e84a960cf076b8f4dbf900cd809`; blob `5795f0cb8bc580eee843a1a6900f208a62f778d8`. Прочитан целиком. B1-B5 используются как принятые PAPER-входы: полный источник, D_alpha, один положительный индекс, проекция и Gram-формула. Отказ голых экспонент не является новым опытом этого ответа.

**S2.** `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md` в SOURCE_BASE: 37796 bytes / 467 LF; SHA-256 `14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc`; blob `de9578084446baecfbb2a316d7bda3da817c8c01`. Содержательно прочитаны нужные BP1-BP3/BP3b и соответствующий исходный словарь. Полное повторное чтение его рекурсивных зависимостей не заявляется.

**S3.** `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` в SOURCE_BASE: 15303 bytes / 335 LF; SHA-256 `1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282`; blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`. Прочитан целиком. Используются полные исходные определения, экспоненциальные огибающие и принятый Theorem T: все конечные V-матрицы PSD тогда и только тогда, когда полная форма Вейля неотрицательна на всех комплексных компактных гладких тестах. Ни одна сторона не принимается положительной.

**S4.** `docs/Codex/REPORT_2026-09-13_VILLAINPHI_INTAKE.md` в SOURCE_BASE: 11945 bytes / 223 LF; SHA-256 `3f0b9c6e9e433b643404ceb742c4519a55795fa65a4ac899fc6d94a741d89019`; blob `0b7061f8321ebe70e8b42f79010922e602d25276`. Прочитан целиком. Исключение гармонических весов с равномерно двухсторонне ограниченной Gibbs-плотностью не расширяется на все модели Виллена. Новый спиновый опыт не запускается.

**P1.** Biane–Pitman–Yor, *Probability laws related to the Jacobi theta and Riemann zeta functions, and Brownian excursions*, arXiv:math/9912170v1, §4.4, printed/PDF p.22: https://arxiv.org/pdf/math/9912170 . Страница непосредственно просмотрена, включая screenshot. Fourier-ряд моста начинается с n=1; в следующей Parseval-строке видна указанная в S1 опечатка n=0. Используется согласованный ряд без нулевой моды. Это лишь Brownian-словарь. Нового утверждения о знаке Вейля в P1 нет. PDF через web прочитан, но его загрузка в sandbox не удалась; унаследованный из S1 PDF-хеш не объявляется независимо пересчитанным.

Все четыре source-хеша и пять Git blobs с запросом пересчитаны. R0/S1/S4 восстановлены из полных UTF-8 ответов GitHub connector. Для S2/S3 байтовые копии извлечены из ранее доставленных точных frames и сопоставлены с blobs, непосредственно полученными из GitHub в SOURCE_BASE. Это способ аутентификации тех же байтов, не подмена источника старым чатом. Код и буквальные результаты находятся в приложении. Bootstrap прочитан из `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`.

Сохраняем
\[
Z=\int_{\mathbb R}\Phi=\xi(1/2),\qquad A=\|\Phi\|_2,
\qquad f=\Phi/A,\qquad \alpha=\tfrac14,
\]
\[
U_1,U_2\ \text{независимы с законом }\nu,
\quad U_1=\sum_{n\ge1}\frac{E_n}{\pi n^2},\quad E_n\sim\operatorname{Exp}(1),
\quad T=U_1+U_2,
\quad C=\mathbb E T^\alpha=2Z.
\tag{4}
\]
U_2 — это случайная величина V из запроса, переименованная только во избежание совпадения с ядром V_f. Z из BP1 имеет другое историческое обозначение: в настоящем документе всегда C=2Z, а Z — интеграл Phi. `[ABSTRACT][PAPER]`

## 3. Кандидат фиксируется до вычислительных проверок

Название: **CONDITIONAL_HALF_ENERGY_Q_PRIMITIVE_PROFILE**.

Для t=exp(2x) задаём
\[
k_x(u)=\frac{h_\nu(t-u)}{r(t)},\qquad
J_x=P_\alpha k_x
=k_x-\frac{Q_\alpha(1,k_x)}C\,1.
\tag{5}
\]
Первая формула равна буквально профилю запроса, поскольку Phi(x)=exp(5x/2)r(t). Используется только одна семья J; позднее диагональное масштабирование рассматривается как необходимое условие гипотетического совпадения, не как второй подгоняемый опыт.

Записанные до символической проверки ожидания: P1 — нормировка/область/примитивность сохраняются; P2 — нормированные Brownian-корреляции при фиксированном ненулевом сдвиге стремятся к 1 на обоих концах; P3 — положительная диагональная нормировка не исправит расхождение с V. Это не предсказания RH. Файл регистрации имеет SHA-256 `6de2a9382cfc9e3f571723296eeca0569d98c574e8f4ca821c3f6701ae5f1eb6`.

## 4. Полный источник: отделение первого экспоненциального слагаемого

Обозначим W=sum_{n>=2} E_n/(pi n^2). При N>=2 точные произведение и сумма телескопируются:
\[
\mathbb E e^{\pi W_N}=\prod_{n=2}^N\frac{n^2}{n^2-1}=\frac{2N}{N+1},
\]
\[
\sum_{n=2}^N\frac1{n^2-1}
=\frac34-\frac1{2N}-\frac1{2(N+1)}.
\tag{6}
\]
Неотрицательные W_N возрастают к W. Монотонная сходимость для exp(pi W_N) и W_N exp(pi W_N) даёт
\[
\mathbb E e^{\pi W}=2,\qquad
\frac{\mathbb E[W e^{\pi W}]}2=\ell:=\frac3{4\pi}.
\tag{7}
\]
Для второй формулы на конечном N дифференцируется конечное произведение, затем применяется именно монотонная сходимость. Бесконечное дифференцирование без мажоранты не требуется.

Пусть
\[
\chi(u)=\tfrac12\mathbb E[e^{\pi W}\mathbf1_{W<u}],\quad u>0.
\]
Это CDF положительного закона с плотностью Радона–Никодима exp(pi W)/2 относительно закона W. В частности
\[
0\le\chi\le1,\qquad
\int_0^\infty(1-\chi(u))\,du=\ell.
\]
Свёртка первого Exp(rate pi) со всем W даёт точные формулы
\[
h_\nu(u)=2\pi e^{-\pi u}\chi(u),
\qquad 0\le h_\nu(u)\le\pi,
\]
\[
r(t)=4\pi^2e^{-\pi t}\mathcal B(t),
\qquad
\mathcal B(t)=\int_0^t\chi(u)\chi(t-u)\,du.
\tag{8}
\]
Оценка h_nu<=pi получается из свёртки с вероятностью, а не из замены 2pi на pi в первой формуле.

Закон W имеет положительную вероятность попасть в (0,epsilon) при любом epsilon>0: выбираем хвост с ожиданием меньше epsilon/4, применяем Markov к хвосту и ограничиваем конечное число независимых экспонент. Его закон не имеет атомов, поскольку содержит независимый Exp(rate 4pi). Поэтому h_nu непрерывна, положительна на (0,infinity), равна нулю на неположительной полуоси и непрерывна в нуле. В частности r(t)>0 для t>0.

Из 1-ab<=(1-a)+(1-b) при a,b в [0,1]:
\[
0<\mathcal B(t)\le t,
\qquad 0\le t-\mathcal B(t)\le2\ell=\frac3{2\pi}.
\tag{9}
\]
Это полная оценка всего бесконечного источника. Никакое слагаемое W не отброшено. `[ABSTRACT][PAPER]`

## 5. Условный профиль, tilt и примитивность

Версия условного закона U_1 при T=t имеет плотность
\[
\eta_t(du)=\frac{h_\nu(u)h_\nu(t-u)}{r(t)}\mathbf1_{0<u<t}\,du
=k_x(u)\,d\nu(u),\qquad t=e^{2x}.
\tag{10}
\]
Это непосредственно следует из совместной плотности (U_1,T). Следовательно int k_x dnu=1. Tilt по T^alpha/C умножает совместную плотность и её T-маргинал на одинаковый фактор, поэтому (10) остаётся тем же условным законом. Замена t=exp(2x) в tilted T-плотности даёт
\[
\frac2C e^{2(1+\alpha)x}r(e^{2x})=\Phi(x)/Z.
\]
Тем самым сохранены tilt, якобиан, полный источник и L1-нормировка. Нормировка A по-прежнему входит только в целевое f.

Для каждого фиксированного t>0:
\[
\|k_x\|_{D_\alpha}^2
\le \left(\frac\pi{r(t)}\right)^2(1+t^\alpha)<\infty,
\quad D_\alpha=L^2((1+u^\alpha)d\nu).
\tag{11}
\]
Постоянные принадлежат D_alpha; Q_alpha и H_alpha непрерывны на этом пространстве по S1 B2-B4. Поэтому J_x принадлежит D_alpha, и
\[
Q_\alpha(1,J_x)=0,
\qquad
H_\alpha(J_x,J_y)=H_\alpha(k_x,k_y)=-Q_\alpha(J_x,J_y).
\tag{12}
\]
Обычное среднее J_x не обязано равняться нулю: оно равно 1-Q_alpha(1,k_x)/C. Не смешиваем это с Q-примитивностью.

k_x не постоянна nu-почти всюду: она нормирована к массе 1 и равна нулю на (t,infinity), которое имеет положительную nu-меру. Значит H_alpha(k_x,k_x)>0 по S1 B4. Любая конечная комплексная линейная комбинация J_x допустима.

На любом компакте x семья k_x непрерывна в D_alpha: r(t) отделена от нуля, h_nu непрерывна и ограничена, а носители k_x лежат в одном ограниченном интервале. Доминированная сходимость в (11) доказывает утверждение. Таким образом и интегрирование этой семьи против компактного L1-теста допустимо как Bochner-интеграл. Для отказа all-node тождества ниже достаточно двух узлов; дополнительный переход через компактные тесты не предполагается. `[ABSTRACT][PAPER]`

## 6. Точная смешанная форма условных профилей

Пусть
\[
\mu=\mathbb E_\nu U^\alpha>0,\quad
w(u)=\int(u+v)^\alpha\,d\nu(v),
\]
\[
\beta(t)=\int w(u)\,d\eta_t(u),\qquad
D(t,s)=\iint(u+v)^\alpha\,d\eta_t(u)d\eta_s(v).
\]
Все эти интегралы конечны: eta_t имеет носитель в (0,t), а nu имеет конечные положительные моменты. При разных t,s используются независимые условные маргиналы eta_t tensor eta_s, а не ошибочно один совместный условный закон при единственном T.

Из определения Q_alpha и B3 следует **полное смешанное равенство**
\[
\boxed{\mathsf B(x,y):=H_\alpha(J_x,J_y)
=\frac{\beta(t)\beta(s)}C-D(t,s),
\qquad t=e^{2x},\ s=e^{2y}.}
\tag{13}
\]
Имеем
\[
0\le D(t,s)\le(t+s)^\alpha,
\quad \mu\le\beta(t)\le\mu+t^\alpha,
\quad C\le2\mu,\quad C<2,\quad\mu>\frac16.
\tag{14}
\]
Первые оценки следуют из субаддитивности степени alpha и поддержки eta_t. Для C<2 используем Jensen и E T=pi/3. Для последней оценки U>=E_1/pi: на событии E_1>=1 с вероятностью e^{-1}>1/3 имеем U^{1/4}>=pi^{-1/4}>1/2. Все константы исходные.

Обозначим
\[
\rho_{\mathrm{Br}}(x,y)=\frac{\mathsf B(x,y)}{\sqrt{\mathsf B(x,x)\mathsf B(y,y)}}.
\tag{15}
\]
Знаменатель положителен, а |rho_Br|<=1 по принятой положительности H_alpha. Это не применение Коши–Буняковского к неизвестной положительности V. `[ABSTRACT][PAPER]`

## 7. Конец x -> -infinity: полный конечный бюджет

Положим M=max(t,s), eta=M^alpha/mu и B_*=mu^2/C. Из (13)-(14) для каждой пары параметров не больше M:
\[
1-3\eta\le\frac{\mathsf B(x,y)}{B_*}\le(1+\eta)^2.
\tag{16}
\]
Действительно, D/B_*<=2^{1+alpha}eta<3eta; произведение beta(t)beta(s)/mu^2 лежит между 1 и (1+eta)^2. То же верно на двух диагоналях.

Если max(x,y)<=-15, то M<=e^{-30}, поэтому
\[
\eta<6e^{-15/2}<\frac6{900}<\frac1{100}.
\]
Здесь e^7>(8/3)^7>900. Получаем
\[
\boxed{\rho_{\mathrm{Br}}(x,y)
\ge\frac{1-3\eta}{(1+\eta)^2}
>\frac{9700}{10201}>\frac{19}{20}.}
\tag{17}
\]
В частности, при любом фиксированном d
\[
\mathsf B(x,x+d)\longrightarrow\frac{\mu^2}C,
\qquad\rho_{\mathrm{Br}}(x,x+d)\longrightarrow1
\quad(x\to-\infty).
\tag{18}
\]
Мы не утверждали сходимости k_x в D_alpha: её норма может расти. Предел (18) доказан непосредственно полным смешанным интегралом (13), без недопустимой подстановки предельной дельта-меры в L2. `[COFINAL_FAMILY][PAPER]`

## 8. Конец x -> +infinity: условная доля энергии и проекция

Из (8)-(10) следует
\[
\eta_t(t\,da)=\frac{t\chi(ta)\chi(t(1-a))}{\mathcal B(t)}\,da,
\qquad 0<a<1.
\tag{19}
\]
Более того, для t>2ell расстояние плотности (19) от 1 в L1(0,1) не больше
\[
\frac{4\ell}{t-2\ell}.
\]
Чтобы проверить константу, обозначим f_t(a)=chi(ta)chi(t(1-a)) и b=cal B(t)/t. Тогда 0<=f_t<=1, int f_t=b, а int |f_t/b-1|<=2(1-b)/b. Оценка (9) завершает доказательство. Это количественная сходимость условной доли U_1/T к Uniform(0,1), а не предположение о распределении энергии.

Непосредственно из (9) также следует при t>=2:
\[
\int u^\alpha\,d\eta_t(u)
\ge\frac{t^\alpha}{1+\alpha}-2\ell t^{\alpha-1}
\ge\frac{t^\alpha}{2(1+\alpha)}=\frac25t^\alpha.
\tag{20}
\]
Для первой оценки потеря числителя не превосходит 2ell t^alpha; cal B(t)<=t. Числитель положителен в используемой области. Вторая оценка требует t>=4ell(1+alpha)=15/(4pi)<2. Поэтому beta(t)>=2t^alpha/5.

Запишем
\[
\varepsilon(t,s)=\frac{CD(t,s)}{\beta(t)\beta(s)}.
\]
При min(t,s)>=2:
\[
0\le\varepsilon(t,s)
\le\frac{25C}4(1/t+1/s)^\alpha
<15\min(t,s)^{-\alpha}.
\tag{21}
\]
Здесь C<2 и 2^{1/4}<6/5. Если min(x,y)>=15, то каждая из epsilon(t,s), epsilon(t,t), epsilon(s,s) меньше 1/60. Следовательно
\[
\boxed{\rho_{\mathrm{Br}}(x,y)
=\frac{1-\varepsilon(t,s)}
{\sqrt{(1-\varepsilon(t,t))(1-\varepsilon(s,s))}}
>\frac{59}{60}>\frac{19}{20}.}
\tag{22}
\]
Все три epsilon сохранены. Знаменатель положителен и не больше 1.

Из (19), ограниченности a^alpha на [0,1] и |w(u)-u^alpha|<=mu:
\[
\frac{\beta(t)}{t^\alpha}\longrightarrow\frac45,
\qquad
\mathsf B(x,y)\sim\frac{16}{25C}(ts)^\alpha
\]
при t,s->infinity с фиксированным положительным отношением. Поэтому
\[
\rho_{\mathrm{Br}}(x,x+d)\longrightarrow1\quad(x\to+\infty).
\tag{23}
\]
На этом конце рангово-одномерный главный вклад возникает из самой примитивной проекции beta(t)beta(s)/C: смешанная D(t,s) имеет меньший порядок. Это установлено для полного закона, не для усечённых броуновских мод. `[COFINAL_FAMILY][PAPER]`

## 9. Полный V_f: независимая верхняя оценка корреляции

Здесь не повторяется опыт с голыми экспонентами B7. Проверяется тот же полный V против новой семьи (5). Из полного вероятностного источника (8)-(9) получается точная theta-факторизация
\[
\Phi(z)=4\pi^2e^{9z/2-a_z}H_\theta(a_z),
\quad a_z=\pi e^{2z},
\quad H_\theta(a)=\frac{\mathcal B(a/\pi)}{a/\pi},
\]
\[
0<H_\theta(a)\le1,\qquad
H_\theta(a)\ge1-\frac3{2a}\quad(a>0).
\tag{24}
\]
Это равенство со всей theta, поскольку r=h_nu*h_nu является буквально r из BP1. Нижняя оценка может быть отрицательной при малом a; ниже она используется только при a>=1500. Не делаем неверного вывода о каждом слагаемом theta-ряда.

Пусть x,y>=15, a=pi e^{2x}, b=pi e^{2y}, S=x+y, Lambda=a+b и l_a=1-3/(2a), l_b=1-3/(2b). Подстановка z=e^{2v}-1 в ПОЛНЫЙ исходный интеграл даёт
\[
\frac{V_f(x,y)}{f(x)f(y)}
=\frac1{2H_\theta(a)H_\theta(b)}
\int_0^\infty [S+\log(1+z)](1+z)^{7/2}e^{-\Lambda z}
H_\theta(a(1+z))H_\theta(b(1+z))\,dz.
\tag{25}
\]
Никакая конечная верхняя граница вместо infinity не подставлена. Для z>=0 используем log(1+z)<=z и (1+z)^{7/2}<=exp(7z/2). Тогда
\[
\frac{V_f(x,y)}{f(x)f(y)}
\le\frac1{2l_al_b}
\left(\frac S{\Lambda-7/2}+\frac1{(\Lambda-7/2)^2}\right),
\]
\[
\frac{V_f(x,x)}{f(x)^2}\ge\frac{x l_a^2}{2a},
\qquad
\frac{V_f(y,y)}{f(y)^2}\ge\frac{y l_b^2}{2b}.
\tag{26}
\]
Нижние диагональные границы получены из того же полного интеграла: удаляются только неотрицательные добавки log(1+z) и (1+z)^{7/2}-1; H_theta(a(1+z))>=l_a, а H_theta(a)<=1. Все экспоненциальные интегралы в (26) вычислены точно.

Для y=x+log2, x>=15 имеем b=4a, Lambda=5a, S>=30, a>1500 и log2<1. Из (26):
\[
\rho_V(x,y)
\le \frac{S\sqrt{ab}}{\Lambda\sqrt{xy}}
\frac1{(l_al_b)^2}
\frac\Lambda{\Lambda-7/2}
\left(1+\frac1{S(\Lambda-7/2)}\right).
\]
Последовательно,
\[
\frac{S\sqrt{ab}}{\Lambda\sqrt{xy}}\le\frac{62}{75},
\quad l_a,l_b>\frac{999}{1000},
\quad \frac\Lambda{\Lambda-7/2}<\frac{1001}{1000},
\quad 1+\frac1{S(\Lambda-7/2)}<\frac{1001}{1000}.
\]
Первое сравнение использует sqrt(xy)>=x и S/(2x)<=31/30; остальные — Lambda>=7500. Получаем строгую рациональную верхнюю огибающую
\[
\boxed{0<\rho_V(x,x+\log2)
<\frac{62}{75}\left(\frac{1000}{999}\right)^4
\left(\frac{1001}{1000}\right)^2
=\frac{2484962480000}{2988017988003}<\frac{17}{20}.}
\tag{27}
\]
Константа не зависит от x>=15. A отменяется только в корреляции, а не меняется в определении исходной формы.

Для отрицательного конца используется точное отражение V_f(-x,-y)=V_f(x,y). Доказательство: при m=(x+y)/2, d=(x-y)/2 интеграл равен int_m^infinity 2w f(w+d)f(w-d)dw; его подынтегральная функция нечётна по w. Разность нижних границ m и -m интегрирует её по симметричному интервалу и равна нулю. Полная сходимость следует из S3. Аналогично V_f(x,x)>0 для каждого вещественного x.

Оценки (25)-(26) также сжимают V_f(x,x+d)/(f(x)f(x+d)) к (2x+d)/(2(a_x+a_{x+d})) при x->infinity. Поэтому воспроизводится принятая асимптотика B8: rho_V->sech(d), а при d=log2 предел равен 4/5. Для конечного отказа достаточно (27), без неопределённого асимптотического порога. `[COFINAL_FAMILY][PAPER]`

## 10. Точное исключение вложения и положительных диагональных нормировок

Для пар (1) оценки (17), (22), (27) дают
\[
\boxed{\rho_V(x_1,x_2)-\rho_{\mathrm{Br}}(x_1,x_2)<-\frac1{10}.}
\tag{28}
\]
В частности подходят две полностью указанные конечные пары:
\[
(15,15+\log2),\qquad(-15-\log2,-15).
\tag{29}
\]
Это не результат подбора точек и не численный отрицательный минор. Полные аналитические огибающие доказывают (28) сразу для всего r>=15.

Если для положительных w(x) существовало бы
\[
V_f(x,y)=H_\alpha(w(x)J_x,w(y)J_y),
\]
то диагонали вынуждали бы w(x)=sqrt(V_f(x,x)/mathsf B(x,x)). После деления на них корреляции обязаны совпадать. (28) это опровергает. Добавление констант к профилям ничего не меняет, поскольку константы лежат в радикале H_alpha; повторная P-проекция также ничего не меняет. Ненулевые комплексные множители не помогают: абсолютное значение нормированной корреляции инвариантно, а в (28) обе корреляции положительны.

**Исключено только это семейство профилей, с указанными скалярными изменениями.** Ни зависимые от масштаба производные, ни новые операторы на условных законах не исключены этим доказательством. Они не запускались как второй опыт. `[COFINAL_FAMILY][PAPER]`

## 11. Полный остаток и запрет одной мнимой починки

Для исходного, ненормированного кандидата положим
\[
\mathscr R(x,y)=V_f(x,y)-\frac{\beta(e^{2x})\beta(e^{2y})}C
+D(e^{2x},e^{2y}).
\tag{30}
\]
Для всех конечных вещественных узлов и всех комплексных c точно
\[
\sum_{i,j}\overline{c_i}V_f(x_i,x_j)c_j
=H_\alpha\left(\sum_i c_iJ_{x_i},\sum_jc_jJ_{x_j}\right)
+\sum_{i,j}\overline{c_i}\mathscr R(x_i,x_j)c_j.
\]
Все интегралы (30) конечны по §§5-6 и S3. Это не новое доказательство знака: полный остаток сохранён и его глобальная неотрицательность не установлена.

Для единственного диагностического совпадения диагоналей w(x)=sqrt(V_f(x,x)/mathsf B(x,x)) остаток R_w имеет нулевую диагональ. Для любой пары (1) и c_i=V_f(x_i,x_i)^{-1/2} получаем **явную отрицательную верхнюю оценку**
\[
\boxed{\sum_{i,j=1}^2\overline{c_i}R_w(x_i,x_j)c_j
=2(\rho_V-\rho_{\mathrm{Br}})<-\frac15.}
\tag{31}
\]
Таким образом R_w не PSD и не может быть суммой независимо положительных форм. Это не попытка построить J через Cholesky целевого V: w — необходимый вес при уже проверяемом равенстве диагоналей, использованный только для опровержения.

**Исходная V-форма на том же векторе положительна:** её значение равно 2+2rho_V>0. Никакого отрицательного свидетеля V, K_- или Вейля из (31) не следует. Выбор меньшего Brownian-вклада, оставляющего ненулевой диагональный резерв, и новое разложение с другим доказательством остатка этим частным запретом не исключаются. `[FINITE_CELL][PAPER]`

## 12. ROUTE MAP, K8A и первый неоплаченный переход

| Объект | Область и проверка | Результат |
|---|---|---|
| Полный U_1+U_2, tilt и C=2Z | ABSTRACT / PAPER | Принятые S1-S2, нормировки проверены |
| Положительный H_alpha | ABSTRACT / PAPER | Принятый S1 B3-B4, не новое решение V |
| Условные k_x и J_x | ABSTRACT / PAPER | Нормированы, принадлежат D_alpha, Q-примитивны |
| Формула (13) | ABSTRACT / PAPER | Точный полный смешанный интеграл |
| Два конца и (28) | COFINAL_FAMILY / PAPER | Новый строгий отказ названного вложения |
| Диагонально исчерпанный остаток (31) | FINITE_CELL / PAPER | Строго отрицателен на явном векторе |
| Другое вложение / положительный резерв | ABSTRACT / CONDITIONAL | Не построены и не исключены |
| Все V / все тесты Вейля | ABSTRACT / CONDITIONAL | Знаковый вход остаётся открыт |

**DOWNSTREAM_CONSUMER:** Theorem T из S3, затем опубликованный критерий Вейля на всех комплексных компактных гладких тестах.

**ACTUAL_CONSUMER_REQUIREMENT:** полный all-node PSD исходного V, с физической нормировкой A. В этой попытке не заменяется ODD2, конечными матрицами одного размера или Brownian-энергией другой формы.

**ORIGINAL_REQUESTED_OBJECT:** одно source-derived вложение условных профилей в H_alpha с точным сохранением V. Названный J_x=P_alpha k_x является кандидатом на достаточный поставщик, не обязательным объектом всякого доказательства.

**ORIGINAL_OBJECT_IS:** NOT_NECESSARY для полного знака V. Конкретное равенство через (5) ложно. Общая возможность другого сохранения формы — UNKNOWN.

**KNOWN_WEAKER_INTERFACES:** V=B+R с независимо доказанными PSD обеих форм; либо иное точное source-derived сохранение смешанных спариваний. Формула (30) сама не оплачивает PSD остатка. Требование этого знака без новой оценки — прежний all-node потребитель, а не прогресс.

**FAILURE_TYPE / EPISTEMIC_STATUS:** INCOMPATIBILITY / MATHEMATICALLY_DEAD только для тождества через (5), даже после диагональной перенормировки. Evidence — (28)-(31). Для общего переноса: NO_DERIVATION / RESEARCH_DEBT. Reopen trigger — иной явный оператор или профиль с доказанным соответствием смешанных элементов, а не переименование H_alpha и не новая скалярная нормировка той же семьи.

**NOVELTY_AXIS:** conditional-half-energy source fit, оба конца, явные конечные отрицательные бюджеты дефекта равенства. Ни абстрактный Hodge-носитель, ни известный Brownian-словарь не заявляются новыми.

**FIRST_UNPAID_TRANSITION:** исходная структура -> сохраняющее V смешанное спаривание. Для выбранной карты переход не просто неоплачен, а опровергнут. Существует точный остаток (30), но допустимого положительного восстановления нет в представленном доказательстве.

**DISCRIMINATOR:** нормированная смешанная корреляция на паре с фиксированным ненулевым логарифмическим расстоянием. Диагональные совпадения этот функционал не видят. Результат здесь не zero-consistent: бюджет (28) отделён от нуля на 1/10.

Две **неисполненные** пере-репрезентации для более широкого открытого переноса, не новые назначенные опыты:

| Представление | Что должно измениться | Оценка kill-power / стоимости |
|---|---|---|
| Логарифмические масштабные разности условных профилей | Удалить выявленное рангово-одномерное насыщение, затем заново оплатить домен и смешанное спаривание | 8/10 против такого же saturation; 5/10 стоимости. Знак/соответствие не доказаны |
| Полный условный оператор и его сопряжённый с сохранённым остатком | Сохранить зависимость от обеих половин энергии, а не только однопрофильный вклад; отдельно оценить настоящий остаток | 9/10 для object-match; 8/10 стоимости. Положительность остатка не дана |

Эти оценки — исследовательские оценки, не теоремы и не разрешение на автоматическое второе семейство. `[ABSTRACT][CONDITIONAL]`

## 13. STRONGEST ATTACK / META CLOSEOUT

**Сильнейшее возражение:** положительная новая геометрия могла бы совпасть с V после устранения неправильной нормировки. Ответ — корреляции (15), (27) инвариантны относительно любых положительных узловых множителей. Отказ относится именно к смешанным элементам, а не к диагональному масштабу.

Другие проверенные риски: (i) small-t предел не принят в D_alpha без доказательства; (ii) при tilt условный закон сохранён расчётом; (iii) W содержит все n>=2, его экспоненциальное взвешивание оплачено полным произведением; (iv) оба бесконечных V-интеграла при отражении оплачены; (v) H_alpha применяется с правильным знаком -Q_alpha на примитивной части; (vi) нулевой Brownian Fourier mode не введён; (vii) отрицательность остатка не названа отрицательностью V.

P1, P2, P3 подтверждены соответственно §§5, 7-8, 10. Прогнозы не переписаны. Алгебраический plant различил точное равенство и ложную рангово-одномерную подстановку до проверки рациональных бюджетов. Численные theta-оценки и Hankel-кампании не выполнялись.

PROGRESS_CLASS: FALSIFICATION_PROGRESS. COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT. ROUTE_SCORE: 4. Весь знаковый потребитель не уменьшен до доказанного положительного интерфейса; сужен класс допустимых условных переносов. Исторический no-source-sign 4 не сбрасывается. Предлагаемый учёт этого законченного опыта после независимого приёма: 4 -> 5; состояние репозитория не изменяется данным предложением.

Memory: выбранный conditional-half-energy профиль теряет фиксированное логарифмическое расстояние в нормированной H_alpha-геометрии на обоих концах. Запрещённое повторение — подгонять только его диагонали или добавлять константы. Следующий дешёвый проверяющий функционал для действительно другого кандидата — тот же двухузловой cross-correlation invariant до большой алгебры.

## 14. Единственная CODEX DIRECTIVE и handoff

Провести независимый PAPER-приём **только** утверждения `CONDITIONAL_HALF_ENERGY_Q_PRIMITIVE_PROFILE_NO_V_TRANSFER`, §§4-11, на точных S1-S3. Проверить телескоп (6), проекцию (12), оба error budgets (17)/(22), полную замену переменных (25), рациональную огибающую (27) и остаток (31). Повторить Appendix A; проверить source-хеши по Appendix B. Не запускать другой профиль, theta-сетку или новую модель Виллена.

Успех: `ACCEPT_NAMED_CONDITIONAL_BROWNIAN_PROFILE_MISMATCH_ONLY`. Отказ: `BROWNIANHODGE_PROOF_GAP` с первой точной формулой и недостающей гипотезой. Ни один результат этого приёма не повышает RH/IC/ODD2 или полный all-order знак.

Публикуется ровно указанный в заголовке новый Markdown в `codex_mac/math-proshka-20260912`, обычной транзакцией поверх синхронизированной ветки. Закрытые ответы не меняются. Lean-файлы: нет. Lake/build/axiom-profile: не запускались и не заявляются. Очередь, runtime, реестры и source-sign counters не редактируются. Commit SHA публикации возвращается в чате и проверяется по GitHub; сам файл не пытается содержать собственный self-referential SHA.


## Appendix A. Полная точная проверка бюджетов

Рабочий каталог: `/mnt/data/brownhodge`. Команда: `python /mnt/data/brownhodge/verify_brownhodge.py`. `N` в конечном calibration-loop — число проверенных экспоненциальных факторов, не подстановка вместо бесконечного доказательства (6)-(7).

```python
from fractions import Fraction as F
from math import prod

# Calibration: the correlation test must accept equality and reject a
# rank-one substitute. These rational matrices are instrument plants,
# not evaluations of the theta source.
rho = F(4, 5)
assert rho - rho == 0
assert rho - F(1) == -F(1, 5)
assert 2*(rho-F(1)) == -F(2, 5)
for a,b in [(F(1),F(1)),(F(2),F(3)),(F(7,5),F(11,4))]:
    aa,bb,ab = a*a,b*b,a*b*rho
    assert ab*ab/(aa*bb) == rho*rho
print('PLANT_EQUALITY=0')
print('PLANT_RANK_ONE_CORRELATION_DEFECT=-1/5')
print('PLANT_DIAGONAL_SCALING_INVARIANT=PASS')
print('PLANT_RESIDUAL_ON_(1,1)=-2/5')

# Check finite telescopes. The proof of the infinite limit is analytic.
for N in range(2, 31):
    P=prod(F(n*n,n*n-1) for n in range(2,N+1))
    S=sum((F(1,n*n-1) for n in range(2,N+1)),F(0))
    assert P==F(2*N,N+1)
    assert S==F(3,4)-F(1,2*N)-F(1,2*(N+1))
print('FINITE_TELESCOPE_CALIBRATION_N_2_TO_30=PASS')

checks = {
    'ROOT_SMALL': F(32)<81,              # 2^(5/4)<3
    'ROOT_LARGE': F(2)<F(6,5)**4,        # 2^(1/4)<6/5
    'E7_LOWER': F(8,3)**7>900,
    'ALPHA_AT_X15': F(3)*2**30>1500,
    'MOMENT_THRESHOLD': F(15,12)<2,
    'SMALL_ETA': F(6,900)<F(1,100),
    'SMALL_CORRELATION': F(9700,10201)>F(19,20),
    'LARGE_EPSILON': F(15,900)==F(1,60),
    'LARGE_CORRELATION': F(59,60)>F(19,20),
    'LAPLACE_RATE': F(7500)/(F(7500)-F(7,2))<F(1001,1000),
    'LAPLACE_LINEAR': 1+1/(F(30)*(F(7500)-F(7,2)))<F(1001,1000),
}
upper = F(62,75)*F(1000,999)**4*F(1001,1000)**2
checks['TARGET_CORRELATION_UPPER'] = upper < F(17,20)
checks['SEPARATION'] = F(17,20)-F(19,20)==-F(1,10)
checks['RESIDUAL_UPPER'] = 2*(F(17,20)-F(19,20))==-F(1,5)
for name,ok in checks.items():
    assert ok, name
    print(name+'=PASS')
print('TARGET_RATIONAL_UPPER='+str(upper))
print('TARGET_MARGIN_TO_17_20='+str(F(17,20)-upper))
print('RATIONAL_CHECKS='+str(len(checks)))
print('SOURCE_EVALUATIONS=0; QUADRATURES=0; HANKEL_SCANS=0; LEAN_RUNS=0')
```

Буквальный stdout:

```text
PLANT_EQUALITY=0
PLANT_RANK_ONE_CORRELATION_DEFECT=-1/5
PLANT_DIAGONAL_SCALING_INVARIANT=PASS
PLANT_RESIDUAL_ON_(1,1)=-2/5
FINITE_TELESCOPE_CALIBRATION_N_2_TO_30=PASS
ROOT_SMALL=PASS
ROOT_LARGE=PASS
E7_LOWER=PASS
ALPHA_AT_X15=PASS
MOMENT_THRESHOLD=PASS
SMALL_ETA=PASS
SMALL_CORRELATION=PASS
LARGE_EPSILON=PASS
LARGE_CORRELATION=PASS
LAPLACE_RATE=PASS
LAPLACE_LINEAR=PASS
TARGET_CORRELATION_UPPER=PASS
SEPARATION=PASS
RESIDUAL_UPPER=PASS
TARGET_RATIONAL_UPPER=2484962480000/2988017988003
TARGET_MARGIN_TO_17_20=1097056196051/59760359760060
RATIONAL_CHECKS=14
SOURCE_EVALUATIONS=0; QUADRATURES=0; HANKEL_SCANS=0; LEAN_RUNS=0
```

SHA-256 исполнявшегося кода: `fa429e6316e20c64b4c129ed1cbf9d72ba5fd5f49f8ae2889fa0c1a90a1273d8`. SHA-256 stdout: `dcf2859e6efc8952e2cfef8fa6db8f86e74fd21b515f1c116616a5fae05dec83`.

## Appendix B. Проверка прочитанных исходных байтов

Рабочий каталог: `/mnt/data/brownhodge`. Команда: `python /mnt/data/brownhodge/verify_pins.py`. `root` — каталог точных локальных копий пяти названных файлов; менять математические данные в `rows` нельзя.

```python
from pathlib import Path
import hashlib
root=Path('/mnt/data/brownhodge')
rows=[
 ('REQUEST.txt',9895,123,'f40965ea88f8ae000af0e31b3e26d7310c2abf8a09bea89a07d8ae4990a1b93d','311885a13b27dcd7573d1855fb91e2f6809f0e70'),
 ('BROWNIAN_PRIMITIVE_FORM.md',10647,206,'accbbc050d41c54cf09927571b24106f2a6a6e84a960cf076b8f4dbf900cd809','5795f0cb8bc580eee843a1a6900f208a62f778d8'),
 ('SLACK_INDEPENDENT_CHECK_2026-09-11.md',37796,467,'14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc','de9578084446baecfbb2a316d7bda3da817c8c01'),
 ('REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md',15303,335,'1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282','b8b5a1a8739c946f75340f3115616d6f9ba5b40e'),
 ('VILLAINPHI_INTAKE.md',11945,223,'3f0b9c6e9e433b643404ceb742c4519a55795fa65a4ac899fc6d94a741d89019','0b7061f8321ebe70e8b42f79010922e602d25276')]
for name,size,lf,sha,blob in rows:
 b=(root/name).read_bytes(); b.decode('utf-8')
 assert len(b)==size and b.count(b'\n')==lf and b.endswith(b'\n') and b'\r' not in b
 assert hashlib.sha256(b).hexdigest()==sha
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
 print(name+': VERIFIED '+str(size)+' bytes / '+str(lf)+' LF / '+sha+' / '+blob)
```

Буквальный stdout:

```text
REQUEST.txt: VERIFIED 9895 bytes / 123 LF / f40965ea88f8ae000af0e31b3e26d7310c2abf8a09bea89a07d8ae4990a1b93d / 311885a13b27dcd7573d1855fb91e2f6809f0e70
BROWNIAN_PRIMITIVE_FORM.md: VERIFIED 10647 bytes / 206 LF / accbbc050d41c54cf09927571b24106f2a6a6e84a960cf076b8f4dbf900cd809 / 5795f0cb8bc580eee843a1a6900f208a62f778d8
SLACK_INDEPENDENT_CHECK_2026-09-11.md: VERIFIED 37796 bytes / 467 LF / 14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc / de9578084446baecfbb2a316d7bda3da817c8c01
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md: VERIFIED 15303 bytes / 335 LF / 1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282 / b8b5a1a8739c946f75340f3115616d6f9ba5b40e
VILLAINPHI_INTAKE.md: VERIFIED 11945 bytes / 223 LF / 3f0b9c6e9e433b643404ceb742c4519a55795fa65a4ac899fc6d94a741d89019 / 0b7061f8321ebe70e8b42f79010922e602d25276
```

SHA-256 исполнявшегося кода: `f25c597638080feb6b4020cca8b938afc5180bf52bee4e9ee413d56a5c1b9031`. SHA-256 stdout: `fa22e0192d8b85aa347dbff4925f8a57dbde02274b33fc9426d8257174381c42`.

## Appendix C. Извлечение только двух ранее доставленных byte frames

Это техническое восстановление S2/S3, не математический поиск в рекурсивном архиве. Полученные Git blobs затем совпали с непосредственно fetched SOURCE_BASE. Команда: `python /mnt/data/brownhodge/extract_pins.py`.

```python
from pathlib import Path
import hashlib,re
spec=[('PROSHKA_REQUEST_GOAL058_LYGSPHI_2026-09-12.txt','docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md','14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc','de9578084446baecfbb2a316d7bda3da817c8c01'),('PROSHKA_REQUEST_GOAL058_ODDINFINITY_2026-09-12.txt','docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md','1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282','b8b5a1a8739c946f75340f3115616d6f9ba5b40e')]
for packet,path,sha,blob in spec:
 b=(Path('/mnt/data')/packet).read_bytes()
 marker=b'===== FILE '+path.encode()+b' BYTES '
 at=b.index(marker); e=b.index(b'\n',at)
 header=b[at:e].decode(); n=int(re.search(r'BYTES (\d+)',header)[1])
 end=b.index(b'===== END FILE '+path.encode()+b' =====',e)
 lines=b[e+1:end].splitlines(keepends=True)
 raw=b''.join(x[2:] for x in lines if x.startswith(b'| '))
 assert len(raw)==n,(path,len(raw),n)
 assert hashlib.sha256(raw).hexdigest()==sha
 got=hashlib.sha1(b'blob '+str(n).encode()+b'\0'+raw).hexdigest()
 assert got==blob,(got,blob)
 (Path('/mnt/data/brownhodge')/Path(path).name).write_bytes(raw)
 print(Path(path).name,n,raw.count(b'\n'),sha,got)
```

Буквальный stdout первого запуска:

```text
SLACK_INDEPENDENT_CHECK_2026-09-11.md 37796 467 14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc de9578084446baecfbb2a316d7bda3da817c8c01
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md 15303 335 1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282 b8b5a1a8739c946f75340f3115616d6f9ba5b40e
```

## Appendix D. Буквальная регистрация ожиданий

```text
CANDIDATE: CONDITIONAL_HALF_ENERGY_Q_PRIMITIVE_PROFILE
J_x = P_alpha k_x; alpha=1/4; k_x as in the controlling request.
Allow arbitrary positive node factors, but no second fitted family.
P1: k_x is a normalized conditional density in D_alpha and J_x is Q_alpha-primitive. Expected true.
P2: the normalized H_alpha correlations of J_x and J_(x+log 2) tend to 1 at each end, rather than the target 4/5. Expected true.
P3: equality with V_f fails even after arbitrary positive diagonal normalization. Expected true.
These expectations are recorded after source intake and before the bounded symbolic verification. They are not predictions of RH or of the sign of V_f.
```

Прогнозы закрыты в §13. Публикация — доставка нового PAPER-доказательства отказа конкретного вложения, не новый дополнительный математический цикл.
