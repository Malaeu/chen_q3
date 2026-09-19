# STATUS: TRY_THETA_POISSON_FULL_BALANCE_ON_LITERAL_SEED
```yaml
OPERATIVE_CLASS: TRY_THETA_POISSON_FULL_BALANCE_ON_LITERAL_SEED
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-19
SOURCE_COMMIT: 9cc72f08b10fa78fae1233a8474d74b13917112a
SOURCE_ENERGY_BLOB: 01c0d23e17a2e3dff8e4b8dace501a49e532c4ed
PROTOCOL_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SCOPE: ABSTRACT
VERIFIER: PAPER
THETA_SPECIFIC_ALL_POLYNOMIAL_IDENTITY: DERIVED
POSITIVE_FACTORIZATION_OF_TRUE_THETA: NOT_PROVED
GLOBAL_THETA_SIGN: NOT_PROVED
COMPENSATION_OVER_t: PRESERVED
ALL_LATTICE_CROSS_TERMS: PRESERVED
LITERAL_WORKING_SEED_CHANGED: false
SECONDARY_FINDING: KILL_SELFDUAL_POSITIVE_THETA_CLASS_AS_SUFFICIENT_SIGN_HYPOTHESIS
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXPLICIT_POSITIVE_MODIFIED_THETA_SOURCE_WITH_OFF_AXIS_ROOTS
KILL_EVIDENCE_REF: SECTION_5
ORIGINAL_XI_REFUTED: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
LEAN_RUN: false
ARB_RUN: false
NEW_INTERVAL_CERTIFICATE: false
EXACT_SYMBOLIC_CHECKS: EXECUTED_AND_REPLAYED
NUMERICS: DIAGNOSTIC_ONLY
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
PROGRESS_CLASS: REPRESENTATION_PROGRESS_AND_SCOPED_FALSIFICATION
GLOBAL_QUANTIFIER_PROGRESS: NONE
ROUTE_SCORE: 3
INDEPENDENT_REVIEW: PENDING
PRIORITY_CLAIM: NONE
CODEX_DISPATCHED: false
PRODUCTION_STATE_CHANGED: false
```

Ы. Получено точное theta-специфическое представление полного энергетического баланса для любого фиксированного полинома. Оно не является положительной факторизацией. Проверка показывает, что одной положительности источника и самодуальности Пуассона недостаточно: существует явное семейство положительных theta-источников с той же самодуальностью и дополнительными внеосевыми нулями. Рабочая Phi не заменяется этим семейством.

## 0. Неизменный объект и источники

[ABSTRACT][PAPER] Прочитан действующий протокол через GitHub, включая окончание. Прямой источник: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GLOBAL_ORTHOGONAL_ENERGY_PREFLIGHT_2026-09-19.md` на SOURCE_COMMIT. Сохраняются

\[
\Phi(t)=\sum_{n\ge1}(4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2})e^{-\pi n^2e^{2t}},
\quad F(p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt=\xi(1/2+p).
\]

Пусть \(f_s=e^{st}\Phi\), \(D=-i\partial_t\), \(E_s(P)=\|P(D)f_s\|_2^2\). Полином P фиксирован при всех производных по s. Используется ненормированный функционал

\[
\mathcal L_\sigma(P\overline P)=\frac2\sigma E'_\sigma(P),\qquad \sigma>0.
\]

Обозначим именно запрошенный полный баланс

\[
\mathcal B_\sigma(P)=\int_0^\sigma\left[
2\|P(D)(tf_s)\|_2^2-\|P'(D)f_s\|_2^2
-\Re\langle P''(D)f_s,P(D)f_s\rangle\right]ds.
\]

Из ранее выведенного двойного антикоммутатора, либо прямого дифференцирования нормы,
\(E_s''=4\|P(D)(tf_s)\|^2-2\|P'(D)f_s\|^2-2\Re\langle P''(D)f_s,P(D)f_s\rangle\).
Чётность полного F даёт \(E'_0=0\), поэтому

\[
\mathcal B_\sigma(P)=\tfrac12E'_\sigma(P),\qquad
\mathcal L_\sigma(P\overline P)=\frac4\sigma\mathcal B_\sigma(P).
\tag{0.1}
\]

Старая ошибочная формула интегрирования по частям из d62163e8 не используется. Старые численные и интервальные сертификаты не запускаются и не повышаются в статусе. Внешний импорт ниже — формула Пуассона для Schwartz-функций [S1]; преобразование гауссиана и интегральные конвенции сверены с [S2]. Все специальные пересчётки и контрольное семейство выведены здесь.

## 1. Буквальный theta-источник как сумма одного зерна

[ABSTRACT][PAPER] Для переменной x, отличной от логарифмической t, зададим

\[
h(x)=(4\pi^2x^4-6\pi x^2)e^{-\pi x^2},\qquad
A=x\partial_x+\tfrac12.
\]

Пусть \(\mathfrak F u(\xi)=\int u(x)e^{-2\pi i x\xi}dx\). Это не конвенция e^{-i tau t} для логарифмической переменной. Прямое дифференцирование гауссиана даёт

\[
\mathfrak Fh=h,\qquad h(0)=\int h=0,\qquad
\mathfrak F A=-A\mathfrak F.
\tag{1.1}
\]

Например, \(\mathfrak F(x^2e^{-\pi x^2})=(1/(2\pi)-\xi^2)e^{-\pi\xi^2}\) и
\(\mathfrak F(x^4e^{-\pi x^2})=(\xi^4-3\xi^2/\pi+3/(4\pi^2))e^{-\pi\xi^2}\). Подстановка именно коэффициентов 4 pi^2 и -6 pi доказывает (1.1).

Определим

\[
(\mathcal Eu)(t)=e^{t/2}\sum_{n\ge1}u(ne^t).
\]

Тогда, буквально по исходному ряду,

\[
\boxed{\Phi=\mathcal Eh,\qquad \partial_t\mathcal Eu=\mathcal E(Au).}
\tag{1.2}
\]

Если u чётна и u(0)=integral u=0, формула Пуассона даёт

\[
\boxed{\mathcal Eu(-t)=\mathcal E(\mathfrak Fu)(t).}
\tag{1.3}
\]

Нулевые решётчатые члены отсутствуют вследствие обоих условий, а не отбрасываются. Для A^j h оба условия сохраняются: (Au)(0)=u(0)/2 и integral Au=-(integral u)/2. Все функции — полиномы, умноженные на гауссиан.

## 2. Перенос произвольного полинома до любого усечения

[ABSTRACT][PAPER] Положим

\[
h_{s,P}=P(-i(A+s))h,\qquad P^\vee(X)=P(-X).
\]

Из (1.1)–(1.3) следуют точные равенства для каждого P in C[X]:

\[
\boxed{P(D)f_s=e^{st}\mathcal E h_{s,P},}
\tag{2.1}
\]
\[
\boxed{\mathfrak Fh_{s,P}=h_{-s,P^\vee},\qquad
\partial_s h_{s,P}=-i h_{s,P'}.}
\tag{2.2}
\]

В первом равенстве (2.2) нет комплексного сопряжения коэффициентов P: Fourier-преобразование линейно. Отражение P^vee обязательно.

Это конечная полиномиальная операция над фиксированным h, а не новый неизвестный ряд производных log Phi. В координате z=pi x^2 пишем

\[
h_{s,P}(x)=R_{s,P}(z)e^{-z},
\quad
R_{s,P}=P\left(-i\left[2z\partial_z+s+\tfrac12-2z\right]\right)(4z^2-6z).
\tag{2.3}
\]

При deg P=d имеем deg R<=d+2. Формула (2.3) задаёт операторное применение: степени заключённого в скобки дифференциального оператора действуют последовательно на 4z^2-6z. Она не означает подстановку скаляра вместо оператора.

## 3. Тождество для полного баланса

[ABSTRACT][PAPER] Введём полные, неусечённые суммы

\[
S_{s,P}(x)=\sum_{n\ge1}h_{s,P}(nx),\qquad x>0,
\]

и одну подписанную скобку

\[
J_{s,P}(x)=\log x\,|S_{s,P}(x)|^2
-\Im\big(S_{s,P}(x)\overline{S_{s,P'}(x)}\big).
\tag{3.1}
\]

Тогда для каждого фиксированного P и каждого sigma>0:

\[
\boxed{
\mathcal B_\sigma(P)=\int_1^\infty
\left[x^{2\sigma}J_{\sigma,P}(x)
-x^{-2\sigma}J_{-\sigma,P^\vee}(x)\right]dx.
}
\tag{3.2}
\]

Следовательно, \(\mathcal L_\sigma(P\overline P)\) равна 4/sigma, умноженному на правую сторону (3.2). Это именно полный баланс из §0. Ни один член внутри J не объявляется положительным.

Доказательство. Подстановка x=e^t в (2.1) даёт

\[
E_s(P)=\int_0^\infty x^{2s}|S_{s,P}(x)|^2dx.
\]

Формула Пуассона, применённая к полному h_{s,P}, даёт
\(S_{s,P}(1/x)=xS_{-s,P^\vee}(x)\). Поэтому

\[
\boxed{E_s(P)=\int_1^\infty
\left[x^{2s}|S_{s,P}|^2+x^{-2s}|S_{-s,P^\vee}|^2\right]dx.}
\tag{3.3}
\]

Дифференцируем (3.3), используя partial_s S_{s,P}=-iS_{s,P'}. Производная первой ветви равна 2 x^{2s}J_{s,P}; второй — -2 x^{-2s}J_{-s,P^vee}. Деление на два и (0.1) доказывают (3.2).

Законность операций. Для каждого фиксированного d и компактного s-интервала существует C such that на x>=1

\[
|S_{s,P}(x)|+|\partial_s S_{s,P}(x)|
\le C(1+x^{2d+4})e^{-\pi x^2}.
\]

Оценка получается суммированием n^{2d+4}e^{-pi(n^2-1)}, конечным независимо от x>=1. Та же оценка с другой константой действует для любого фиксированного числа производных. Поэтому произведения, логарифмические множители и их интегралы абсолютно сходятся. Малая полуось x<1 оплачена точной формулой Пуассона, а не незаконной почленной перестановкой до компенсации. При sigma=0 используется предел (0.1), а не деление на ноль.

В квадратах S остаётся вся двойная сумма по n,m, включая n!=m. В отличие от искусственного чётного продолжения конечного дивизорного пакета, (3.2) получено из полной Poisson-пары до каких-либо усечений. Оно не утверждает положительность отдельных пар или конечных голов.

## 4. Проверки нормировки и реальная граница результата

[FINITE_CELL][PAPER FOR EXACT ALGEBRA; NUMERICAL VALUES DIAGNOSTIC_ONLY] check_exact.py проверяет Fourier-самодуальность h, перенос производных до степени 6, независимые Fourier-пересчётки для 1, X, X^2-8 и 1+iX+X^2. Намеренное удаление P^vee отвергается. Аналитические доказательства §§1–3 работают для всех степеней независимо от этих конечных тестов.

Независимый диагностический расчёт сравнивает (3.2)–(3.3) с xi-интегралами на спектральной стороне при sigma=1/4:

| P | E_sigma(P) | B_sigma(P) |
|---|---:|---:|
| 1 | 0.32073569658215859789 | 0.00394131776217137536 |
| X^2-8 | 64.33991553343313603 | 1.11978544298403823344 |

Максимальное относительное расхождение исполненных вариантов меньше 3e-26. Эти числа не являются интервальными сертификатами: диагностические срезы n<=7, x<=5, tau<=80 отдельно не сертифицированы. Согласие служит только проверкой транскрипции, не поставщиком знака. Два ранних запуска диагностики остановлены лимитом инструмента; исходная программа и частичный вывод сохранены. Итоговый вариант завершил обе строки.

[ABSTRACT][PAPER] Из положительности энергии (3.3) не следует знак её производной (3.2). Само тождество Якоби также не даёт этот знак. Следующая точная проверка существенно сильнее абстрактного предупреждения: она остаётся внутри класса положительных theta-сумм самодуальных гауссово-полиномиальных функций.

## 5. Строгий контроль против автоматического вывода из самодуальности

[ABSTRACT][PAPER] Только в этом разделе меняется контрольный источник. Для R>=10 положим

\[
\Psi_R=\frac{\Phi^{(4)}+2R^2\Phi''+(R^4+1)\Phi}{R^4+1}.
\tag{5.1}
\]

Это не рабочая Phi. Тем не менее Psi_R имеет ту же точную форму theta-суммы:

\[
\Psi_R=\mathcal E h_R,\qquad
h_R=\frac{(A^2+R^2)^2+1}{R^4+1}h.
\]

Поскольку операторный полином чётен по A,
\(\mathfrak Fh_R=h_R\) и \(h_R(0)=\int h_R=0\). Поэтому Psi_R чётна по той же формуле Пуассона.

### 5.1. Положительность всего контрольного источника

Для T0(z)=4z^2-6z зададим T_(j+1)=2zT_j'+(1/2-2z)T_j. Числитель одного атома (5.1) равен

\[
Q_R(z)=T_4(z)+2R^2T_2(z)+(R^4+1)T_0(z).
\]

Пусть r=z-3>=0 и u=R^2-100>=0. Точная полиномиальная алгебра даёт

\[
\begin{aligned}
8Q_R(r+3)={}&512r^6+768r^5+9408r^4+72960r^3
+348850r^2+1032777r+979929\\
&+u(256r^4+1280r^3+6736r^2+23304r+23112)\\
&+u^2(32r^2+144r+144)>0.
\end{aligned}
\tag{5.2}
\]

На t>=0 все атомы имеют z=pi n^2e^{2t}>3, поэтому Psi_R(t)>0. Чётность переносит знак на всю прямую. Все суммы и производные сохраняют сверхэкспоненциальное убывание. Это аналитическое доказательство для каждого R>=10, не сетка по R.

### 5.2. При этом преобразование имеет внеосевые нули

Четыре интегрирования по частям в полной Laplace-формуле дают

\[
F_R(p)=\int\Psi_R(t)e^{pt}dt
=\frac{(p^2+R^2)^2+1}{R^4+1}F(p).
\tag{5.3}
\]

В частности, F_R(0)=F(0): якорная нормировка сохранена. Явный нуль:

\[
p_R=\alpha_R+i\beta_R,\quad
\alpha_R=\sqrt{\frac{\sqrt{R^4+1}-R^2}{2}},\quad
\beta_R=\sqrt{\frac{\sqrt{R^4+1}+R^2}{2}}.
\]

Имеем
\(0<\alpha_R<1/(2R)\le1/20<1/2\), \(\beta_R>R\), и \((p_R^2+R^2)^2+1=0\). Никакого предположения о нулях F не требуется: дополнительный множитель уже даёт нуль F_R.

Строгая отрицательная верхняя оболочка полного знака существует в той же полосе. Запишем F_R(p)=(p-p_R)^m a(p) в малом диске, где m>=1 и a не обращается в ноль. На горизонтальном отрезке зададим a_min=min|a|>0, C=max|a' conjugate(a)|<infinity. Для достаточно малого delta>0, с delta<alpha_R и delta C<=m a_min^2/2, получаем

\[
\boxed{4\Re\big(F_R'(p_R-\delta)\overline{F_R(p_R-\delta)}\big)
\le-2m a_{min}^2\delta^{2m-1}<0.}
\tag{5.4}
\]

Это отрицательность полного преобразованного объекта контрольного источника, не локального слагаемого. Точная область запрета: положительность источника, Fourier-самодуальность гауссово-полиномиального зерна, нулевые значения/масса зерна и тождество Пуассона вместе не влекут знак H во всей целевой полосе. Конкретный h степени 4 этим не опровергнут: h_R имеет другую степень и другие коэффициенты. Прежние дополнительные оценки кривизны и моментных миноров для Psi_R здесь не заявляются.

### 5.3. Контрольные источники приближают настоящий

[COFINAL_FAMILY][PAPER] В каждом Schwartz-полунорме

\[
\Psi_R-\Phi=\frac{2R^2\Phi''+\Phi^{(4)}}{R^4+1}\longrightarrow0.
\]

На каждом компактном множестве p также F_R->F локально равномерно. Добавленные нули уходят на высоту beta_R->infinity, поэтому противоречия с Гурвицем нет. Следовательно, одной малой ошибки источника в любом фиксированном конечном наборе таких норм вместе с перечисленными симметриями недостаточно для универсального Fourier-знака. Более сильные специальные достаточные условия этим не исключаются.

## 6. Открытый вход и выбор следующего представления

[COFINAL_FAMILY][CONDITIONAL] Для буквального h=(4 pi^2 x^4-6 pi x^2)exp(-pi x^2) остаётся доказать неотрицательность всей правой стороны (3.2) для всех P и 0<sigma<=1/2. Она не доказана и не названа нормой.

R1, основной: положительный разбор полной Poisson-парной формы (3.2), использующий именно коэффициенты зерна 4z^2-6z. Решительность при all-order успехе 10/10; стоимость следующего структурного теста 4/10; оценка стоимости глобального доказательства не установлена. Минимальный содержательный вход — тождество или нижняя оболочка всей формы, а не знак J или отдельного n,m.

R2: нелокальная факторизация исходного полного ядра, задающая фактор до предположения о его спектральном знаке и сохраняющая точное обратное равенство. Решительность 10/10; первый тест явного кандидата 4/10; глобальная стоимость не установлена. Формальное назначение Fourier(h)=sqrt(Fourier(K)) запрещено до доказательства знака.

MINIMAL_MISSING_IDENTITY: positive representation of (3.2) on the literal degree-four seed for every fixed polynomial P, or an equivalent vanishing-error lower-envelope family. Общая самодуальность не может занимать этот слот по §5.

DISCRIMINATOR: полный B_sigma(P), с неизменным h. PASS допустим только от нижней оболочки >=0. KILL полного знака потребовал бы отрицательной верхней оболочки для этого же объекта; §5 предоставляет её только для изменённого источника. Интервал, содержащий ноль, требует точного тождества или сходящихся оплаченных оболочек.

## 7. Предсказания, самопроверка и зависимости

[ABSTRACT][PAPER] registration.json записан после ручного построения кандидата, но до символьных тестов. P_DILATION_TRANSPORT (0.97) и P_DUAL_FOLD (0.95) подтверждены как тождества, не как знак. P_SELFDUAL_NOT_SIGN (0.85) подтверждено положительным изменённым источником при R=10. Расширение R>=10 зарегистрировано отдельно после просмотра полинома при R=10; это post-exploration validation, не слепой прогноз. Его точный полиномиальный тест подтверждён. Исходы находятся в prediction_fates.json.

STRONGEST ATTACK: формула (3.2) всё ещё представляет неизвестный знак, а не уменьшает его универсальный квантор. Это верно. Результат — точная спецификация действия всей theta-структуры и доказанная граница обобщения, не найденная положительная факторизация. Старые общие антикоммутаторные формулы сами по себе theta-теоремой не стали.

K8A:
- DOWNSTREAM_CONSUMER: H>=0 for all tau and 0<sigma<=1/2; horizontal monotonicity then excludes off-axis zeros.
- ACTUAL_CONSUMER_REQUIREMENT: sign of the unchanged full source, not all positive selfdual sources.
- ORIGINAL_REQUESTED_OBJECT: theta-specific identity for the full compensated balance.
- ORIGINAL_OBJECT_IS: NOT_NECESSARY in this exact representation; a direct full-sign proof is an alternative.
- KNOWN_WEAKER_INTERFACES: whole-form nonnegative lower envelopes with vanishing error; full positive autocorrelation factorization.
- FAILURE_TYPE: NO_DERIVATION for true-theta positivity; COUNTEREXAMPLE for the enlarged selfdual-source sufficient hypothesis.
- EPISTEMIC_STATUS: RESEARCH_DEBT for true-theta sign; MATHEMATICALLY_DEAD only the enlarged implication of §5.
- REOPEN_TRIGGER: a literal-seed coefficient-sensitive identity that survives the modified-source control by using a hypothesis that this control does not satisfy.
- NOVELTY_AXIS: explicit all-polynomial Poisson transport and full positive selfdual theta-source control; bibliographic priority not claimed.

META CLOSEOUT: получено (3.2) для любого P с сохранением полной компенсации. Общий знак не получен. Не повторять перенос знака из самодуальности или близости источников; не приписывать свойствам h_R свойства исходного h. Новый сертификат моментной матрицы не строился. Memory: operator=REPRESENTATION_SHIFT; invariant=literal seed plus full Poisson pairing; next_decisive_test=whole-form literal-seed identity, not a new moment grid.

CODEX: не назначен. Lean-файлы и production-state не изменяются. VERIFICATION HANDOFF: записывается только этот новый Markdown в docs/routeB_bus/proshka/. Lean/Arb не запускались; аксиомный профиль не заявляется. WORKDIR для проверок — каталог извлечённого архива; команды приведены в RUN.txt. Повтор символьной алгебры не заменяет независимую проверку аналитических доказательств и не сертифицирует диагностическую квадратуру.

## Внешние источники

[S1] NIST DLMF §1.8(iv), equation 1.8.14: Poisson summation. https://dlmf.nist.gov/1.8#iv

[S2] NIST DLMF §1.14(i): Fourier transform conventions and Gaussian identities. https://dlmf.nist.gov/1.14#i

[S3] NIST DLMF §20.7(viii): Jacobi modular transformations. https://dlmf.nist.gov/20.7#viii

Эти источники не утверждают положительность исследуемого theta-баланса. Новые формулы §§2–5 — собственные выводы, а не импорт готового RH-результата.
