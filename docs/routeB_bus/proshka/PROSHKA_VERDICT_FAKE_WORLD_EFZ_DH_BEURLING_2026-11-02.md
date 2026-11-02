# STATUS: TRY_FAKE_WORLD_EFZ_DH_FLOOR_AND_BEURLING_SOURCE_LOCK

```yaml
OPERATIVE_CLASS: TRY_FAKE_WORLD_EFZ_DH_FLOOR_AND_BEURLING_SOURCE_LOCK
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_FAKE_WORLD_DEPENDENCY_AUDIT
TASK_MODE: PINNED_MATHEMATICAL_REVIEW_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_PRIME_COMPLEMENT_COMMIT: a4ab9e92bf080ee3bcfd729af067ade6fc6392fc
SOURCE_PRIME_COMPLEMENT_BLOB: 88de1569443ba35acdeefdeb64ace9bbb43c47e8
SOURCE_QUIET_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_QUIET_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_INDEX_COMMIT: f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf
SOURCE_INDEX_BLOB: 84b6d256ed2cb30b71949bfcc465c148dbb15a82
SOURCE_CONSTANT_FLOOR_BLOB: 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
DEPENDENCY_AUDIT: COMPLETED
EFZ_EXHAUSTIVE_CLASSIFICATION: false
ADDITIONAL_TAGS_REQUIRED: [ALGEBRA_GEOMETRY, ANALYTIC_CONTINUATION, ZERO_LOCATIONS, ORDINARY_INTEGER_LATTICE]
DH_SOURCE_OPERATOR: CORRECT_ODD_GAMMA_CONDUCTOR_5_NO_POLE_FUNCTIONAL
DH_QUIET_RESIDUAL: PAPER_DERIVED_VIA_ALMOST_PERIODS_NOT_IMPORTED_GONEK
DH_FULL_BOTTOM: TENDS_TO_MINUS_INFINITY_PAPER
DH_COMPLEMENT_BOTTOM: TENDS_TO_MINUS_INFINITY_PAPER
DH_COMPLEMENT_FLOOR: REFUTED_AT_COFINAL_FAMILY_PAPER_SCOPE
KILL_TARGET: DH_SOURCE_CORRECT_UNIFORM_COMPLEMENT_FLOOR
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: ANALYTIC_QUARTET_WITNESS_AND_RAYLEIGH_UPPER_ENVELOPE
KILL_EVIDENCE_REFERENCE: THIS_FILE_SECTIONS_5_6_7
BEURLING_MODEL: DIAMOND_MONTGOMERY_VORHAUER_THEOREM_1
BEURLING_COMPLETED_WINDOW_SOURCE: NOT_SUPPLIED_BY_THAT_THEOREM
BEURLING_SAME_INEQUALITY_VIOLATION: NOT_ESTABLISHED
BEURLING_FINDING: SOURCE_TRANSFER_GAP_NOT_A_NEGATIVE_EIGENVALUE_CERTIFICATE
REQUEST_BOTH_MODELS: PARTIAL_WITH_EXPLICIT_BEURLING_TRANSPORT_BOUNDARY
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
VERIFIER: PAPER
NEW_INDEPENDENT_ANALYTIC_REVIEW: false
EXACT_CONTROL_GROUPS_EXECUTED: 7
DH_EIGENPROBLEMS_COMPUTED: 0
BEURLING_EIGENPROBLEMS_COMPUTED: 0
ZERO_BOX_INTERVAL_CERTIFIED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
RH_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. Основной вывод не симметричен для двух контролей.

**Давенпорт–Хейльбронн (DH):** после правильной замены арифметических коэффициентов, gamma-фактора и полюсных членов доказывается, что полная тихая невязка на moving-kappa графике сверхполиномиальна, но минимум на её ортогональном дополнении стремится к минус бесконечности. Следовательно, аналог запрошенного постоянного complement-floor действительно ложен. Доказательство ниже не устанавливает первый отрицательный m.

**Бёрлинг–DMV:** исходная теорема о генеральных простых не задаёт аналог всей завершённой отражённой формы, theta-радикал и соответствующий J. Поэтому из неё нельзя получить нарушение именно той же complement-оценки. Перенос ломается до этого утверждения. Выдумывать gamma-фактор, отражённые нули или необходимую непрерывность формы нельзя.

Это различие — результат судьи, а не основание остановить исследование. Для DH ниже получен новый PAPER-контроль. Для Бёрлинга указан точный отсутствующий контракт, а не объявлена математическая невозможность.

## 0. Какое именно неравенство проверяется

**[FINITE_CELL | PAPER: сверка закреплённого источника.]** В `a4ab9e9` нет отдельного уравнения с меткой `(5)`. Есть `(5.1)`–`(5.5)`: Abel-тождество, его производная и верхние оценки. Требуемый незакрытый равномерный знак находится в `(3.3)`, эквивалентной форме `(4.3)` и матричной записи `(6.1)`. Поэтому предмет настоящего аудита фиксируется явно:

\[
 \boxed{\mathcal P_m[f]\le \mathcal H_m[f]+\mathcal O_m[f]
                 +C\|f\|_2^2,
 \quad f\in J_m^\perp,\quad C<\infty\text{ независимо от }m.}
 \tag{C}
\]

Квантор потребителя — на одной неограниченной исходной семье; для DH ниже опровергается даже эта более слабая версия. Для исходной zeta-формы

\[
 \mathfrak k_m[f]=\mathcal H_m[f]-c_*\|f\|^2
                     -\mathcal P_m[f]+\mathcal O_m[f].
\]

Таким образом, (C) равносильно постоянному нижнему полу на дополнении. Нельзя называть «опровержением (5)» нарушение другого оператора либо опровержение одного из точных Abel-тождеств.

Ни `(C)` для настоящей zeta, ни новое RH-утверждение здесь не доказываются и не опровергаются.

## 1. Реестр зависимостей: E, F, Z не исчерпывают математику

Обозначения:

* **E:** Euler product самой рассматриваемой функции; для zeta — точные неотрицательные коэффициенты Lambda(p^k)=log p и их prime-power support.
* **F:** конкретное функциональное уравнение и его gamma/pole данные, а не только абстрактная симметрия относительно 1/2.
* **Z:** только численный счёт нулей, включая кратности и оценки хвоста, не расположение отдельных нулей.
* **LA:** линейная алгебра, Fourier-геометрия выбранного окна, интегрирование по частям. Эти действия не являются Z.
* **A:** аналитическое продолжение, полосы роста/убывания, реальные симметрии коэффициентов, фактические координаты нулей.
* **I:** обычная целочисленная структура, например биномиальные коэффициенты и целые частоты Dirichlet-ряда. Одно абстрактное E её не заменяет.

**[ABSTRACT | PAPER: dependency audit of the pinned proofs.]**

| Шаг исходной цепочки | Непосредственный вход | Что не следует автоматически |
|---|---|---|
| `2176dab`: точная rational Fourier-формула carrier, изометрический Gram-переход | LA | Никакая арифметическая положительность |
| `2176dab`: `dim J >= m+1-N(T)` | LA + Z; чётная идентификация симметричных строк использует F/A | Равенство с N(T), простота нулей, независимость повторных строк |
| `2176dab`: Riemann–von Mangoldt/Bellotti–Wong | Z как импорт; доказательство такого счёта опирается на конкретную аналитическую структуру | Та же формула счёта для всякого объекта с E либо с F |
| `2176dab`: все zeta-нули в `0<Re rho<1` | E даёт отсутствие нулей справа от 1; F переносит влево | У DH эта полоса неверна: есть нули правее 1 |
| `2176dab` (3.5)–(3.9): удаление автоматических sinc-нулей | **E + I + A**, через полную формулу Гонека и знак `-Lambda(m)`; Z оплачивает общее число и кратности | Это **не** вывод только из Z; та же формула Гонека не импортируется для DH |
| `2176dab`: Бляшке и оценка хвоста при заданных активных нулях | LA/комплексный анализ + A; Z для суммируемости хвоста | E больше не нужен внутри этой дисковой оценки |
| Отождествление нулевой формы с настоящими prime/arch/pole коэффициентами zeta | E + F + A | Положительность формы из одного тождества |
| `2176dab`: полный residual, затем относительное Gram-неравенство | Предыдущие source-оценки; последний переход LA | Оценка на J-perp |
| `f6c9cd8`: ранг value-матрицы и её kernel | LA + фактические узлы (A), не только Z | Верхний спектральный счёт A |
| `f6c9cd8`: критические пары/off-critical четвёрки | F + вещественный тип (A) и кратности; E не нужен в попарной алгебре | Сохранение инерции после хвоста/сдвига порога |
| `f6c9cd8`: Schur-индекс, coupling, пол из saturation | **LA** | Ни E, ни F не являются условиями теоремы о блоках |
| `a4ab9e9` §2: пол дополнения + bounded residual => полный пол | **LA** | Сам пол дополнения |
| `a4ab9e9` §3: `O=I_L+R` | LA: автокорреляция и чётность f | Что произвольно выбранная O действительно является полюсным членом другой функции |
| `a4ab9e9` §3: `j=e^{-s/2}+j_+`, константа 4 | Конкретный **F_zeta**/gamma/pole контракт + LA | Те же числа и тот же j для conductor-5 odd gamma |
| `a4ab9e9` §4: сумма степеней `p^k`, k>=3 | **E + I**; элементарная суммируемость | Для DH вообще нет такой поддержки; для Бёрлинга меняется постоянная и нужен контроль плотности |
| `a4ab9e9` (5.1)–(5.3): Stieltjes и границы | LA; входная арифметическая мера задана через E | Односторонний знак совместной корреляции |
| `a4ab9e9` (5.5): Chebyshev через binomial/Legendre | **E + I**, а не E абстрактных Beurling primes | Та же численная оценка для произвольных генеральных простых |
| `a4ab9e9` (3.3)/(4.3)/(6.1), то есть (C) | **Открытая source-specific оценка**; E/F находятся в A, Z/A — в определении J | Нельзя присвоить ей тег «доказано из E+F» |
| Унаследованный full floor => RH | Отрицательный witness, dense radical, полный finite return: F/A/Z; E нужен для идентификации zeta-source | Универсальный вывод для неидентифицированного Beurling-оператора |

Нельзя помещать чтение фактических комплексных нулей в категорию «только счёт». Нельзя также объявлять линейную алгебру разновидностью Z: это скрыло бы, какие части обязаны выжить в любом корректном отрицательном контроле.

### 1.1. Два логических исправления к мотивации

**[ABSTRACT | PAPER.]** Из существования F-без-E и E-без-F примеров с off-line zeros следует, что эти два ослабленных набора предпосылок по отдельности недостаточны. Не следует, что произвольно сформулированное `E AND F` достаточно, либо что любое доказательство обязано буквально пользоваться именно этими двумя представлениями.

Более того, DH имеет другой conductor и odd gamma-фактор, а не **точно** функциональное уравнение zeta со всеми её аналитическими гипотезами. Введение в Bombieri–Ghosh напоминает Hamburger uniqueness для точного zeta-уравнения и ordinary Dirichlet-серий. Поэтому «есть F» — классификация структуры, не разрешение сохранять все gamma-константы.

## 2. h-радикальность не является уникальным детектором Euler product

**[ABSTRACT | PAPER.]** Пусть H — чётная entire-функция вещественного типа с нулями z_rho, и форма задана согласованной нулевой суммой

\[
 \mathfrak q(f,g)=\sum_\rho
       \overline{\widehat f(\overline{z_\rho})}\widehat g(z_\rho).
 \tag{2.1}
\]

Если `hat h=H` и классы тестов обеспечивают абсолютную сходимость, то

\[
 \mathfrak q(h^{(2j)},g)=0
\]

потому что `hat h^(2j)(z)=(-1)^j z^(2j)H(z)` зануляется во всех узлах. Здесь нет Euler product. Для zeta полная явная формула переводит этот нулевой факт в точную компенсацию prime-side; для DH такая же компенсация работает с другими, не prime-power, коэффициентами.

Следовательно, утверждение «только у zeta есть тихая theta-радикальная семья» неверно как общий критерий. Отсутствие E не обязано убивать радикальность. Также недостаточно сохранить лишь чётность: нужны рост, плотность, точный source-return.

## 3. Точный DH-оператор, который должен считать Codex

**[COFINAL_FAMILY | PAPER; базовые аналитические свойства и существование zeros >1 — проверенные внешние THEOREM-импорты P1.]** Положим

\[
 t=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}\in(0,1),
\]
\[
 D(s)=\sum_{n\ge1}a(n)n^{-s},\quad
 (a(1),a(2),a(3),a(4),a(5))=(1,t,-t,-1,0),
 \quad a(n+5)=a(n).
 \tag{3.1}
\]

Его completion можно нормировать как

\[
 \Lambda_D(s)=\left(\frac5\pi\right)^{s/2}
      \Gamma\!\left(\frac{s+1}{2}\right)D(s),
 \quad \Lambda_D(s)=\Lambda_D(1-s).
 \tag{3.2}
\]

Умножение completion на постоянную не меняет следующую форму. Она entire, вещественного типа; D — соответствующая линейная комбинация двух primitive odd Dirichlet L-functions mod 5. Это используется только для её аналитических свойств, не для приписывания Euler product самой D.

### 3.1. Коэффициенты логарифмической производной

Определим в достаточно правой полуплоскости

\[
 -\frac{D'}D(s)=\sum_{n\ge2}b_D(n)n^{-s}.
\]

Они однозначно вычисляются рекурсией

\[
 \boxed{b_D(n)=a(n)\log n-
          \sum_{\substack{d\mid n\\1<d<n}}b_D(d)a(n/d).}
 \tag{3.3}
\]

Точно:

\[
 b_D(2)=t\log2,\quad b_D(3)=-t\log3,
\]
\[
 b_D(4)=-(2+t^2)\log2,\qquad
 \boxed{b_D(6)=(1+t^2)\log6\ne0.}
 \tag{3.4}
\]

Значит, ломаются и положительность, и prime-power support. Классифицировать этот ряд как `Lambda_D(p^k)` с нулём на остальных целых нельзя.

Достаточная полуплоскость абсолютной сходимости существует элементарно: при Re s>=2 имеем

\[
 |D(s)-1|\le\sum_{n\ge2}n^{-2}=\zeta(2)-1<1.
\]

Геометрический ряд для 1/D и дифференцирование абсолютно сходящихся рядов дают абсолютную сходимость ряда b_D там. Это не Euler product.

### 3.2. Gamma, полюсы и явная форма

Для физического Fourier-преобразования из исходной задачи положим

\[
 j_D(u)=\frac{e^{-3u/2}}{1-e^{-2u}},\qquad
 c_D=\gamma+\log(8\pi/5)-\pi/2.
\]

На исходном even carrier `N=m, L=log m`:

\[
 \mathcal H_D[f]=\int_0^\infty j_D(u)\|f-T_u f\|_2^2du,
\]
\[
 \mathcal P_D[f]=\sum_{2\le n\le m}\frac{b_D(n)}{\sqrt n}
                       Q_f(\log n),
\]
\[
 \boxed{\mathfrak q_{D,m}[f]
       =\mathcal H_D[f]-c_D\|f\|^2-\mathcal P_D[f].}
 \tag{3.5}
\]

**Полюсной формы `|<p,f>|^2` здесь нет.** У completion DH нет zeta-полюсов 0,1. Чётность f не создаёт отсутствующий полюс.

Проверка arch-константы: arch-multiplier равен

\[
 \log(5/\pi)+\Re\psi(3/4+iu/2).
\]

В нуле он равен `-c_D`, поскольку
`psi(3/4)=-gamma+pi/2-3log2`. Integral representation разности digamma даёт именно j_D. Никакого дополнительного Parseval-фактора в дискретной нулевой сумме нет.

### 3.3. Нулевая идентичность без Euler product

Обозначим `H_D(z)=Lambda_D(1/2-iz)`, `z_rho=i(rho-1/2)`. Тогда

\[
 \boxed{\langle g,A_m^D f\rangle
  =\sum_{\Lambda_D(\rho)=0}
        \overline{\widehat g(\overline{z_\rho})}\widehat f(z_\rho).}
 \tag{3.6}
\]

Все кратности сохранены. Это обычный contour/residue вывод для `Lambda_D'/Lambda_D`: сначала выбрать правую линию Re s>2, где (3.3) абсолютно сходится, затем перенести левую линию посредством (3.2). Gamma-член даёт §3.2, а finite-support корреляция оставляет только n<=m. Euler product на этом шаге не требуется: нужен логарифмический Dirichlet-ряд, а не его особая поддержка.

Переход к нулевым продолжениям cosine-функций законен при фиксированном m через сглаживание. Их Fourier-образы в фиксированной горизонтальной полосе убывают как O_m((1+|Re z|)^-1); произведение абсолютно суммируется по нулям. На source-side поддержка ограничивает арифметическую сумму, а BV-контроль сохраняет endpoint-термы и arch-интеграл.

## 4. Аналитические входы DH и смысл кванторов

**[COFINAL_FAMILY | PAPER.]**

1. Из `|D(s)-1|<1` при Re s>=2 и (3.2) все нули completion находятся в `-1<Re rho<2`. Поэтому `|Im z_rho|<3/2`, а не 1/2 как в исходной zeta-оценке.

2. D(s) не имеет вещественных нулей completion. Для вещественного s>0 группировка по периоду даёт сумму положительных блоков

\[
 [(5k+1)^{-s}-(5k+4)^{-s}]
 +t[(5k+2)^{-s}-(5k+3)^{-s}]>0.
\]

Эта сгруппированная сумма сходится при s>0; оставшиеся вещественные s покрывает (3.2). Поэтому cutoff `0<|Im rho|<T` не пропускает нулей на вещественной оси.

3. В каждой фиксированной горизонтальной z-полосе

\[
 |H_D(z)|\le C_a(1+|\Re z|)^{M_a}e^{-\pi|\Re z|/4},
 \qquad |\Im z|\le a.
 \tag{4.1}
\]

Это следует из Stirling для gamma и polynomial vertical-strip growth конечной комбинации Dirichlet L-functions. Removable точки completion не являются полюсами.

4. Достаточная для хвоста оценка `N_D(T)=O_D(T log(2+T))` следует из конкретной оценки `log max_(|z|<=R) |H_D(z)|=O_D(R log(2+R))` и Jensen, а не из абстрактного order=1 без контроля типа. Для этой completion указанная оценка получается из Stirling и bounded Dirichlet-series на правой стороне; функциональное уравнение переносит левую сторону, а оставшаяся фиксированная вертикальная полоса имеет polynomial growth до умножения на gamma. Поэтому

\[
 \sum_{\gamma\ge T}\gamma^{-2}\le C_D\frac{\log T}{T}
 \quad(T\text{ достаточно велико}).
 \tag{4.2}
\]

5. DH имеет нуль `rho_*=beta_*+i gamma_*` с beta_*>1: это не вывод из decimal near 85.7, а аналитическая теорема, проверенная по Bombieri–Ghosh §5, Theorem 7, q=1, real parameter t. Использование Euler products компонент L в доказательстве этого внешнего факта не даёт Euler product самой DH.

Для отрицательного контроля ниже НЕ нужны численный m0, простота нулей, lower-gap hypothesis, либо точный ранг по числу нулей. Если требуется отдельно посчитать ранг, остаётся прежняя algebraic interpolation формула для фактических узлов. Ненулевой ранг не является скрытой предпосылкой доказательства нарушения пола: при пустом J оно становится утверждением о полном carrier.

## 5. Тихая moving-kappa семья существует у DH без E

**Теорема DH-Q. [COFINAL_FAMILY | PAPER.]** Для

\[
 L=\log m,\quad h=1+\log L,\quad
 \varepsilon=ch/L,\quad T=(1+\varepsilon)2\pi m/L,
 \qquad 0<c<1\text{ фиксировано},
\]

пусть J_m^D — ядро всех actual complex-zero value-условий DH ниже T, на том же even cosine-carrier, а Q_m^D — любой ортонормированный синтез. Тогда существуют постоянные `C_D,H_D^*>0`, зависящие только от DH, такие что для всех достаточно больших m

\[
 \boxed{\|A_m^D Q_m^D\|
 \le C_D m^{3/2}L\varepsilon^{-2}
     \exp\!\left[-\frac{\pi\varepsilon^2m}{96H_D^*L}\right].}
 \tag{5.1}
\]

В частности,

\[
 \boxed{\|A_m^D Q_m^D\|
 \le\frac{C_D}{c^2}\frac{m^{3/2}L^3}{h^2}
 \exp\!\left[-\frac{\pi c^2}{96H_D^*}
                          \frac{mh^2}{L^3}\right]
 =o(m^{-B})\quad\forall B>0.}
 \tag{5.2}
\]

Константы существования здесь не представлены как численно извлечённые.

### 5.1. Не переносим Gonek: строим другой нижний счёт

Выберем диск радиуса r вокруг rho_* из §4, целиком в Re s>1, без нулей на границе. Пусть `a_*=min_boundary |D|>0`.

Абсолютно сходящийся ordinary Dirichlet-ряд D в этой полосе равномерно почти-периодичен по вертикали. Для полноты: хвост ряда мал равномерно; конечная сумма экспонент `exp(-i t log n)` имеет относительно плотные возвраты к единице в замыкании своей траектории на компактном торе; объединение этих двух фактов даёт почти-периоды полного ряда. Это свойство абсолютной сходимости, не multiplicativity коэффициентов.

Существует ell>0, так что каждый интервал длины ell содержит tau с

\[
 \sup_{|s-\rho_*|\le r}|D(s+i\tau)-D(s)|<a_*/2.
\]

По Rouche каждый такой переведённый диск содержит нуль DH и остаётся в Re s>1. Выбирая диски в разнесённых блоках длины

\[
 H_D^*=\ell+4r+1,
\]

получаем для всякой полосы высот `(U,V]` достаточно большой длины W=V-U не менее `W/(2H_D^*)` **различных** нулей. Диски непересекающиеся; кратность не подменяет число различных узлов. Ни один из этих нулей не является автоматическим sinc-нулём, поскольку Re rho>1.

Берём ту же внешнюю подполосу

\[
 U=(1+\varepsilon/3)\Omega,\qquad
 V=(1+2\varepsilon/3)\Omega,\qquad \Omega=2\pi m/L.
\]

Отсюда

\[
 \boxed{k_m^D\ge \frac{\pi\varepsilon m}{3H_D^*L}.}
 \tag{5.3}
\]

Равномерность по положению полосы обеспечена **относительной плотностью почти-периодов**, а не глобальной асимптотикой с неконтролируемым остатком для коротких интервалов. W=epsilon Omega/3 стремится к бесконечности на выбранном графике.

### 5.2. Возврат через Бляшке к полному оператору

Полиномиальная/Fourier геометрия carrier не зависит от arithmetic source. Применяем ту же Joukowski/Бляшке конструкцию `2176dab`:

\[
 \theta=\frac{R(u+v)}{R^2+uv},\qquad
 D_\kappa=\frac{(1+v)^4}{(1-R)^2(1-v)^2},
\]

где

\[
 u=(1+\varepsilon/3-\sqrt{(1+\varepsilon/3)^2-1})^2,
\]
\[
 v=(1+\varepsilon-\sqrt{(1+\varepsilon)^2-1})^2,
 \quad R=(1+u)/2.
\]

Точные elementary bounds остаются

\[
 -\log\theta\ge\varepsilon/32,\qquad
 D_\kappa\le1024\varepsilon^{-2}.
\]

Но `|Im z_rho|<3/2` меняет оценку sine на

\[
 |\sin(z_\rho L/2)|\le m^{3/4}.
\]

Поэтому полный mixed zero-sum даёт, с произвольным единичным g в carrier,

\[
 \|A_m^D|_{J_m^D}\|
 \le 8D_\kappa\frac{(2m+1)m^{3/2}}L
          \left(\sum_{\gamma\ge T}\gamma^{-2}\right)\theta^{k_m^D}.
 \tag{5.4}
\]

Это норма полного образа, не compressed quadratic form. Подставляя (4.2), (5.3) и `T~m/L`, получаем (5.1). Все multiplicities остаются в хвосте, а в Бляшке используются только доказанные различные нули.

Для любого синтеза B пространства J и Gram `G=B*B` автоматически

\[
 B^*(A_m^D)^2B\preceq (\delta_m^D)^2G.
\]

Таким образом, conditioning не прячется в отдельном неоплаченном знаменателе.

**Вывод:** ζ-специфическая proof-route через знак Lambda перестала работать, но её **заключение** о quiet residual для DH восстановлено другим независимым supplier. Нельзя было заключать, что отсутствие E уже опровергло это заключение.

## 6. Полное дно DH уходит к минус бесконечности

**Теорема DH-N. [COFINAL_FAMILY | PAPER.]** Для source-correct A_m^D из §3:

\[
 \boxed{\lambda_{\min}(A_m^D)\longrightarrow-\infty.}
 \tag{6.1}
\]

Ниже дана новая проверка механизма, а не применение zeta-RH эквивалентности к чужой функции.

### 6.1. Явный отрицательный глобальный witness

Пусть z_0 — nonreal spectral zero H_D с Re z_0!=0, точной кратности nu. Отражённая орбита состоит из `z_0,-z_0,bar z_0,-bar z_0` с той же кратностью.

Функция

\[
 G_0(z)=\frac{H_D(z)}{[(z^2-z_0^2)(z^2-\overline{z_0}^{\,2})]^\nu}
\]

entire, real-type и even; её значение в z_0 ненулевое. Поскольку Im(z_0^2)!=0, существуют вещественные a,b, для которых

\[
 G(z)=(a+bz^2)G_0(z),\qquad G(z_0)=i.
 \tag{6.2}
\]

Тогда `G(bar z_0)=-i` и G зануляется во всех остальных нулях H_D. Из (4.1) следует экспоненциальное убывание G на каждой фиксированной горизонтальной полосе. Поэтому его обратное Fourier-преобразование g — вещественная even-функция, все производные которой имеют все экспоненциальные веса в L2; обозначим этот класс S_exp.

Для неё (3.6) содержит только выбранную орбиту:

\[
 \boxed{\mathfrak q_D[g]=-4\nu<0.}
 \tag{6.3}
\]

Это точная конечная сумма, а не отрицательность, выведенная из численного root approximation.

### 6.2. Dense radical не требует E или положительности h

Пусть `hat h_D=H_D`. Все конечные even derivatives h_D^(2j) лежат в S_exp и в radical (2.1).

Их линейная оболочка плотна в even L2. Доказательство: если v even и ортогональна всем этим производным, то все even moments функции

\[
 F(t)=\overline{\widehat v(t)}H_D(t)
\]

равны нулю. Она even, поэтому odd moments также нулевые. По (4.1) и Cauchy–Schwarz F интегрируема с некоторым положительным экспоненциальным весом. Её двустороннее Laplace-преобразование аналитично в полосе и имеет все производные в нуле равными нулю. Оно тождественно нулевое; Fourier uniqueness даёт F=0. Ненулевая entire H_D не обращается в нуль на множестве положительной меры на R, следовательно v=0. Это доказывает плотность.

Выбираем конечный even jet r, сколь угодно близкий к g в L2. При этом точно

\[
 \mathfrak q_D[g-r]=\mathfrak q_D[g]=-4\nu.
\]

Следовательно Rayleigh quotient на S_exp_even не ограничен снизу. Здесь сначала выбирается фиксированный r для заданного отрицательного уровня; никакой increasing-jet limit не переставляется с m.

### 6.3. Полный возврат к исходным диагональным окнам

Для фиксированного g-r гладкие even cutoffs сходятся в каждой экспоненциально взвешенной Sobolev-норме. Нулевая сумма непрерывна в этой топологии: в полосе `|Im z|<=3/2` Fourier-образы имеют любой обратный степенной спад, а `N_D(T)=O(T log T)`. Поэтому для любого M>0 существует **фиксированная** even compact-smooth phi с

\[
 \mathfrak q_D[\phi]/\|\phi\|^2<-2M.
\]

Далее `P_m phi` — projection на тот же carrier с L=log m, N=m. Для каждого K, после того как support phi лежит внутри окна, Fourier-series tail имеет sup- и first-derivative ошибки `O_phi,K((m/L)^(-K))`, с допустимыми log-факторами. Endpoint-значения projection равны значениям этого хвоста, так как phi около концов равна нулю.

Для нулевого продолжения e_m=P_m phi-phi это даёт на каждой фиксированной полосе `|Im z|<=3/2`, при любом A>0,

\[
 |\widehat e_m(z)|\le C_{\phi,A}m^{-A}(1+|\Re z|)^{-1}.
 \tag{6.4}
\]

Доказательство этой конкретной границы: L1-оценка использует длину L и вес `exp(3L/4)=m^(3/4)`; integration by parts использует L1 derivative и **оба** endpoint jump masses. Увеличение K оплачивает все эти полиномиальные множители. Это стандартный фиксированный smooth Fourier-tail estimate, не предположение о спектре A_m.

Подстановка (6.4) в absolutely convergent mixed zero-sum показывает

\[
 \mathfrak q_{D,m}[P_m\phi]\to\mathfrak q_D[\phi],
 \quad\|P_m\phi\|\to\|\phi\|.
\]

Для всех достаточно больших m Rayleigh quotient меньше -M. Так как M произвольно, доказано (6.1).

## 7. Нарушение complement-floor: явный upper witness

**Лемма проекции дна. [ABSTRACT | PAPER.]** Пусть A=A*, `lambda_min(A)=-R<0`, Q изометричен, `||AQ||<=delta<R`. Обозначим `Pi=QQ*`, `G=A|_(J-perp)` в смысле compression. Тогда

\[
 \boxed{\lambda_{\min}(G)
 \le -R+\frac{\delta^2}{R-\delta}.}
 \tag{7.1}
\]

**Доказательство.** Для единичного bottom v имеем

\[
 R\|Q^*v\|=\|Q^*Av\|\le\delta.
\]

Положим x=Pi v, y=(I-Pi)v, a=||x||^2<=delta^2/R^2. Тогда

\[
 \langle y,Ay\rangle=-R+2Ra+\langle x,Ax\rangle
             \le -R+(2R+\delta)a,
\]

`||y||^2=1-a>0`. Деление и монотонность по a дают

\[
 \frac{\langle y,Ay\rangle}{\|y\|^2}
 \le -R+\frac{(R+\delta)a}{1-a}
 \le -R+\frac{\delta^2}{R-\delta}.
\]

Это admissible **upper** Rayleigh envelope. Следовательно он может опровергать нижний пол; направление неравенств не перепутано.

**Следствие DH-C. [COFINAL_FAMILY | PAPER.]** Из DH-Q и DH-N:

\[
 \boxed{\lambda_{\min}\bigl(U_m^*A_m^D U_m\bigr)\to-\infty,
       \qquad\operatorname{ran}U_m=(J_m^D)^\perp.}
 \tag{7.2}
\]

Source-correct аналог (C) для DH —

\[
 \mathcal P_D[f]\le\mathcal H_D[f]+C\|f\|^2,
          \quad f\perp J_m^D.
 \tag{C-DH}
\]

Он равносилен `q_D[f]>=-(C+c_D)||f||^2`. Для любого фиксированного C величина

\[
 U_m(C)=-R_m+\frac{(\delta_m^D)^2}{R_m-\delta_m^D}+C+c_D
 \longrightarrow-\infty.
 \tag{7.3}
\]

Как только U_m(C)<0, нормированный y из доказательства (7.1) нарушает (C-DH). Это происходит на **всех достаточно поздних m**, следовательно ни одна неограниченная подпоследовательность не спасает постоянный C.

Итак, для корректного DH-source строгий отрицательный контроль проведён: quiet residual и exact index сохраняются, а искомый complement-floor ложен. Это не доказывает, что E автоматически даёт пол для zeta; это доказывает, что пол не является следствием одной тихой геометрии, reflection symmetry и zero count.

## 8. Бёрлинг: где действительно обрывается перенос

**[COFINAL_FAMILY | PAPER: точная граница импортируемой теоремы.]** P3 (Diamond–Montgomery–Vorhauer, Theorem 1) строит для `1/2<theta<1` и подходящего a генеральные простые с

\[
 N_{\mathcal B}(x)=\varkappa x+O(x^\theta),\quad
 \zeta_{\mathcal B}(s)=\prod_{p\in\mathcal B}(1-p^{-s})^{-1}
       \quad(\Re s>1),
\]

meromorphic continuation в `Re s>=theta`, единственным полюсом s=1 в этой области, и бесконечными нулями

\[
 \Re\rho=1-a/\log|\Im\rho|>1/2
\]

на поздних высотах. Теорема также задаёт сильные PNT/oscillation свойства. Это реальный E-контроль, не произвольное «плохое распределение точек».

### 8.1. Что сохраняется

Logarithmic derivative имеет настоящую положительную prime-power меру

\[
 -\zeta'_{\mathcal B}/\zeta_{\mathcal B}(s)
   =\int x^{-s}\,d\psi_{\mathcal B}(x),\quad
 d\psi_{\mathcal B}=\sum_{p\in\mathcal B,k\ge1}\log p\,\delta_{p^k}.
\]

Abel/Stieltjes identity исходного §5 остаётся верной с этой мерой и корректными endpoints. Суммируемость k>=3 тоже переносится при `p_min>1` и `pi_B(x)=O(x)`, которые у рассматриваемых систем обеспечены integer count:

\[
 |\mathcal P_{\mathcal B}^{\ge3}[f]|
 \le \frac{2}{1-p_{\min}^{-1/2}}
     \left(\sum_{p\in\mathcal B}\frac{\log p}{p^{3/2}}\right)\|f\|^2.
\]

Это конечная **system-dependent** постоянная, не zeta-константа C3<28. Нельзя заменять множество генеральных простых подмножеством натуральных чисел, а Legendre/binomial proof Chebyshev в прежнем виде не переносится.

### 8.2. Чего теорема DMV не предоставляет

Она не предоставляет для этого source:

1. entire completion с конкретным gamma-фактором и равенством `Lambda_B(s)=Lambda_B(1-s)`;
2. full-plane reflected zero divisor с нужным ростом;
3. theta/Fourier H_B с плотной S_exp-радикальной derivative-семьёй;
4. тождество, отождествляющее prime measure с **тем самым** even Weil operator, включая arch/pole terms;
5. analogue full residual на `J_m^B` в данной диагональной семье.

Часть отражённых точек `1-rho` лежит левее области `Re s>=theta`, где указанная теорема даёт продолжение. Их нельзя добавлять как будто это известные нули zeta_B.

Важно уточнить: из вещественных коэффициентов можно искусственно построить некоторую real-even Hermitian zero-form уже по conjugate pairs. Поэтому проблема не формулируется как «без F невозможно написать самосопряжённую матрицу». Проблема — **нет доказанного равенства этой искусственной формы настоящей Beurling arithmetic form**, нет нужного completion/dense-radical/finite-return контракта. Самосопряжённость по определению не исправляет это.

### 8.3. Почему отсюда не следует нарушение именно (C)

Логическая цепочка имеет вид

\[
 \text{source identification + negative witness + dense radical/return
       + bounded quiet residual + (C)}\ \Longrightarrow\ \bot.
\]

Для DH все предпосылки до (C) проверены выше. Для DMV они не предоставлены. Отсутствие F — провал предпосылок переноса, а не доказательство отрицания последнего неравенства.

Можно по желанию **определить** matrix с теми же zeta-arch/pole terms и с заменой Lambda на psi_B. Это будет конкретный искусственный оператор. Но его связь с известными zeros zeta_B, выбранным J_B и constant-floor implication требует нового доказательства. Нельзя назвать нарушение или выполнение такого оператора свойством исходной DMV-zeta без этого шага.

Поэтому затребованный вывод «(C) доказанно нарушено для DMV в тех же координатах» здесь **не установлен**. Не проведена и его численная подмена. Это точный source-transport finding, не отрицание возможности отдельной Beurling-теоремы.

## 9. Судьба двух исходных ставок K6

**[FINITE_CELL | CONDITIONAL: финитный эксперимент не выполнен.]**

* Ставка 0.6: первая отрицательность при прохождении Omega через около 85.7. **NOT_TESTED.** Выше доказана eventual divergence, а не first onset. Finite cosine Fourier-transforms имеют sinc-хвосты: Omega не является жёсткой границей их поддержки. Ни равенство Omega=gamma0, ни факт первого off-line zero не дают автоматический индекс первого отрицательного окна. Опубликованное значение около `0.808517+85.699348 i` служит ориентиром, не локальным интервальным сертификатом этой работы.
* Ставка 0.55: DH имеет тихую семью, а пол на дополнении ломается. **QUALITATIVE_COFINAL_MECHANISM_CONFIRMED_IN_THIS_PAPER_DERIVATION**, при source-correct DH definition. Фраза «так же» не означает копирование Gonek или zeta-gamma: использованы Rouche/almost periods, более широкая полоса нулей, другой arch-kernel и отсутствие полюса. Поведение при m=20..120 не измерено.

Новые зарегистрированные algebra-controls: DH b(6) не должен исчезнуть; projection upper имеет знак (7.1); Schur identity остаётся верной; gamma constant должна смениться. Все 7 exact-control groups прошли. Они не заменяют независимого analytic review DH-Q/DH-N.

## 10. Минимальный следующий объект и две репрезентации

**Для zeta:** эта работа не оплачивает prime/square signed complement estimate. Она устанавливает, что supplier должен отличать её арифметику от DH, даже после сохранения quiet-space геометрии.

**Для Beurling:** минимальный отсутствующий контракт — не ещё один список нулей. Нужны выбранная система, completed/arithmetical form, точный test class, real-even carrier, source equality с remainder, определение J и full residual. Не требуется заранее навязывать всю zeta-completion: достаточно более слабого интерфейса, который действительно даёт negative-witness return и bounded quiet residual для того же оператора.

| Репрезентация | Что меняет решение | Сила / цена |
|---|---|---|
| DH source-first: все b_D(n), explicit odd-gamma kernel, then Schur/complement | Одна строгая отрицательная upper enclosure для q_D на admissible y подтверждает finite failure; source/zero matching отличает арифметический дефект от ошибки прибора | Высокая / умеренная |
| Beurling compensated Stieltjes form как самостоятельный источник | Может дать direct negative competitor без несуществующего theta; нужен полный arch/pole/source contract и перенос в явно определённый complement | Высокая при наличии источника / высокая |
| Reflected zero-model только как algebraic planted control | Проверяет pairing, multiplicities и negative witness; **не** идентифицирует DMV-source и не является его доказательством | Умеренная / низкая |

DISCRIMINATOR: при zero-consistent numerical result вычислять полный Rayleigh upper для конкретного unit witness и full interval source/zero discrepancy. Отдельные float signs, нормы residual или одиночные zero-coordinates не сертифицируют отрицательность. Для Beurling first discriminator — существует ли verified source identity; отсутствие такого identity нельзя маскировать eigensolver-результатом.

### Единственная CODEX DIRECTIVE

`SOURCE_CORRECT_DH_NEGATIVE_CONTROL`: строить (3.5) с рекурсией (3.3) на **всех целых n<=m**, kernel `exp(-3u/2)/(1-exp(-2u))`, scalar c_D и **без** zeta-pole rank-one term. До большой серии проверить b_D(3), b_D(6), функциональное уравнение completion, физический Gram и полную явную формулу на малом наборе mixed tests с zero-tail enclosure. Затем исходный N=m, L=log m; J использует **все фактические complex zeros ниже T**, а не только критические ordinates. Для найденного отрицательного bottom вернуть его certified Rayleigh upper, полную ||AQ||, projection witness (7.1), и нарушенный budget (C-DH) при заранее фиксированном C. First onset не объявлять m, где Omega пересекает 85.7. Beurling-source не конструировать путём неоговорённого добавления reflected zeros или gamma terms. Никаких изменений route-state/RH exports.

## 11. Meta closeout и dependency contract

**Что стало меньше:** DH-контроль доведён до конкретного complement upper envelope (7.3); quiet-space перенос закрыт альтернативным almost-periodic proof, а не оставлен предположением. Beurling-тест отделён от неидентифицированного spectral surrogate.

**Что опровергнуто:** существование постоянного source-correct DH-пола на moving-kappa complement, в смысле (C-DH), COFINAL_FAMILY/PAPER. Не исходный zeta-floor, не все possible Beurling approaches, не вся Route B.

**Что нельзя повторять:** автоматически переносить zeta-Gonek на DH; обрезать b_D(n) до prime powers; сохранять zeta pole у entire DH; считать radicality уникальной для Euler product; превращать отсутствие F в отрицательный eigenvalue неуказанной матрицы.

DOWNSTREAM_CONSUMER: constant floor for the unchanged literal zeta CCM family.
ACTUAL_CONSUMER_REQUIREMENT: uniform complement floor plus bounded full quiet residual and the pinned negative-witness/dense-radical return theorem.
ORIGINAL_REQUESTED_OBJECT: E/F/Z audit and proved failure of the analogous floor in two fake worlds.
ORIGINAL_OBJECT_IS: NOT_NECESSARY for the zeta proof; it is a falsification/control design.
KNOWN_WEAKER_INTERFACES: a source-correct finite negative Rayleigh certificate can validate a negative-control detector; it does not prove cofinal failure by itself. Lemma (7.1) transfers divergence with merely bounded delta, not necessarily superpolynomial delta.
FAILURE_TYPE_FOR_BEURLING: NO_SOURCE for the requested completed-window counterpart; not COUNTEREXAMPLE to its floor.
EPISTEMIC_STATUS_FOR_BEURLING: RESEARCH_DEBT.
REOPEN_TRIGGER_FOR_BEURLING: pin a concrete arithmetic/completed form and verify its negative-witness and quiet-residual transfer, or provide a direct prime-side admissible negative witness.
KILL_SCOPE_FOR_DH: THEOREM_SHAPE.
KILL_EVIDENCE_FOR_DH: exact negative quartet (6.3), admissible all-late finite return, and strictly negative upper envelope (7.3).
NOVELTY_AXIS: DH full quiet residual via right-half-plane almost periods; explicit projection-to-complement kill; dependency/source audit.

Memory entry:

```yaml
iteration:
  target: fake_world_dependency_discriminator
  status: PROGRESS
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: quiet_radical_and_even_geometry_survive_without_the_functions_own_Euler_product
  forbidden_future_move: infer_Beurling_complement_failure_without_identifying_its_operator_and_return
  next_decisive_test: source_correct_DH_Rayleigh_certificate_with_all_logderivative_coefficients
```

## 12. Источники и проверка

### Repository pins

S1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, commit `2176dab16bf77dd015f7efcb5a6f704587f732c8`, blob `ebf7f8cab61a795118bda5dc7e65a0b3386247b7`. Прочитаны определение и математические шаги, отдельно повторно §§3–4.

S2. `docs/routeB_bus/proshka/PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md`, commit `f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf`, blob `84b6d256ed2cb30b71949bfcc465c148dbb15a82`. Прочитаны pairing/rank/Schur/tail obligations.

S3. `docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_COMPLEMENT_FLOOR_2026-11-02.md`, commit `a4ab9e92bf080ee3bcfd729af067ade6fc6392fc`, blob `88de1569443ba35acdeefdeb64ace9bbb43c47e8`. Прочитан полностью. В нём uniform complement bound НЕ заявлен доказанным.

S4. `docs/routeB_bus/proshka/NOESCAPE_CONSTANT_FLOOR_REDUCTION_2026-10-31.md`, fetched at `a4ab9e9`, blob `26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7`. Прочитан полностью; DH-вывод §6 дан отдельно, не приписан этому zeta-source.

### Primary public sources

P1. E. Bombieri, A. Ghosh, *Around the Davenport–Heilbronn function*, Russian Mathematical Surveys 66:2 (2011), 221–270, DOI `10.1070/RM2011v066n02ABEH004740`. Использованы definition/functional equation в §5.1, analytic off-line/right-half-plane existence (Theorem 7), и описание almost-periodicity в §2.2. Последний механизм также доказан непосредственно в §5.1 настоящего файла.

`https://www.mathnet.ru/links/3a48ba618035d15eef32e551dc91b8b2/rm9410_eng.pdf`

P2. E. P. Balanzario, J. Sánchez-Ortiz, *Zeros of the Davenport–Heilbronn counterexample*, Mathematics of Computation 76 (2007), 2045–2049, DOI `10.1090/S0025-5718-07-01999-0`. Использовано определение и опубликованный ориентир near 85.699; никакой decimal root из этой статьи не используется как interval certificate настоящей работы.

`https://citeseerx.ist.psu.edu/document?doi=dccc1914d446d2c22ce2d2b3fd9a04619f4e68fe&repid=rep1&type=pdf`

P3. H. G. Diamond, H. L. Montgomery, U. M. A. Vorhauer, *Beurling primes with large oscillation*, Mathematische Annalen 334 (2006), 1–36, DOI `10.1007/s00208-005-0638-2`. Проверены формулировка Theorem 1, область продолжения, Euler/log-derivative identities и границы того, что эта теорема поставляет.

`https://deepblue.lib.umich.edu/bitstream/handle/2027.42/46253/208_2005_Article_638.pdf`

Public PDF text was retrieved. Requested web PDF screenshots returned Cache miss; an attempted local retrieval also failed. Therefore this record does **not** claim a successful visual PDF inspection. All imported formulas used here were present in extracted text, cross-checked between DH sources where applicable; no graph or image-only data were used.

### Проверки и honesty boundary

Выполнены 7 групп точных SymPy-проверок, код приведён ниже. Нового скана DH/Beurling/CCM, interval-root certification, Lean build, независимого аналитического аудита или Git write не было. PAPER proofs §5–7 требуют независимого source/analysis review; запись файла сама такого статуса не даёт.

## Appendix. Исполняемые точные проверки

Запуск: сохранить блок как `fake_worlds_exact_checks.py`, затем выполнить

```sh
uv run --with sympy fake_worlds_exact_checks.py
```

```python
#!/usr/bin/env python3
"""Exact controls for the fake-world audit; not a CCM eigensolver.
Predictions registered before tests: DH log derivative is not prime-power supported;
negative-bottom projection has the stated upper envelope; odd gamma changes the
kernel and removes the zeta pole functional.
"""
import sympy as s

tau=s.symbols('tau',real=True)
A={n:({1:s.Integer(1),2:tau,3:-tau,4:-s.Integer(1),0:s.Integer(0)}[n%5]) for n in range(1,25)}
b={1:s.Integer(0)}
for n in range(2,25):
    b[n]=s.expand(A[n]*s.log(n)-sum(A[n//d]*b[d] for d in s.divisors(n) if 1<d<n))
assert s.expand_log(b[2],force=True)==tau*s.log(2)
assert s.expand_log(b[3],force=True)==-tau*s.log(3)
assert s.simplify(s.expand_log(b[4]+(2+tau**2)*s.log(2),force=True))==0
assert s.simplify(s.expand_log(b[6]-(1+tau**2)*s.log(6),force=True))==0
print('PASS 1 DH: b(2), b(3), b(4), b(6), including non-prime-power support')

R,d=s.symbols('R d',positive=True)
a=s.symbols('a',nonnegative=True)
f=(-R+(2*R+d)*a)/(1-a)
assert s.simplify(f-(-R+(R+d)*a/(1-a)))==0
assert s.simplify(f.subs(a,d**2/R**2)-(-R+d**2/(R-d)))==0
print('PASS 2 bottom-to-complement upper envelope; domain R>d')

nu=s.symbols('nu',positive=True)
assert s.simplify(nu*(s.I**2+s.I**2+(-s.I)**2+(-s.I)**2)) == -4*nu
print('PASS 3 reflected quartet witness has energy -4 nu')

c0=s.EulerGamma+s.log(8*s.pi/5)-s.pi/2
assert s.simplify(s.expand_log(s.polygamma(0,s.Rational(3,4))+s.log(5/s.pi)+c0,force=True))==0
print('PASS 4 DH gamma scalar c_D = gamma + log(8pi/5) - pi/2')

L,h,c,H=s.symbols('L h c H',positive=True)
m=s.symbols('m',positive=True)
eps=c*h/L
expr=s.pi*eps**2*m/(96*H*L)
assert s.simplify(expr-s.pi*c**2*m*h**2/(96*H*L**3))==0
assert s.simplify(m**s.Rational(3,2)*L/eps**2 - m**s.Rational(3,2)*L**3/(c**2*h**2))==0
print('PASS 5 moving-band DH Blaschke budget substitution')

x,B,G,mu=s.symbols('x B G mu',real=True)
Ablock=s.Matrix([[x,B],[B,G]])
U=s.Matrix([[1,B/(mu-x)],[0,1]])
result=s.simplify(U.T*(Ablock-mu*s.eye(2))*U)
expected=s.diag(x-mu,G-mu+B**2/(mu-x))
assert s.simplify(result-expected)==s.zeros(2)
print('PASS 6 Schur inertia identity is source-independent algebra')

for n in range(2,25):
    lhs=sum(A[n//d]*b[d] for d in s.divisors(n) if d>1)
    assert s.simplify(lhs-A[n]*s.log(n))==0
print('PASS 7 full coefficient convolution through n=24')
print('NO zero location certified. NO literal DH or Beurling eigensystem computed.')
```