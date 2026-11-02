# STATUS: TRY_PRIME_SIDE_COMPLEMENT_FLOOR

```yaml
OPERATIVE_CLASS: TRY_PRIME_SIDE_COMPLEMENT_FLOOR
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_PRIME_SIDE_COMPLEMENT_REQUEST
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
SOURCE_FLOOR_COMMIT: e724ae65ed39a8ba8b8f07c928d790ea9820342a
SOURCE_FLOOR_BLOB: 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_RESIDUAL_AUDIT_BLOB: 4e6165039aaa6e5d52774413ca39de596be409bd
SOURCE_INDEX_COMMIT: f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf
SOURCE_INDEX_BLOB: 84b6d256ed2cb30b71949bfcc465c148dbb15a82
SOURCE_INDEX_SHA256: f1e6e3634a5829744c98faeb9e3e01535fd29c0ac976c50fefb19bdc0ea97e34
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: REQUESTED_UNIFORM_COMPLEMENT_BOUND_NOT_PROVED
REQUESTED_LITERAL_CCM_ASSERTION_REFUTED: false
NEW_ESTIMATES_USE_ZERO_SIDE: false
QUIET_SPACE_AND_RESIDUAL: INHERITED_SUPPLIERS_NOT_REPROVED_WITHOUT_ZEROS
POLE_CONTINUUM_CANCELLATION: EXACT
STIELTJES_ARITHMETIC_REMAINDER: EXACT_WITH_BOTH_ENDPOINTS
HIGHER_PRIME_POWERS_K_GE_3: UNIFORM_EXPLICIT_OPERATOR_BOUND
PRIMITIVE_PRIMES_AND_SQUARES_JOINT_SIGN: NOT_PROVED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
NEW_COFINAL_SOURCE_SIGN: NONE
VERIFIER: PAPER
SYMBOLIC_CONTROL_GROUPS: 6
NEW_CCM_EIGENPROBLEMS: 0
INDEPENDENT_ANALYTIC_REVIEW: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Ответ

Требуемая константа, независимая от m на неограниченной исходной семье, **не доказана**. Отсутствие доказательства не объявляется опровержением утверждения для CCM.

Ниже выполнена прямая арифметическая попытка: полюс точно сокращён с непрерывным главным членом, остаток записан через действительную лестницу von Mangoldt, все степени p^k при k>=3 оплачены одной постоянной. Не получен равномерный односторонний контроль оставшегося совместного вклада простых, квадратов и непрерывного компенсатора на J_m-perp.

Это не новая положительность дополнения и не новый достаточный критерий вместо запрошенного. Переписывание источника не выдается за доказательство знака. Высокие степени не удалены: их полная цена сохранена.

## 1. Закреплённые входы и смысл «без нулей»

Прочитаны через GitHub:

- `NOESCAPE_CONSTANT_FLOOR_REDUCTION_2026-10-31.md` на e724ae6: определение полного источника, постоянный-floor supplier и его граница.
- `PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md` на 2176dab, (0.1)–(0.5): исходное J_m, фиксированное 0<c<1, kappa_m=1+c(1+log log m)/log m и полный residual delta_m=||A_m Q_m||.
- `SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_PAPER_AUDIT_2026-11-02.md` на e724ae6: независимый PAPER audit подтверждает перечисленные rank/residual входы. Это не новый аудит в данной сессии.
- `PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md` на f6c9cd8: блоки D,B,G, цена связи и ограничение области действия Schur-формулы. Локальный Git blob и SHA-256 пересчитаны; blob совпал с GitHub.

J_m здесь дан из запроса. Его определение использует нули, а доказательство унаследованного residual использовало нулевую сторону. В НОВОЙ попытке оценить арифметический знак эта сторона не используется: нет сумм по нулям, zero-location гипотез, переноса на критическую прямую или положительности неучтённого нулевого хвоста. Импортированная геометрия J_m не называется заново доказанной без нулей.

Новая арифметика ниже использует только определение Lambda(p^k)=log p, положительность этих коэффициентов, конечные суммы, интегралы и линейную алгебру. Справочная нормировка Lambda сверена с NIST DLMF §27.2; внешняя асимптотическая теорема о простых не импортируется.

## 2. Связь блоков действительно оплачена — она не является новым препятствием

**[FINITE_CELL | PAPER.]** Положим J=J_m, Pi=Q Q*, E=I-Pi. В ортонормированном разложении J плюс J-perp:

    A = [[D, B*], [B, G]],  ||D|| <= delta,  ||B|| <= delta,
    delta = ||A Q||.

Сохраняется именно полный residual, не только ||D||. Если новая оценка запроса доказана с C>=0, то

    G >= -M I,  M=C+c_*,  c_*=gamma+log(8 pi)+pi/2.

Для x in J, y in J-perp:

    k[x+y] >= -delta ||x||²-2 delta ||x|| ||y||-M ||y||².

Значит

    lambda_min(A) >= -[M+delta+sqrt((M-delta)²+4 delta²)]/2
                   >= -max(M,delta)-delta.                 (2.1)

Это доказательство использует лишь минимальное собственное значение указанной вещественной 2x2-формы. При delta_m->0 получаем постоянный нижний пол. Унаследованный supplier из e724ae6 затем даёт RH. Эта последняя импликация принадлежит закреплённой цепочке; она не является новым арифметическим доказательством.

Утверждение на J_m тоже правильно: k[j]>=-delta_m||j||². Никакого дополнительного spectral-gap условия для (2.1) нет. Нельзя, однако, обратить (2.1) и получить нижнюю оценку G из малого delta.

## 3. Точное сокращение полюса — только со стороны простых

**[FINITE_CELL | PAPER; для всего исходного вещественного чётного carrier.]** Продолжаем f нулём. L=log m, b=L/2, N=||f||². Обозначим

    Q_f(s)=2 integral_R f(x)f(x+s) dx,
    P_m[f]=sum_(2<=n<=m) Lambda(n)n^(-1/2) Q_f(log n),
    p(x)=sqrt(2) cosh(x/2),  O[f]=|<p,f>|²,
    j(s)=exp(-s/2)/(1-exp(-2s)),
    A[f]=integral_0^infinity j(s)||f-T_s f||² ds.

Q_f(0)=2N, Q_f(L)=0; Q_f(s)=0 for s>=L. Даже для n=m корреляция равна нулю, так что атом на правой границе не создаёт неоплаченного члена.

Положим

    I_L[f]=integral_0^L exp(s/2)Q_f(s) ds,
    R[f]=integral_0^L exp(-s/2)Q_f(s) ds,
    S_m[f]=P_m[f]-I_L[f].

Тогда точно

    O[f]=I_L[f]+R[f].                                      (3.1)

Доказательство: для C_f(s)=Q_f(s)/2 его двусторонний Laplace-интеграл равен произведению integral exp(x/2)f и integral exp(-x/2)f. Чётность f делает эти два множителя равными. Разбить интеграл на s>0 и s<0 и учесть p=sqrt(2)cosh(x/2). Ни одной оценки нулей здесь нет.

Кроме того,

    j(s)=exp(-s/2)+j_+(s),
    j_+(s)=exp(-5s/2)/(1-exp(-2s)),
    H_+[f]=integral_0^infinity j_+(s)||f-T_s f||² ds >=0.

Следовательно

    A[f]=H_+[f]+4N-R[f],
    P_m[f]-A[f]-O[f]=S_m[f]-H_+[f]-4N.                    (3.2)

Это точное сохранение ВСЕХ полюсных и архимедовых членов. В частности, запрос эквивалентен

    S_m[f] <= H_+[f]+(4+C)||f||²,  f in J_m-perp.          (3.3)

Формула (3.3) не поставляет эту оценку. Она показывает, какая подписанная арифметическая часть осталась после законного сокращения главного члена. В частности, оценивать P_m и I_L независимо и затем объявлять их разность ограниченной нельзя.

## 4. Полная цена степеней p^k, k>=3, действительно постоянна

**[COFINAL_FAMILY | PAPER; каждый m и весь carrier, не только J_m-perp.]** Определим

    P_m^(>=3)[f]=sum_(p^k<=m, k>=3) (log p)p^(-k/2) Q_f(k log p).

Из |Q_f(s)|<=2||f||²:

    |P_m^(>=3)[f]| <= C_3 ||f||²,
    C_3=(1+sqrt(2))(8+5 log 2) < 28.                       (4.1)

Точная константа, не округлённое число, используется далее.

Доказательство. Суммирование всей геометрической прогрессии и увеличение множества простых до целых дают

    sum_p sum_(k>=3) (log p)p^(-k/2)
       <= [1/(1-2^(-1/2))] sum_(n>=2) (log n)n^(-3/2).

Функция log x/x^(3/2) убывает для x>=2. Поэтому

    sum_(n>=2) (log n)n^(-3/2)
       <= (log 2)/2^(3/2)+integral_2^infinity (log x)x^(-3/2)dx
       = (log 2)/2^(3/2)+(2 log 2+4)/sqrt(2).

Умножение на 2/(1-2^(-1/2)) даёт (4.1). Все кратности простых степеней считаются по фактическому Lambda(p^k)=log p; n=p^6 присутствует именно как k=6. Никакой квадрат или куб не считается простым числом. Это обычная абсолютная оценка только равномерно суммируемого сектора, не оценка всей компенсированной формы по модулю.

Положим

    S_m^(1,2)[f]
      =sum_(p<=m) (log p)/sqrt(p) Q_f(log p)
       +sum_(p<=sqrt(m)) (log p)/p Q_f(2 log p)
       -I_L[f].                                          (4.2)

Тогда S_m=S_m^(1,2)+P_m^(>=3). Достаточно доказать, с одной K,

    S_m^(1,2)[f] <= H_+[f]+K||f||² on J_m-perp.            (4.3)

Она дала бы запрос с C=K+C_3-4 (при необходимости увеличенным до 0). Обратно, запрос влечёт (4.3) с K=C+4+C_3. Таким образом, существование постоянной эквивалентно после конечного изменения бюджета. Это не доказательство (4.3). Квадраты не выброшены: без специального совместного аргумента их сумма не относится к равномерно суммируемому сектору k>=3.

## 5. Прямая Abel-попытка и её точный остаток

**[FINITE_CELL | PAPER.]** Пусть

    psi(x)=sum_(n<=x) Lambda(n),
    E_0(x)=psi(x)-(x-1),  x>=1.

Для исходного конечного Fourier-carrier корреляция Q_f абсолютно непрерывна на [0,L]. При

    w_f(x)=x^(-1/2)Q_f(log x)

имеем E_0(1)=0 и w_f(m)=0. Стилтьесово интегрирование по частям даёт

    S_m[f]=integral_(1,m] w_f(x)dE_0(x)
          =integral_1^m E_0(x)x^(-3/2)
             [Q_f(log x)/2-Q_f'(log x)] dx.                (5.1)

Не потерян нижний endpoint: замена E_0 на psi(x)-x без дополнительного члена 2||f||² изменила бы равенство. Правый endpoint равен нулю даже при m=p^k. Граничные скачки нулевого продолжения f также сохранены:

    Q_f'(s)=2 integral_(-b)^(b-s) f(x)f'_int(x+s)dx
             -2 f(b-s)f(b),  0<s<L.                       (5.2)

При Omega=2 pi m/L и d_m=2m+1 имеем

    |Q_f'(s)| <= [2Omega+2d_m/L]||f||²,
    |Q_f(s)|/2 <= ||f||².                                 (5.3)

Это следует из Bernstein-оценки для конечных мод, Cauchy–Schwarz и точного point-evaluation upper sqrt(d_m/L)||f||. Поэтому абсолютный перенос (5.1) предоставляет лишь

    |S_m[f]| <= [1+2Omega+2d_m/L]||f||²
                  integral_1^m |E_0(x)|x^(-3/2)dx.         (5.4)

Оценка (5.4) не доказана ограниченной по m; она не даёт требуемую константу. Ограничение f in J_m-perp само не сокращает правую часть: для такого вывода нужна отдельная совместная оценка фактических корреляций этого подпространства с E_0. Здесь она не получена.

Для сравнения, доступен полностью элементарный upper всей prime-формы:

    P_m[f] <=16(log 2)sqrt(m)||f||².                       (5.5)

Доказательство без PNT и без нулей: psi(2n)-psi(n)<=log binom(2n,n)<=2n log2, поскольку каждое p^k in (n,2n] даёт единицу в соответствующей Legendre-строке биномиального коэффициента. Телескопирование на степенях двойки и монотонность дают psi(x)<=4(log2)x для x>=1. Частичное суммирование даёт sum_(n<=m)Lambda(n)/sqrt(n)<=8(log2)sqrt(m), затем |Q_f|<=2||f||² даёт (5.5).

Поскольку A и O неотрицательны, (5.5) даёт лишь растущую допустимую цену. Это НЕ нижняя оценка требуемой оптимальной константы и НЕ контрпример целевой оценке. Результат остановившейся попытки: потеря совместного знака при переходе от (5.1) к (5.4), а не математическая невозможность исходной задачи.

## 6. Почему малая невязка не завершает арифметическую часть

**[ABSTRACT | PAPER; контроль, не другая CCM-семья.]** Для произвольного растущего r_m матрица diag(0_(r_m),-m,1,...) имеет delta_m=0 на указанном тихом пространстве, связь B=0 и неограниченно отрицательное дополнение. Этот контроль опровергает только вывод из residual и связи. Он не опровергает target для литеральных простых.

Новый source-объект, который ещё требуется, можно записать без нулевой суммы: для любого ортонормированного синтеза U_m на J_m-perp нужна одна конечная C и неограниченная семья, на которой

    U_m* [ A_arch,m + p_m p_m* + C I - Prime_m ] U_m >=0.   (6.1)

Это ровно запрошенный знак, не новый supplier. Все матрицы в квадратных скобках строятся по исходным prime-power/archimedean/pole формулам. U_m задаёт только уже определённое подпространство. Определить факторизацию (6.1) через квадратный корень предполагаемо положительной матрицы было бы кругом.

## 7. Две допустимые формы следующей попытки и дискриминатор

1. Совместная Stieltjes-форма (5.1), с конечными correlation matrices на U_m. Требуется односторонняя матричная оценка против H_+, а не верхняя оценка |E_0| отдельно. Сила: высокая для всей семьи; стоимость: умеренная для проверки конечной формулы, высокая для нового кофинального знака.
2. Независимая prime-side сумма квадратов для (6.1) с явно неотрицательным остатком. Факторы должны быть заданы из арифметики, не из неизвестной положительной части искомого оператора. Сила: максимальная для закрытия семейства; стоимость: высокая. Факторизация в данном батче не построена.

Проверенные стыки: ортогональное блочное исключение оплачивает перенос; pole/continuum convolution даёт точную компенсацию; Abel summation переводит остаток в совместное арифметическое спаривание. Ни один из трёх стыков не создаёт отсутствующую оценку знака.

DISCRIMINATOR: независимый нижний envelope минимального eigenvalue (6.1) для заранее фиксированного C; при нуль-согласованном интервале нужен точный положительный фактор либо более узкое полное enclosure. Конечный положительный результат не заменяет неограниченный квантор. Новых CCM-сканов здесь не было.

Единственная CODEX DIRECTIVE: PRIME_COMPLEMENT_ARITHMETIC_AUDIT. Проверить (3.1)–(5.3), константу (4.1), endpoint x=1 и все powers. Не повышать статус target после аудита тождеств. Для настоящего supplier требуется независимый lower envelope (6.1) с одним C на неограниченной семье; не использовать нулевую сторону для нового знака и не заменять complement residual-оценкой тихого блока.

## 8. Closeout и граница результата

DOWNSTREAM_CONSUMER: constant lower floor for the literal CCM, then pinned RH implication.
ACTUAL_CONSUMER_REQUIREMENT: fixed complementary lower floor plus bounded full quiet residual.
ORIGINAL_REQUESTED_OBJECT: uniform prime-side inequality on J_m-perp.
ORIGINAL_OBJECT_IS: sufficient; equivalent to the full-floor interface up to bounded block costs on the inherited schedule.
FAILURE_TYPE: NO_DERIVATION of the required uniform signed arithmetic estimate.
EPISTEMIC_STATUS: RESEARCH_DEBT, not MATHEMATICALLY_DEAD.
REOPEN_TRIGGER: independent joint signed estimate (4.3) or positive source certificate (6.1).
NOVELTY_AXIS: no claim of a new CCM sign theorem; explicit source accounting and bounded higher-power sector only.

До исполнения кода зарегистрированы P1: continuum/pole нормировка должна сохранять коэффициент 4; P2: в Abel-формуле нужен E_0(1)=0 либо явный endpoint; P3: малый quiet residual сам не контролирует complement. Все подтверждены шестью exact-control groups. Код не проверяет кофинальную оценку, спектр CCM, RH или гипотезы о нулях.

Что оплачено: весь равномерно суммируемый сектор p^k, k>=3, с явной постоянной. Что НЕ оплачено: (4.3)/(6.1). Что не повторять: выдавать компенсированное тождество за upper, переходить к unsigned Psi-ошибке без оплаты её цены, переносить delta на дополнение.

VERIFICATION HANDOFF: новый Markdown только в docs/routeB_bus/proshka/ на ветке proshka_inbox_2026-10-31; при успешной доставке commit SHA сообщается отдельно. Старые файлы, rh_clean, Lean и route-state не изменяются. Lean axiom profile неприменим: Lean source не писался. Самопроверка не является независимым аналитическим аудитом. Одна Git-запись доказывает только доставку файла.

## Appendix. Exact controls

Извлечь следующий блок и выполнить `uv run --with sympy prime_complement_checks.py`.

```python
#!/usr/bin/env python3
"""Exact controls, not a CCM spectrum or a proof of a uniform floor.
Registered before execution: retain the pole compensator, lower endpoint,
and prime powers. A quiet residual alone must not certify its complement.
Run: uv run --with sympy prime_complement_checks.py
"""
import sympy as s

x, L = s.symbols('x L', positive=True)
q = 2*(1-x/L)
plus = s.integrate(s.exp(x/2)*q, (x, 0, L))
minus = s.integrate(s.exp(-x/2)*q, (x, 0, L))
pole = 8*(s.exp(L/2)+s.exp(-L/2)-2)/L
assert s.simplify(plus+minus-pole) == 0
print('PASS 1 exact continuum/pole identity on normalized constant test')

j = s.exp(-x/2)/(1-s.exp(-2*x))
jplus = s.exp(-5*x/2)/(1-s.exp(-2*x))
assert s.simplify(j-jplus-s.exp(-x/2)) == 0
P, Aplus, norm2, R = s.symbols('P Aplus norm2 R')
Iplus = s.symbols('Iplus')
A = Aplus+4*norm2-R
O = Iplus+R
S = P-Iplus
assert s.expand(P-A-O-(S-Aplus-4*norm2)) == 0
print('PASS 2 compensated form and coefficient 4')

# m=4, Q(s)=2(1-s/log4). Exact interval-by-interval Abel check.
a = s.log(4)
w = 2*x**(-s.Rational(1,2))*(1-s.log(x)/a)
W = 4*s.sqrt(x) - (4*s.sqrt(x)*s.log(x)-8*s.sqrt(x))/a
assert s.simplify(s.diff(W,x)-w) == 0
exact = s.log(2)*w.subs(x,2)+s.log(3)*w.subs(x,3)+s.log(2)*w.subs(x,4)-(W.subs(x,4)-W.subs(x,1))
abel = 0
for left,right,psi in [(1,2,0),(2,3,s.log(2)),(3,4,s.log(2)+s.log(3))]:
    e0=psi-x+1
    abel += -(e0*w).subs(x,right)+(e0*w).subs(x,left)-(W.subs(x,right)-W.subs(x,left))
assert s.simplify(exact-abel) == 0
assert w.subs(x,4) == 0
print('PASS 3 Abel identity, x=1 boundary and n=m endpoint')

bound = s.log(2)/2**s.Rational(3,2)+s.integrate(s.log(x)/x**s.Rational(3,2),(x,2,s.oo))
c3=2*bound/(1-1/s.sqrt(2))
assert s.simplify(c3-(1+s.sqrt(2))*(8+5*s.log(2))) == 0
print('PASS 4 exact higher-power constant')

for M in (8,16,27,64,200):
    lhs={}
    for n in range(2,M+1):
        fac=s.factorint(n)
        if len(fac)==1:
            p,k=next(iter(fac.items()))
            if k>=3: lhs[n]=s.log(p)/s.sqrt(n)
    rhs={}
    for p in list(s.primerange(2,M+1)):
        v=p**3
        while v<=M:
            rhs[v]=s.log(p)/s.sqrt(v)
            v*=p
    assert lhs==rhs
print('PASS 5 all higher prime powers counted once with weight log p')

# Abstract falsifier: not a replacement for the literal CCM.
N=s.symbols('N',positive=True)
AA=s.diag(0,-N,1)
Q=s.Matrix([1,0,0])
assert AA*Q==s.zeros(3,1)
assert AA[1,1]==-N
D,B,G,C=s.symbols('D B G C',real=True)
mat=s.Matrix([[D,B],[B,G]])
assert s.expand(mat.det()-(D*G-B**2))==0
print('PASS 6 quiet residual does not bound complementary negative energy')

```
