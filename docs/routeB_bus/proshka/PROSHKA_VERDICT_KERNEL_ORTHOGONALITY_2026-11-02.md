# STATUS: TRY_PRIME_KERNEL_CORRELATION_REMAINDER
```yaml
OPERATIVE_CLASS: TRY_PRIME_KERNEL_CORRELATION_REMAINDER
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_PROVE_BOUND_OR_IDENTIFY_EXACT_UNCANCELLED_TERM
TASK_MODE: MATHEMATICAL_RESPONSE_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
SOURCE_PRIME_COMMIT: a4ab9e92bf080ee3bcfd729af067ade6fc6392fc
SOURCE_PRIME_BLOB: 88de1569443ba35acdeefdeb64ace9bbb43c47e8
SOURCE_PRIME_SHA256: 3a827900de98c45d02ce617f606c4a0ab1fa7b337ed846ea12f7eb9db301b3fa
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_INDEX_COMMIT: f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf
SOURCE_INDEX_BLOB: 84b6d256ed2cb30b71949bfcc465c148dbb15a82
SOURCE_FLOOR_COMMIT: e724ae65ed39a8ba8b8f07c928d790ea9820342a
SOURCE_FLOOR_BLOB: 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: EXACT_UNCANCELLED_KERNEL_PAIRING_IDENTIFIED
REQUESTED_UNIFORM_BOUND: NOT_PROVED
REQUESTED_BOUND_REFUTED: false
ALTERNATIVE_REQUEST: FULFILLED_BY_EXPLICIT_MEMBER_AND_LITERAL_COMPLEMENT_WITNESS
NEW_ZERO_SIDE_SIGN_USED: false
ZERO_INFORMATION_USED: INHERITED_EVALUATION_NODES_AND_EXISTENCE_OF_ACTIVE_EXTERIOR_NODE_ONLY
SOURCE_REMAINDER: JOINT_PSI_CORRELATION_MATRIX_WITH_PHYSICAL_GRAM
ENDPOINT_ANNIHILATION_ON_COMPLEMENT: FALSE_ON_INHERITED_LATE_SCHEDULE
BULK_DERIVATIVE_ANNIHILATION_ON_ZERO_TRACE_SLICE: FALSE_WHEN_DIM_COMPLEMENT_GE_2
PROGRESS_CLASS: REPRESENTATION_PROGRESS
NEW_COFINAL_ARITHMETIC_SIGN: NONE
VERIFIER: PAPER
EXACT_CONTROL_GROUPS: 6
NEW_CCM_EIGENPROBLEMS: 0
INDEPENDENT_ANALYTIC_REVIEW: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
```

## 0. Ответ и источники

**Постоянная в (5) не доказана. Выполнена вторая альтернатива запроса:** ниже указан точный член (6), который не сокращается от f perpendicular J_m. Он вычислен в настоящих оконных ядрах, с физической Gram-метрикой, полным moving-boundary членом и всеми простыми степенями. На том же дополнении построен явный единичный вектор с ненулевым граничным следом. Это не контрпример требуемой верхней оценке: несокращение отдельного члена не запрещает совместную арифметическую компенсацию.

S1: PRIME_COMPLEMENT_FLOOR на a4ab9e9, §§3–5. В файле формулы, названные (5),(6),(7) в сообщении, имеют номера (4.3),(5.1),(5.2). Локальные байты полного S1 сверены с его Git blob; SHA-256 указан выше.
S2: SHRINKING_KAPPA_INTERPOLATION_RESIDUAL на 2176dab, (0.1)–(0.5), §3.3.
S3: QUIET_SPACE_INDEX на f6c9cd8, §§2–4. Его локальные байты также совпали с закреплённым blob; SHA-256 f1e6e3634a5829744c98faeb9e3e01535fd29c0ac976c50fefb19bdc0ea97e34.
S4: NOESCAPE_CONSTANT_FLOOR_REDUCTION на e724ae6, supplier и граница результата.

Нулевая явная формула не применяется к новому знаку. S2 используется как уже данный поставщик пространства и геометрии узлов, не как заново доказанный prime-only результат. Никакой RH, простоты нулей или замены комплексных точек их реальными проекциями нет.

## 1. Ортогональность точно означает range, а не новые нулевые значения

**[FINITE_CELL | PAPER.]** Положим L=log m, b=L/2, omega_j=2 pi j/L. Сохраняем исходный ортонормированный базис

    phi_j(x)=d_j*(-1)^j*cos(omega_j*x)/sqrt(L), |x|<=b,
    d_0=1, d_j=sqrt(2) (j>=1).

Все функции продолжаются нулём. E — вещественная матрица Fourier-value условий ниже T: реальная строка для реального узла, Re/Im строки для комплексного. Повторы и точные зависимости удаляются без изменения ker E; производные в кратных нулях не добавляются. Выбирается полный независимый набор строк. Пусть q=rank E, J=ker E. При q=0 дополнение нулевое и задача на нём пуста; ниже q>0.

Определим реальные Riesz-ядра и Gram-матрицу

    k_alpha=sum_j E_(alpha,j) phi_j,
    G_(alpha,beta)=<k_alpha,k_beta>=(E E^T)_(alpha,beta)>0.

Тогда

    f perpendicular J  <=>  f=sum_alpha c_alpha k_alpha,
    ||f||²=c^T G c,                 E f=G c.                 (1.1)

Это конечномерное равенство (ker E)^perp=ran E^T. Более того,

    ell_alpha=sum_beta (G^-1)_(beta,alpha) k_beta,
    E ell_alpha = unit_coordinate_alpha.                    (1.2)

Следовательно, на дополнении значения в независимых узлах могут быть ЛЮБЫМИ. Они не зануляются и не имеют предписанного знака. (1.2) не отрицает специальной совместной оценки с реальными простыми; она исключает использование value-условий J как будто они действуют на J-perp.

## 2. Формула (6) в оконных ядрах: точный оставшийся объект

**[FINITE_CELL | PAPER.]** Для 0<=s<=L зададим симметричную матрицу

    R_ab(s)=integral_(-b)^(b-s)
      [k_a(x)k_b(x+s)+k_b(x)k_a(x+s)] dx.                   (2.1)

За L она нулевая. Для f из (1.1): Q_f(s)=c^T R(s)c; R(0)=2G, R(L)=0.

Положим

    E0(x)=psi(x)-(x-1),
    a_m(s)=exp(-s/2) E0(exp s),
    M(s)=R(s)/2-R'(s).

Подстановка в точную Abel-формулу S1 даёт

    S_m[f]=c^T D_m c,
    D_m=integral_0^L a_m(s) M(s) ds
       =integral_1^m E0(x)x^(-3/2) M(log x) dx.             (2.2)

Здесь S_m включает все prime powers. Преобразование не оценивает E0 по модулю. Границы оплачены E0(1)=0 и R(L)=0, в том числе при m=p^k. При использовании psi(x)-x вместо E0 необходим дополнительный 2||f||².

Чтобы получить именно простые и квадраты из (5), вычтем

    R_ge3=sum_(p^k<=m,k>=3) (log p)p^(-k/2) R(k log p).

Тогда S_m^(1,2)[f]=c^T(D_m-R_ge3)c. Из S1:

    -C3 G <= R_ge3 <= C3 G,
    C3=(1+sqrt(2))(8+5 log 2)<28.                           (2.3)

Архимедов член также точен:

    H_m=integral_0^infinity j_+(s)[2G-R(s)] ds >=0,
    j_+(s)=exp(-5s/2)/(1-exp(-2s)).                          (2.4)

Искомая постоянная K существует ровно тогда, когда на требуемой неограниченной семье

    D_m-R_ge3-H_m <= K G.                                  (2.5)

То есть нужно ограничить сверху lambda_max(G^-1/2 (D_m-R_ge3-H_m) G^-1/2). Ортогональность уже полностью использована в (1.1); (2.5) — НЕ новая доказанная оценка. Нельзя заменить G единичной матрицей только потому, что исходные phi_j ортонормированы: ядра k_alpha не ортонормированы.

## 3. Точный член, который не исчезает: граница плюс внутреннее спаривание

**[FINITE_CELL | PAPER.]** Введём

    v_alpha=k_alpha(b),       w_alpha(s)=k_alpha(b-s),
    B_ab(s)=integral_(-b)^(b-s)
       [k_a(x)k'_b(x+s)+k_b(x)k'_a(x+s)] dx.

Правило Лейбница, включая движущийся правый край, даёт

    R'(s)=B(s)-w(s)v^T-vw(s)^T,
    M(s)=R(s)/2-B(s)+w(s)v^T+vw(s)^T.                      (3.1)

Следовательно,

    D_m=integral a_m(s)[R(s)/2-B(s)] ds + v z_m^T+z_m v^T,
    z_m=integral_0^L a_m(s)w(s) ds.                         (3.2)

Ни одного неизвестного remainder в (3.2) нет. В физических координатах последний член равен

    Boundary_m[f]
      =2 f(b) integral_0^L exp(-s/2)E0(exp s) f(b-s) ds.     (3.3)

Внутренний производный член равен

    Bulk_m[f]
      =-2 integral_0^L exp(-s/2)E0(exp s)
          integral_(-b)^(b-s) f(x)f'_int(x+s) dx ds.         (3.4)

(3.3) и (3.4) — конкретные члены запрошенной (6) после подстановки (7). Условие f perpendicular J не обращает их в нуль. Их глобальная сумма с R/2 и H_m может иметь полезное сокращение; оно пока не доказано.

Нормированная граничная матрица — rank<=2: положив u=G^-1/2 v, w=G^-1/2 z_m, получаем u w^T+w u^T. Её возможные ненулевые собственные значения равны u^T w +/- ||u||||w||. Поэтому один знак ей не присваивается. Это описание только граничной части, не всей целевой формы.

Причина граничного члена видна и до дифференцирования. Для T_s f(x)=f(x+s), 0<s<L,

    Fourier(1_I T_s f)(z)
      =exp(i z s)[hat f(z)-integral_(-b)^(-b+s) f(y)exp(-i z y)dy]. (3.5)

Даже нулевое значение hat f(z) оставляет collar-интеграл. Нельзя заменить обрезанный сдвиг полным Fourier-множителем; последующая finite-mode проекция также не устраняет этот член автоматически.

## 4. На настоящем дополнении граничный член не формальность

### 4.1. Два точных endpoint-теста

**[FINITE_CELL | PAPER.]** Из чётности и гладкости внутри окна:

    B(0)=0, R'(0+)=-2vv^T,
    M(0+)=G+2vv^T >0,
    M(L-)=2vv^T.                                          (4.1)

Первое равенство есть интеграл производной k_a k_b с одинаковыми значениями на двух концах. При s->L область внутреннего интеграла сжимается до нуля, а w(L)=v.

Таким образом, даже матричный множитель E0 в (2.2) не зануляется после restriction на J-perp. У левого конца E0(exp s)=1-exp s до первого простого: вклад малого начального участка отрицателен, а не опасен. Это контроль НЕВАНИШИНГА, не отрицание возможной верхней оценки.

### 4.2. Явный единичный свидетель в литеральном J-perp

**[FINITE_CELL | PAPER; COFINAL existence uses inherited S2 §3.3.]** У активного узла z с Re z>Omega и sin(zb)!=0 совокупный комплексный след его Re/Im-ядер равен

    t_m(z)=2z sin(zb)/L * sum_(j=0)^m d_j²/(z²-omega_j²).   (4.2)

Это следует из точной Fourier-формулы S3 и phi_j(b)=d_j/sqrt(L). Для настоящего комплексного Riesz-ядра значение сопряжено; утверждение о ненулевом следе то же.

t_m(z) НЕ равен нулю. Если z вещественно и z>Omega, все знаменатели в сумме положительны. Если z невещественно, z² невещественно и

    Im sum_j d_j²/(z²-omega_j²)
      =-Im(z²) sum_j d_j²/|z²-omega_j²|² !=0.               (4.3)

Ненулевой sinc-множитель оставлен явным. S2 §3.3 поставляет хотя бы один такой неавтоматический узел между Omega и T на всех достаточно поздних клетках выбранного расписания; фактически число таких узлов растёт. Используется лишь существование узла, НЕ знак нулевой Weil-суммы. Поэтому v!=0 для полного независимого набора строк E. Если выбранная строка выражается через другие, её ненулевой след всё равно запрещает v=0.

Положим

    tau_m=v^T G^-1 v>0,
    f_*=sum_alpha (G^-1 v)_alpha k_alpha / sqrt(tau_m).      (4.4)

Тогда точно f_* in J-perp, ||f_*||=1, f_*(b)=sqrt(tau_m), и

    Q_f*(L-u)=2 tau_m u+o(u),
    Q_f*(s)/2-Q'_f*(s) -> 2 tau_m  as s->L-.                (4.5)

Это также максимальный квадрат граничного значения на единичной сфере J-perp. Ни роста tau_m, ни независимого положительного lower по m здесь не утверждается.

На последнем целочисленном интервале m-1<x<m лестница psi постоянна, и E0(x)=psi(m-1)+1-x. Она не может тождественно равняться нулю на этом интервале. Множитель в (4.5) положителен возле правого края. Поэтому существует сколь угодно близкий к m малый интервал, на котором подынтегральное выражение (6) для ЭТОГО f_* имеет фиксированный ненулевой знак. Локального зануления от ортогональности нет. В частности, его левый endpoint-limit при x->m равен

    2 tau_m m^(-3/2) [psi(m-1)-(m-1)].                     (4.6)

Если скобка случайно нулевая, предыдущий локальный вывод сохраняется за счёт наклона -1 у E0. Никакой знак или рост самой скобки не предполагается. Входящий атом при n=m умножен на Q(L)=0 и не создаёт добавочной граничной массы.

**Граница вывода:** локально ненулевой вклад может компенсироваться вкладом других s и H_+. (4.4) не предъявляется контрпримером к (5), собственным вектором A_m или свидетельством нарушения RH.

## 5. Удаление boundary не убирает внутренний производный член

**[FINITE_CELL | PAPER.]** Если q>=2, существует ненулевой f in J-perp с f(b)=0: это ядро одного линейного функционала на q-мерном пространстве. Для такого f обе крайние величины нулевые и

    Q'_f(0+)=0,
    Q''_f(0+)=-2||f'_int||²<0.                             (5.1)

Дважды продифференцировать корреляцию и интегрировать f f'' по частям. Граничный член f f' равен нулю; f не может быть ненулевой константой с нулевым endpoint. Поэтому

    Q'_f(s)=-2||f'_int||² s+o(s)

не тождественно нулева, хотя (3.3) полностью исчезла. В этом случае R'-вклад производится именно (3.4). Наличие q>=2 на позднем расписании следует уже из поставленной S2 нижней оценки числа различных активных внешних узлов. Для основной формулы (2.2) предпосылка q>=2 не нужна.

Это показывает, почему формулировка «оплатим только край» недостаточна: остаётся совместное арифметическое спаривание с внутренними производными ядер. Но (5.1) не утверждает, что оно слишком велико для H_+.

## 6. Минимальный незакрытый знак и смысл результата

**[COFINAL_FAMILY | CONDITIONAL: supplier requirement, not proved.]** Единственное требуемое новое неравенство остаётся (2.5), с той же одной константой K. Его точный неоплаченный объект —

    integral a_m(s)[R(s)/2-B(s)] ds + v z_m^T+z_m v^T
       -R_ge3-H_m.                                        (6.1)

Все entries заданы фактической psi и оконными ядрами. Это не сумма по нулям как источник знака. Малая невязка на ker E контролирует A_m на другом блоке и его mixed columns; она не оценивает (6.1) на ran E^T. Оплаченная связь блоков не возвращается в список недоказанных предпосылок.

Два возможных представления для нового знака:

1. Совместная Gram-нормированная матрица (6.1): сохранить все cross-kernel entries и оценивать её сверху относительно G. Сила высокая; конечная проверка умеренной стоимости; кофинальная оценка ещё отсутствует.
2. Точная rank-two граница (3.2) плюс bulk на срезе v^T c=0: проверять их СОВМЕСТНО с H_m, а не по абсолютным нормам E0 и ядер по отдельности. Сила высокая для локализации механизма; стоимость умеренная для матричной диагностики, высокая для аналитического знака.

DISCRIMINATOR: независимый нижний envelope для K G+H_m+R_ge3-D_m при заранее выбранном K, со строгим учётом Gram и всех интегральных ошибок. Нуль-согласованность не является положительностью. Конечный успех не заменяет неограниченный квантор.

DOWNSTREAM_CONSUMER: constant complement floor, then inherited full-floor RH consumer S4.
ACTUAL_CONSUMER_REQUIREMENT: uniform one-sided signed arithmetic bound (2.5).
ORIGINAL_REQUESTED_OBJECT: prove the bound OR identify the exact member where orthogonality gives no cancellation.
ORIGINAL_OBJECT_IS: second alternative fulfilled; first remains unproved and is not refuted.
FAILURE_TYPE: NO_DERIVATION of the cofinal sign; automatic endpoint-annihilation shortcut is false.
EPISTEMIC_STATUS: RESEARCH_DEBT for target; no route-family death.
REOPEN_TRIGGER: independent joint source estimate for (6.1), not small quiet residual again.
NOVELTY_AXIS: exact kernel-pair compression and a literal complementary endpoint witness; no new RH sign.

**Одна CODEX DIRECTIVE: KERNEL_PAIR_REMAINDER_AUDIT.** Проверить (1.1), (2.2), (3.1), (4.2)–(4.5) и (5.1) на закреплённых определениях. Не пересчитывать спектр ради новых похожих чисел. Успех — совпадение прямой prime-minus-continuum матрицы с (2.2) в физической Gram-метрике и сохранение boundary/bulk terms. Это проверка точной локализации остатка; статус (2.5) не повышать без самостоятельного кофинального upper.

## 7. Проверки и доставка

Перед запуском зарегистрированы P1 range/cardinal, P2 оба endpoint-multiplier, P3 обязательный Leibniz boundary, P4 ненулевая bulk-производная при нулевом trace, P5 Abel endpoint, P6 физическая Gram. Все шесть групп точных контролей прошли. Код проверяет конечные тождества; общие утверждения обеспечиваются доказательствами выше. Новый CCM-eigenproblem и новая оценка нулей не вычислялись. Нет независимого аналитического аудита, Lean или Arb.

Записывается только этот новый Markdown в docs/routeB_bus/proshka/ на ветке proshka_inbox_2026-10-31. Старые вердикты, rh_clean, Lean и route-state не изменяются. Commit SHA сообщается после записи и повторного чтения. Git-доставка не является проверкой математического доказательства. Для replay: извлечь следующий Python-блок в checks.py и выполнить `uv run --with sympy checks.py` из каталога с checks.py. Lean gate и профиль аксиом неприменимы: Lean source не создавался.

Что установлено: полностью явный несокращённый член (6), включая его граничный след на реальном дополнении. Что не доказано: постоянный верхний бюджет (5). Что не повторять: превращать range(E^T) в ker(E), менять Gram на I, выбрасывать collar или выводить невозможность глобального upper из локального ненулевого вклада. RH не заявляется.

## Appendix: exact controls

```python
#!/usr/bin/env python3
"""Exact finite algebra controls, NOT a CCM spectral or cofinal certificate.
Run: uv run --with sympy KERNEL_ORTHOGONALITY_CHECKS_2026-11-02.py
Predictions P1--P6 were recorded before this script was executed.
"""
import sympy as s

# P1: nonorthogonal sampling rows; this matrix is a linear-algebra plant,
# not a table of zeta zeros or a substitute for literal CCM.
E = s.Matrix([[1, 2, 0], [0, 1, 1]])
G = E*E.T
Pi = E.T*G.inv()*E
assert Pi*Pi == Pi and Pi.T == Pi
assert E*E.T*G.inv() == s.eye(2)
for j in E.nullspace():
    assert Pi*j == s.zeros(3, 1)
assert E*(E.T*G.inv()) == s.eye(2)
print('PASS P1 range, projector, and cardinal kernel identities')

# P2/P3: exact even window functions 1 and cos(pi*x) on [-1,1].
# They are controls of the differentiation formula, not CCM eigenvectors.
x, u = s.symbols('x u', real=True)
functions = [s.Integer(1), s.cos(s.pi*x)]
v = s.Matrix([1, -1])
Gwin = s.diag(2, 1)
R = s.Matrix([[4-2*u, 2*s.sin(s.pi*u)/s.pi],
              [2*s.sin(s.pi*u)/s.pi,
               (2-u)*s.cos(s.pi*u)-s.sin(s.pi*u)/s.pi]])
B = s.zeros(2)
for a in range(2):
    for b in range(2):
        corr = s.integrate(functions[a]*functions[b].subs(x,x+u)
                           +functions[b]*functions[a].subs(x,x+u), (x,-1,1-u))
        assert s.simplify(corr-R[a,b]) == 0
        integrand = functions[a]*s.diff(functions[b],x).subs(x,x+u) \
                  + functions[b]*s.diff(functions[a],x).subs(x,x+u)
        B[a,b] = s.simplify(s.integrate(integrand,(x,-1,1-u)))
M = R/2-R.diff(u)
assert s.simplify(M.subs(u,0)-(Gwin+2*v*v.T)) == s.zeros(2)
assert s.simplify(M.subs(u,2)-2*v*v.T) == s.zeros(2)
print('PASS P2 both endpoint multiplier matrices')
w = s.Matrix([z.subs(x,1-u) for z in functions])
assert s.simplify(R.diff(u)-(B-w*v.T-v*w.T)) == s.zeros(2)
# Dropping the moving-boundary term must fail for this same test.
assert s.simplify((R.diff(u)-B)[0,0]) == -2
print('PASS P3 exact Leibniz term and planted omitted-boundary failure')

# P4: endpoint zero does not imply a zero bulk derivative.
a = s.Matrix([1,1])
Q = (a.T*R*a)[0]
assert (v.T*a)[0] == 0
assert s.simplify(s.diff(Q,u).subs(u,0)) == 0
assert s.simplify(s.diff(Q,u,2).subs(u,0)) == -2*s.pi**2
assert s.simplify((a.T*B*a)[0]-s.diff(Q,u)) == 0
print('PASS P4 zero trace with nonzero bulk correlation derivative')

# P5: literal von-Mangoldt atoms 2,3,4 at m=4. The endpoint atom 4
# is retained and multiplied by Q(log 4)=0. No zeta formula is used.
y = s.symbols('y', positive=True)
L = s.log(4)
W = 2*(1-s.log(y)/L)/s.sqrt(y)
abel = s.Integer(0)
for lo,hi,psi in [(1,2,0), (2,3,s.log(2)), (3,4,s.log(2)+s.log(3))]:
    primitive = s.integrate((psi-y+1)*(-s.diff(W,y)),y)
    abel += primitive.subs(y,hi)-primitive.subs(y,lo)
source = s.log(2)*W.subs(y,2)+s.log(3)*W.subs(y,3) \
       + s.log(2)*W.subs(y,4)-s.integrate(W,(y,1,4))
assert s.simplify(abel-source) == 0
# E=psi-x instead of E0 loses +Q(0)=2 from the final identity.
assert s.simplify(s.integrate(-s.diff(W,y),(y,1,4))) == 2
print('PASS P5 literal prime-power Abel source and lower endpoint')

# P6: Gram metric is indispensable; all statements stay in physical norm.
c1,c2 = s.symbols('c1 c2', real=True)
c = s.Matrix([c1,c2]); coeff = E.T*c
assert s.expand((coeff.T*coeff)[0]-(c.T*G*c)[0]) == 0
arithmetic = s.Matrix([[2,3,1],[3,-1,4],[1,4,5]])
assert s.expand((coeff.T*arithmetic*coeff)[0]
                -(c.T*(E*arithmetic*E.T)*c)[0]) == 0
endpoint = s.Matrix([1,2])
max_lift = E.T*G.inv()*endpoint
trace_sq = (endpoint.T*G.inv()*endpoint)[0]
assert (max_lift.T*max_lift)[0] == trace_sq
print('PASS P6 arithmetic compression, physical Gram, endpoint lift')
print('ALL 6 GROUPS PASSED; no zeta-zero sign, no CCM eigenproblem, no RH claim')

```
