# STATUS: TRY_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43
```yaml
OPERATIVE_CLASS: TRY_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43
REQUEST_ID: Q43_ORIGINAL_METRIC_SIGNED_PRIMITIVE
DATE: '2026-10-26'
VERDICT_CODE: JOINT_DIFFERENTIATED_PRIMITIVE_RETURN_PAID_NO_NEW_SIGNED_INPUT
REQUEST_COMPLETION: TRANSFER_EXECUTED_MAIN_ARITHMETIC_REQUIREMENT_NOT_PROVED
PROGRESS_CLASS: NO_PROGRESS
PRIMARY_CONSUMER: OPEN
SOURCE: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
REQUEST_BYTES: 129190
REQUEST_LF: 2240
REQUEST_SHA256: 17b8e7a51d140e0807ed8d12959ccad06d7ba06cbb52b08100293e42612272db
BASE_COMMIT: 154e8214042c25cb2b8c860d047611589b866048
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_BODIES: 10
MANIFEST: ALL_BYTE_LF_HASH_FRAMES_MATCH
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
CLOSES: []
OPENS: []
RH: OPEN_NOT_CLAIMED
ZF78: INHERITED_CONDITIONAL_NOT_USED
CF22_PYSR: PARKED_REOPENABLE
NEW_EXTERNAL_ARITHMETIC_INPUT: NONE
REPOSITORY_WRITES: false
HISTORICAL_CODE_EXECUTED: false
NEW_INDEPENDENT_AUDIT: false
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_SPECTRA: NOT_RUN
```

# Q43. Полная дифференцированная первообразная в исходной метрике

## 0. Результат без повышения статуса

**Независимого нового одностороннего арифметического входа я не получил.** Основное требование — новый signed upper с показателем, стремящимся к нулю, либо действительно уменьшающая этот долг подлемма — остаётся невыполненным.

Испытанный ход конкретен: **сначала свернуть настоящую первообразную Q42 с полной мерой Мангольдта, затем вернуть её производную и adjoint в одной исходной форме**. Не оценивать производную, первообразную и обратную замену метрики независимо. Эта свёртка вычисляется через полную конечную факториальную сумму короткой \(\mu\), с balancing-атомом и всеми полами.

Получены:

1. Точное соответствие дифференцированному источнику, включая экспоненциальный вес, все скачки и верхний distributional seam.
2. Полностью оплаченная ошибка конечной факториальной квадратуры на исходном \(P\), с ценой
   \[
   O_\epsilon(m^{3\epsilon/2}).
   \]
   Это вспомогательная аналитико-арифметическая плата; она **не** является верхом полной CCM. По содержанию это возврат короткого сектора, а не новая компенсация главного остатка.
3. Точная совместная сборка показывает, что эта ошибка входит в два канала с противоположными знаками. После её возврата остаётся
   \[
   -\int_1^m[\psi(x)-(x-1)]\,\mathsf W_m'(x)\,dx=C_m^0
   \]
   с коэффициентом **один**. Неизвестный знак не заменён предпосылкой.

Следовательно, ниже **нет нового арифметического показателя, нового pair-margin, no-go для CCM или доказательства RH**. Новая усиленная норма ради ещё одного отрицательного сертификата не строится. Своевременно распознаётся возврат к уже открытому первому signed pairing; затем выбирается более ранний, действительно достаточный receiver на настоящей паре из S8, с явным бюджетом и без утверждения, что его знак уже найден.

---

## 1. Intake и зависимости

Прочитаны весь канонический TXT и десять полных source bodies, в том числе весь исторический оригинал S2 с кодом. Исторические команды и программы не выполнялись.

```text
PROSHKA_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43_2026-10-26.txt
129190 bytes
2240 LF
SHA256 17b8e7a51d140e0807ed8d12959ccad06d7ba06cbb52b08100293e42612272db
```

Общий fingerprint вычислен по приложению; короткая подпись пользователя его не задавала. Все десять внутренних размеров, LF, SHA256, UTF-8 и точные завершающие рамки совпали. Разделительный LF не включался в тело. Полный manifest и программа его повторной проверки приведены ниже. Хеши подтверждают тождество текста, не математическую истинность его утверждений.

Bootstrap прочитан через GitHub connector из `Malaeu/chen_q3`, `rh_clean`, `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`; blob указан в заголовке. Другие живые файлы для выбора задачи не сканировались. Записей в репозиторий, установок и новых внешних арифметических запросов не было.

### 1.1. Что принимается, а что выводится здесь

**[COFINAL_FAMILY | PAPER, inherited]** Из S1–S3 используется ровно следующий принятый вход. Для неограниченной последовательности \(U\ge64\), общей для всех тестов,
\[
 a_U=\sum_{d\le U}\frac{\mu(d)}d,\qquad U|a_U|\le\frac12,
 \quad v=U+1,\quad \tau_U=v a_U,
\]
\[
 u(d)=\mu(d)\mathbf1_{d\le U}-\tau_U\mathbf1_{d=v},
 \qquad \sum_d\frac{u(d)}d=0.
 \tag{1.1}
\]
Положим
\[
 \beta_U=-\sum_d\frac{u(d)\log d}{d},\qquad
 e_U=1-\beta_U,
 \quad S_U=\sum_d|u(d)|.
\]
Принятые Q42-границы:
\[
 |e_U|\le\frac45,\quad \frac15\le\beta_U\le\frac95,
 \qquad \frac{1+S_U}{v}\le\frac45.
 \tag{1.2}
\]
Сам cofinal input и его внешнее происхождение принимаются в проверенной области пакета; здесь они не усиливаются и не сертифицируются заново. Условная оценка \(G(n,U)\) из внешней статьи **не используется**.

При фиксированном \(0<\epsilon<1/32\) выбираются целые
\[
 U^{1/\epsilon}\le m<(U+1)^{1/\epsilon},\qquad
 M=R=U,\quad K=\lceil1/\epsilon\rceil,
 \quad v^K>m.
 \tag{1.3}
\]
Это исходное расписание на общей cofinal последовательности. Ни \(\epsilon\), ни \(m\) не выбираются по вектору.

**[COFINAL_FAMILY | PAPER, inherited]** Из S5–S8 используются исходный синтез и три контакта, полная CCM-идентификация, прежние short/arch-платы и receiver. Из S1–S2:
\[
 A_m=PF_M^*(\mathscr B+\mathscr B^*)F_MP,
 \qquad C_m^0=A_m+H_d,\qquad0\preceq H_d\preceq4P,
 \tag{1.4}
\]
\[
 \mathscr B=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}V_{\log n},
 \qquad
 \mathcal F_{m,U}=C_m^0-e_U^KH_d,
 \quad\kappa_U=1-e_U^K>0.
 \tag{1.5}
\]
Все \(\Lambda(p^j)\) включены. Последнее равенство — принятый полный Q42-return, не новое достижение этого ответа.

Ниже доказываются конечные формулы свёртки, их distributional и adjoint-return и явные вспомогательные бюджеты. Не импортируются новые PNT, Mertens, variance или zero-free оценки. Единственный log-factorial estimate выводится элементарно в §5.

### 1.2. Проверка на повтор до расчёта

S3 контролирует \(\widetilde Y(s)/s\), не \(\widetilde Y(s)\), и уже оплачивает цену его чужой метрики. Мы не оптимизируем этот сертификат ещё раз. S5 предупреждает, что общий metric derivative сам по себе — открытая цель. S4/S10 исключают повтор Selberg/renewal как нового поставщика. S6/S7 уже оплачивают contour/central maps.

Выбранное здесь вычисление ограничено вопросом: **что происходит, если производную вернуть через целую фактическую свёртку \(\Lambda*h_U\), прежде чем разделять её части?** Если это возвращает старый \(C^0\), оно будет признано проверкой соответствия источнику, не новым арифметическим неравенством. Именно это и происходит.

---

## 2. Физическая область и точное восстановление производной

**[ABSTRACT | PAPER]** На \(L^2(0,L)\), \(L=\log m\), используем причинные сдвиги
\[
 (V_s f)(t)=\mathbf1_{s\le t\le L}f(t-s),
 \quad V_sV_t=V_{s+t},\quad V_s=0\ (s\ge L).
\]
Все произведения берутся **до** окончательного сжатия. Для исходного \(c=Pc\), \(f=F_Mc\),
\[
 \|f\|_2=\|c\|_2,\quad \|f'\|_2\le\Omega\|f\|_2,
 \quad\Omega=\frac{2\pi M}{L},
\]
\[
 f(0)=f(L)=0,
 \qquad\int_0^L e^{t/2}f(t)\,dt=
 \int_0^L e^{-t/2}f(t)\,dt=0.
 \tag{2.1}
\]
Нулевое продолжение \(f\) принадлежит \(H^1(\mathbb R)\). Производные и промежуточные свёртки **не** объявляются принадлежащими тому же \(P\).

Пусть \(\mathbf1(n)=1\), \(\delta_1\) — единица Dirichlet-свёртки,
\[
 g_U=\mathbf1*u,\qquad y_U=\delta_1-g_U,
 \quad G_U(x)=\sum_{n\le x}g_U(n)=\sum_{d\le v}u(d)\lfloor x/d\rfloor,
\]
\[
 h_U(t)=1-G_U(e^t)\quad(t\ge0),\qquad h_U(t)=0\quad(t<0).
 \tag{2.2}
\]
Тогда \(h_U\) — **накопленная сумма** коэффициентов \(y_U\), не сама последовательность:
\[
 h_U(t)=\sum_{n\le e^t}y_U(n),\qquad
 h_U(t)=0\ (t<\log v),\qquad
 |h_U(t)|\le1+S_U.
 \tag{2.3}
\]
В частности, первый возможный скачок не потерян:
\[
 y_U(v)=\mu(v)+\tau_U.
 \tag{2.4}
\]
Это следует из \(\sum_{d\mid v}\mu(d)=0\), включая случаи, когда \(v\) не квадратсвободно.

Для \(\sigma>0\) определим
\[
 H_\sigma f(t)=\int_0^t e^{-\sigma s}h_U(s)f(t-s)\,ds,
 \quad
 Y_\sigma=\sum_{n\le m}y_U(n)n^{-\sigma}V_{\log n}.
\]
На причинной полуоси в распределениях
\[
 (\partial_s+\sigma)[e^{-\sigma s}h_U(s)]
 =\sum_{n\ge1}y_U(n)n^{-\sigma}\delta_{\log n}.
 \tag{2.5}
\]
Здесь **оба** члена \(-\sigma e^{-\sigma s}h_U\) и \(+\sigma e^{-\sigma s}h_U\) необходимы; первый появляется при дифференцировании веса. После их сокращения остаются все атомы, а не гладкий нулевой остаток.

### 2.1. Верхний seam

Если сперва обрезать ядро в \(L\), правильная формула имеет вид
\[
 \begin{aligned}
 (\partial_s+\sigma)\bigl[\mathbf1_{[0,L]}(s)e^{-\sigma s}h_U(s)\bigr]
 ={}&\sum_{n\le m}y_U(n)n^{-\sigma}\delta_{\log n}\\
 &-m^{-\sigma}h_U(L)\delta_L.
 \end{aligned}
 \tag{2.6}
\]
В правой части \(h_U(L)\) — **правый след**, включающий \(n=m\). Сумма атома \(y_U(m)\delta_L\) и последнего члена равна отрицательному левому следу, как и требуется производной обрезанного ядра. Не подменяем \(h_U(L)\) на \(h_U(L-)\), одновременно оставляя верхний атом.

На физическом \((0,L)\) оба сдвига в \(L\) действуют нулём. Это точный causal return, не оценка малого хвоста. При последующей sinc-квадратуре нельзя отдельно удалить сглаженный верхний атом; в этом расчёте такая квадратура вообще не используется.

Если обрезается уже **результат** \(H_\sigma f\), возникает отдельно \(-H_\sigma f(L)\delta_L\). Его спаривание с исходным \(f\) нулевое из \(f(L)=0\); **не** из \(H_\sigma f(L)=0\). Промежуточная свёртка может иметь ненулевой верхний след.

На исходных входах:
\[
 Y_\sigma f=H_\sigma(f'+\sigma f),\qquad
 Y_\sigma^* f=H_\sigma^*(-f'+\sigma f).
 \tag{2.7}
\]
Первое равенство использует \(f(0)=0\), второе — \(f(L)=0\); adjoint содержит обратную временную ориентацию. Это равенства операторных действий на данной области, не утверждение, что \(H_\sigma\) сохраняет полосу или контакты.

Для контроля масштаба, уже на исходном весе,
\[
 \|H_{1/2}\|\le\frac{2(1+S_U)}{\sqrt v},
 \qquad
 \|Y_{1/2}f\|\le
 \frac{2(1+S_U)}{\sqrt v}(\Omega+\tfrac12)\|f\|.
 \tag{2.8}
\]
Цена одного такого действия имеет vanishing-\(\epsilon\) степень. Но (2.8) **не** является контрактом для полной \(\mathcal F\): дальнейшие множители содержат полную арифметику, а промежуточные векторы вышли из исходной области. В частности, из (2.8) не следует малая норма \((I-Y_{1/2})^{-1}\) или благоприятный знак логарифмической производной.

---

## 3. Выбранный совместный арифметический расчёт

Здесь возвращается **весь** источник, а не только \(Y\). Введём короткий logarithmic convolution
\[
 \ell_U=u*\log,
 \qquad
 J_U(x)=\sum_{n\le x}\ell_U(n)
 =\sum_{d\le v}u(d)\log\bigl(\lfloor x/d\rfloor!\bigr),
 \tag{3.1}
\]
где \(\log0!=\log1!=0\). Ни один внутренний \(k\) не удалён.

**[ABSTRACT | PAPER]** Полная свёртка Мангольдта с первообразной равна
\[
 \boxed{
 \Pi_U(x):=\sum_{n\le x}\Lambda(n)h_U(\log(x/n))
 =\psi(x)-J_U(x).
 }
 \tag{3.2}
\]
Доказательство конечное, для каждого вещественного \(x\ge1\):
\[
 \begin{aligned}
 \sum_{n\le x}\Lambda(n)G_U(x/n)
 &=\sum_{d\le v}u(d)\sum_{nk\le x/d}\Lambda(n)\\
 &=\sum_{d\le v}u(d)\sum_{j\le x/d}\sum_{n\mid j}\Lambda(n)\\
 &=\sum_{d\le v}u(d)\sum_{j\le x/d}\log j=J_U(x).
 \end{aligned}
\]
Использовано **настоящее** \(\Lambda*\mathbf1=\log\), включая каждый \(p^a\). Все переменные упорядочены, пределы — буквальные полы. Отсюда
\[
 \ell_U+\Lambda*y_U=\Lambda.
 \tag{3.3}
\]
Это классическая коэффициентная алгебра, **не новая оценка**. Она нужна, чтобы проверяемая манипуляция действительно относилась к заданной полной форме.

Для \(1\le x<v\), \(J_U(x)=\psi(x)\) и \(\Pi_U(x)=0\). Первый скачок \(h_U\) в \(\log v\) сам по себе не даёт скачка \(\Pi_U\) там: \(\Lambda(1)=0\). Связанные скачки \(\Pi_U\) возникают с полными коэффициентами \((\Lambda*y_U)(n)\), в частности начиная не раньше \(2v\).

### 3.1. Почему один шаг не отбрасывает остальные биномиальные каналы

Здесь \(\Pi_U\) — не приближённая замена всего Q42-ряда. Полная конечная алгебра сохраняет
\[
 \mathscr B=\mathscr L_U\sum_{j=0}^{K-1}Y_{1/2}^{\,j}
             +\mathscr B Y_{1/2}^{\,K},
 \qquad Y_{1/2}^{\,K}=0\quad(v^K>m).
\]
Поэтому
\[
 \mathscr B Y_{1/2}
 =\mathscr L_U\sum_{j=1}^{K-1}Y_{1/2}^{\,j}.
\]
В последующем \(\mathscr B H_{1/2}\)-переносе находится **вся** эта правая часть, а не только один её канал. Все степени, упорядоченные произведения и mixed balancing terms остаются совместными. Нулевая causal-поддержка хвоста здесь применяется только к конечному операторному равенству; отдельные полюсные или контурные части бесконечного хвоста не удаляются. Это та же поддержка, что в S1–S2, не новый выигрыш.

### 3.2. Источниковая карта на исходном весе

Пусть
\[
 \mathscr L_U=\sum_{n\le m}\ell_U(n)n^{-1/2}V_{\log n},
 \qquad \mathscr Q_U=\mathscr B H_{1/2}.
\]
До сжатия \(\mathscr Q_U\) — причинная свёртка с ядром
\[
 k_U(s)=e^{-s/2}\Pi_U(e^s).
 \tag{3.4}
\]
Множитель \(n^{-1/2}\) из \(\mathscr B\) и вес внутри \(H_{1/2}\) соединяются точно в \(e^{-s/2}\); никакой tilt к \(\sigma=1\) не нужен.

Из (2.5), (3.3) на исходном входе:
\[
 \boxed{
 \mathscr Bf=\mathscr L_Uf+
 \mathscr Q_U(f'+\tfrac12f).
 }
 \tag{3.5}
\]
Для ядра (3.4) аналог (2.6) содержит верхнюю поправку
\(-m^{-1/2}\Pi_U(m)\delta_L\). Она возвращается точно тем же способом. Нельзя считать отдельно малой \(\Pi_U(m)\): в исходной физической форме множитель на этом seam равен нулю.

Определим
\[
 \mathcal S_U=PF_M^*(\mathscr L_U+\mathscr L_U^*)F_MP,
\]
и полный Hermitian-остаток \(\mathcal V_U=A_m-\mathcal S_U\). Тогда для любого комплексного \(c=Pc\)
\[
 \boxed{
 c^*A_mc=c^*\mathcal S_Uc+
 2\Re\langle f,\mathscr Q_U(f'+\tfrac12f)\rangle.
 }
 \tag{3.6}
\]
Ни \(|\mathscr Q_U|\), ни \(|f|\), ни независимые векторы для двух сторон времени не вводятся. Это полная исходная self/cross-форма; поляризация сохраняет все смешанные матричные элементы.

---

## 4. Возврат signed primitive до первой нормы

Обозначим
\[
 q_f(s)=2\Re\int_s^L\overline{f(t)}f(t-s)\,dt,
 \quad
 \mathsf W_m(x)=x^{-1/2}P Q_M(\log x)P,
 \quad g_c(x)=c^*\mathsf W_m(x)c=x^{-1/2}q_f(\log x).
\]
Для исходных входов
\[
 |q_f(s)|\le2\|f\|^2,\quad |q_f'(s)|\le2\Omega\|f\|^2,
 \quad q_f(L)=q_f'(L)=0.
 \tag{4.1}
\]
Производная overlap не получает нижнего boundary term из-за \(f(0)=0\). Следовательно,
\[
 \|\mathsf W_m'(x)\|\le(1+2\Omega)x^{-3/2},
 \quad\mathsf W_m(m)=0.
 \tag{4.2}
\]

Подставляя (3.4) в **целое** вещественное спаривание (3.6), получаем
\[
 \begin{aligned}
 c^*\mathcal V_Uc
 &=\int_0^L e^{-s/2}\Pi_U(e^s)
       [\tfrac12q_f(s)-q_f'(s)]\,ds\\
 &=-\int_1^m\Pi_U(x)g_c'(x)\,dx.
 \end{aligned}
 \tag{4.3}
\]
Это первое место, где совместный перенос можно проверить без символического обозначения неопределённой энергии. Скачки исходной \(\Pi_U\) полностью соответствуют исходной мере \(\Lambda*y_U\). Значения на отдельных швах не меняют Lebesgue-интеграл в последней строке; верхний Stieltjes-атом до перехода к нему уже возвращён.

Пусть
\[
 E(x)=\psi(x)-(x-1),\qquad
 R_U(x)=J_U(x)-\beta_U(x-1).
\]
Точная, ещё не оцененная связь:
\[
 \boxed{\Pi_U(x)=E(x)+e_U(x-1)-R_U(x).}
 \tag{4.4}
\]
Введём полную матричную ошибку короткой квадратуры
\[
 \mathcal E_U=-\int_1^m R_U(x)\mathsf W_m'(x)\,dx.
 \tag{4.5}
\]
Нижние следы \(E(1)=R_U(1)=\Pi_U(1)=0\), верхний тест \(\mathsf W_m(m)=0\). Поэтому без потери знака
\[
 \boxed{
 \mathcal S_U=-\beta_UH_d+\mathcal E_U,
 \qquad
 \mathcal V_U=C_m^0-e_UH_d-\mathcal E_U.
 }
 \tag{4.6}
\]
Все части здесь на одном и том же \(P\).

**Именно здесь проверяемый ход возвращается к старому долгу.** Ошибка \(\mathcal E_U\) входит с противоположными знаками, и её полное совместное возвращение даёт
\[
 \mathcal S_U+\mathcal V_U=C_m^0-H_d=A_m,
\]
\[
 \boxed{
 \mathcal F_{m,U}
 =\mathcal S_U+\mathcal V_U+\kappa_UH_d
 =C_m^0-e_U^KH_d.
 }
 \tag{4.7}
\]
Нет нового коэффициента меньше единицы перед \(E\), перед \(C^0\) или перед всей \(\mathcal F\). (4.7) согласуется с принятым Q42, а не заменяет его новым результатом.

В частности, малость \(H_1\), локального germ \(\widetilde Y\) или даже хорошая отдельная оценка \(\mathcal E_U\) **не** даёт знака \(C^0\). Продолжать формальные energy-преобразования, не добавив новой арифметической информации, здесь не оправдано.

---

## 5. Полная количественная цена факториальной ошибки

Эта секция нужна для полного возврата, а не для объявления главного арифметического выигрыша.

### 5.1. Элементарная оценка, включая дробные края

**[ABSTRACT | PAPER]** Для каждого вещественного \(y\ge1\)
\[
 F(y):=\log(\lfloor y\rfloor!)-(y\log y-y+1)
 =-\{y\}\log y+\int_1^y\frac{\{t\}}t\,dt.
 \tag{5.1}
\]
Это конечная Stieltjes-формула для \(\lfloor y\rfloor\). Она верна в целых точках с правым следом. Оба слагаемых справа сохранены до оценки:
\[
 \boxed{|F(y)|\le\log y.}
 \tag{5.2}
\]
Здесь не нужен внешний Stirling theorem и не используется знак произвольной ошибки квадратуры.

Для \(x\ge v\) все \(x/d\ge1\). Благодаря **точному** балансированию (1.1),
\[
 J_U(x)=\beta_Ux+A_U+\sum_{d\le v}u(d)F(x/d),
 \quad A_U=\sum_{d\le v}u(d).
 \tag{5.3}
\]
Член \(x\log x\sum u(d)/d\) и член \(-x\sum u(d)/d\) сократились совместно. Нельзя сохранять \(\mu\)-префикс, но удалить balancing-атом из этого сокращения.

Отсюда
\[
 \boxed{|R_U(x)|\le S_U(1+\log x)+|\beta_U|\quad(x\ge v).}
 \tag{5.4}
\]
На \(1\le x<v\) используем \(J_U(x)=\psi(x)\) и только элементарное \(\Lambda(n)\le\log n\):
\[
 |R_U(x)|\le x(\log x+|\beta_U|).
 \tag{5.5}
\]
Ни оценки ошибки PNT, ни усиления \(G(n,U)\) здесь нет.

### 5.2. Матрица на полном исходном \(P\)

**[COFINAL_FAMILY | PAPER, conditional only on inherited cofinal selection]** Из (4.2), (5.4)–(5.5):
\[
 \boxed{\|\mathcal E_U\|\le\mathfrak e_U,}
\]
\[
 \begin{aligned}
 \mathfrak e_U=(1+2\Omega)\bigg[&2\sqrt v\log v
 +2|\beta_U|(\sqrt v-1)\\
 &+\frac2{\sqrt v}\{S_U(\log v+3)+|\beta_U|\}\bigg].
 \end{aligned}
 \tag{5.6}
\]
Использованы
\[
 \int_v^\infty x^{-3/2}dx=2v^{-1/2},\qquad
 \int_v^\infty(1+\log x)x^{-3/2}dx
 =2v^{-1/2}(\log v+3).
\]
Интеграл продлён до бесконечности **только в неотрицательном верхе ошибки**; ни одного нового арифметического атома после \(m\) в источнике не появилось. Split в \(v\) сделан после полного Stieltjes-return; его скачок не потерян.

При исходном расписании, с фиксированным \(\epsilon\),
\[
 \mathfrak e_U\ll(1+\Omega)\sqrt v(1+\log v)
 =O_\epsilon(m^{3\epsilon/2}).
 \tag{5.7}
\]
Последнее верно eventually: \(\Omega\asymp m^\epsilon/L\), \(\log v=O_\epsilon(L)\), а остаток \(m^{\epsilon/2}L\) поглощается \(C_\epsilon m^{3\epsilon/2}\). Никакой равномерности onset по \(\epsilon\downarrow0\) не утверждается.

Это верх на **всю** матрицу \(\mathcal E_U\), не на диагонали и не на отдельные коэффициенты мод. Но в (4.6) эта матрица присутствует дважды с противоположным знаком. При совместном возвращении её фактическая добавочная плата — ноль. Оценка (5.6) полезна только для явно объявленного разделения короткого и длинного секторов. Она не улучшает общий показатель и не выдаётся за новую source-specific signed лемму.

### 5.3. Полная balancing-поправка, а не один голый сдвиг

Положим
\[
 B_d=\sum_{dk\le m}\log k\,\mathsf W_m(dk),\qquad
 T_{\le R}=\sum_{d\le R}\mu(d)B_d,
 \quad T_{>R}=\sum_{d>R}\mu(d)B_d.
\]
Тогда буквально
\[
 \boxed{\mathcal S_U=T_{\le R}-\tau_UB_v,
 \qquad\mathcal V_U=T_{>R}+\tau_UB_v.}
 \tag{5.8}
\]
В \(B_v\) сохранена полная внутренняя сумма. Малость \(\tau_Uv^{-1/2}V_{\log v}\) **без этой суммы** не является её ценой.

Для ясного самостоятельного контроля можно получить
\[
 \boxed{\|B_d\|\le\frac{16+8\Omega}{\sqrt d}\quad(1\le d\le m).}
 \tag{5.9}
\]
Это возврат того же типа, что уже оплаченные full-log blocks, не новый механизм сокращения \(\Lambda\).

Доказательство. Пишем \(a=\log d\). Непрерывная часть равна
\[
 C_d=\frac1d\int_a^L(s-a)e^{s/2}P Q_M(s)P\,ds.
\]
Два контакта дают
\[
 \int_0^L e^{s/2}P Q_M(s)P\,ds=-H_d,
\]
а тождество для \(r=t-u\)
\[
 |r|e^{|r|/2}=r(e^{r/2}-e^{-r/2})+|r|e^{-|r|/2}
\]
удаляет только rank-части с одним чистым экспоненциальным контактом. Поэтому норма полного логарифмического continuous moment не превосходит
\(\int_{\mathbb R}|r|e^{-|r|/2}dr=8\). Отделяя \([0,a]\) лишь после этих полных равенств,
\[
 \|C_d\|\le\frac{8+4a+2\int_0^a(a-s)e^{s/2}ds}{d}
 =\frac8{\sqrt d}.
\]
Здесь не предполагалось положительности decaying log kernel.

Для \(F_d(t)=\log t\,\mathsf W_m(dt)\), \(1\le t\le m/d\), оба endpoint-значения равны нулю. Euler-return с полным дробным краем и (4.2) даёт
\[
 \Big\|\sum_{k\le m/d}F_d(k)-\int_1^{m/d}F_d(t)dt\Big\|
 \le\int_1^{m/d}\|F_d'(t)\|dt
 \le\frac{8+8\Omega}{\sqrt d}.
\]
Использованы \(\int_1^\infty t^{-3/2}dt=2\),
\(\int_1^\infty\log t\,t^{-3/2}dt=4\). Это доказывает (5.9), включая нецелый \(m/d\) и случай \(d=m\), когда весь блок нулевой.

Таким образом, цена отдельного восстановления balancing-блока не больше
\[
 \boxed{\mathfrak b_{\rm bal}=|\tau_U|\|B_v\|
 \le(16+8\Omega)\frac{\sqrt v}{2U}.}
 \tag{5.10}
\]
Она имеет порядок \(O_\epsilon(m^{-\epsilon/2}+m^{\epsilon/2}/L)\). В полной сборке (5.8) она сокращается точно и не добавляется ещё раз.

---

## 6. Первая неоплаченная строка

После полного совместного вычисления остаётся
\[
 \boxed{
 \mathcal C_E:=-\int_1^m E(x)\mathsf W_m'(x)\,dx
 =C_m^0.
 }
 \tag{6.1}
\]
Не доказан независимый upper
\[
 \mathcal C_E\preceq D_\epsilon m^{\eta(\epsilon)}P,
 \qquad\eta(\epsilon)\to0,
 \tag{6.2 — UNPROVED}
\]
или достаточная более узкая версия на настоящей source-pair семье.

Искомая связь actual coefficients и их фазированного теста отсутствует именно в (6.2). Малость исходной \(h_U\) в чужом весе не оценивает \(\Pi_U=\Lambda*h_U\) в нужном знаковом спаривании. Балансирование уничтожает \(x\log x\) в \(J_U\), но не уничтожает \(E\) в (4.4). Неравенство для всего \(\mathcal V_U\) также не появляется из одного \(\|\mathcal E_U\|\).

**Не допущена подстановка (6.2) в качестве нового «арифметического свойства».** Не утверждается знак \(\Pi_U\), положительность производной корреляции, метрическая монотонность или сохранение \(P\) свёрткой.

Точное соответствие Q04 теперь прозрачно: после восстановления всей производной и обратного источника мы снова имеем первую форму реальной \(\Lambda\), эквивалентную прежнему \(2\Re\langle f,M'_{1/2}Z_{1/2}f\rangle\). Это распознано как тот же долг, **не** засчитано как новая попытка доказать его с помощью нового названия.

### 6.1. Полностью законные цены без желаемой предпосылки

Принятый прямой верх:
\[
 A_m\preceq s_{\rm keep}P,
 \qquad s_{\rm keep}\le6\sqrt m+6m^{1/4}.
 \tag{6.3}
\]
Он сразу даёт, не прибегая к новым нормам,
\[
 \mathcal F_{m,U}\preceq
 [s_{\rm keep}+4\kappa_U]P,
\]
\[
 \mathcal V_U\preceq
 [s_{\rm keep}+4\beta_U+\mathfrak e_U]P.
 \tag{6.4}
\]
Эти формулы — перенесённый fallback. Их \(m\)-степень остаётся \(1/2\). Не строится нижняя цена ещё одного сертификата и не делается вывод об actual spectrum из величины allowance.

Если бы независимо был найден \(\mathcal V_U\preceq sP\), то точный возврат был бы
\[
 T_{>R}\preceq(s+\mathfrak b_{\rm bal})P,
 \qquad
 PK_mP\succeq-[s+\mathfrak e_U+50L+8]P,
 \tag{6.5 — ONLY A CONDITIONAL MAP}
\]
поскольку \(\beta_U>0\) и \(\mathcal S_U=-\beta_UH_d+\mathcal E_U\). В первой строке не добавляется ещё и полный \(b_{\rm div}\): исходный \(T_{>R}\) уже возвращён напрямую через (5.8). **Само \(s\) здесь не поставлено.**

Поэтому фактический окончательный бюджет сохраняется в своей более сильной исходной форме:
\[
 \boxed{
 T_{>R}\preceq(s_{\rm keep}+b_{\rm div})P,
 \qquad
 PK_mP\succeq-[s_{\rm keep}+50L+8]P,
 }
 \tag{6.6}
\]
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\]
Short fee начислена один раз только для перехода \(A\to T_{>R}\). В direct \(K\) нет повторных \(H_d\), \(\mathcal E_U\), prime-power или balancing fees. Q32-return \(O_\epsilon(m^{2\epsilon})\) нужен только при явном переходе через \(N_\star\), а не поверх (6.6). Условные \(3/8\) по ZF78 остаются условными; в этом вычислении ZF78 не использовалась.

### 6.2. Ledger возвратов

| Часть | Цена / точное действие | Scope и verifier |
|---|---|---|
| \(\mu\)-префикс и balancing-атом | Возвращены в (1.1), (3.1), (5.8); не заменяют actual \(\Lambda\) | ABSTRACT / PAPER |
| Все \(\Lambda(p^j)\) и гиперболические края | В (3.2)–(3.3) точно, без удаления | ABSTRACT / PAPER |
| Производная веса и все скачки | (2.5), включая \(y(v)=\mu(v)+\tau\) | ABSTRACT / PAPER |
| Верхние kernel/output seams | (2.6) и исходный \(f(L)=0\); промежуточные traces не занулены | ABSTRACT / PAPER |
| Изменение вектора, нормы, \(P\) | 0: в основном расчёте вектор не меняется | ABSTRACT / PAPER |
| Факториальная ошибка \(\mathcal E_U\) | (5.6), \(O_\epsilon(m^{3\epsilon/2})\) при отдельном использовании | COFINAL_FAMILY / PAPER |
| Та же ошибка в полной форме | \(+\mathcal E_U-\mathcal E_U=0\) точно | ABSTRACT / PAPER |
| Полный balancing-блок \(\tau B_v\) | (5.10) отдельно; 0 в совместной сборке | COFINAL_FAMILY / PAPER |
| Полный signed верх \(C^0\) нужной степени | **Не доказан** | COFINAL_FAMILY / CONDITIONAL |
| Фактический \(T_{>R}\), \(K\) | Только (6.6), inherited | COFINAL_FAMILY / PAPER |

---

## 7. Обоснованный ранний откат: не требовать all-\(P\) там, где достаточно настоящей пары

Откат не состоит в ещё одной записи \(C^0\) под новым именем. **Останавливается выбранная цепочка contractive primitive → differential/metric return.** Она не поставила требуемой арифметической информации. Возвращаемся к документированной развилке S8 **до усиления достаточной задачи до всех векторов**.

S8 уже даёт условный настоящему гипотетическому нулю
\(w=\delta+i\gamma\), \(0<\delta<1/2\), кратности \(r\), целый источникосогласованный witness \(z_{m,w}\in\operatorname{ran}P\), с ограниченной нормой, всеми контактами и full \(K_m\)-return. Это не новая конструкция Q43 и не утверждение существования внепрямого нуля.

**[COFINAL_FAMILY | CONDITIONAL, inherited actual-zero witness]** В ненормированной версии принятого source-pair receiver положим
\[
 X_w(m)=m^\delta L^{-2\delta},\qquad\|z_{m,w}\|^2\le D_w,
\]
\[
 z_{m,w}^*K_mz_{m,w}=-2rX_w(m)+\varepsilon_K(m),
 \qquad |\varepsilon_K(m)|\le\rho_K(m)=o(1).
 \tag{7.1}
\]
Полное значение пары и достаточность её возвращения наследуются из S8; здесь не реконструируются отсутствующие в данном пакете исходные профили и не назначаются им вымышленные параметры.

Для фиксированного \(q>1/\epsilon+2\) явная принятая цена имеет вид
\[
 \begin{aligned}
 \rho_K(m)\le C_{w,q}\big[&m e^{-c_wL^2}
 +m\Omega^{1/2-q}+\sqrt m\Omega^{3/2-q}
 +\sqrt m\Omega^{1-q}\\
 &+E_q^2+\sqrt m L^{q+1/2}M^{1/2-q}\big],
 \end{aligned}
\]
\[
 E_q=C_{w,q}[\sqrt m\Omega^{1/2-q}
                 +\Omega^{3/2-q}+\Omega^{1-q}].
 \tag{7.2}
\]
Сохранены cutoff, обе zero-extension полосы, все три контактных поправки, линейные смешанные и квадратичные ошибки. Промежуточные функции не считаются точно лежащими в \(P\). Эта цена действовала на всех поздних ячейках, значит и на cofinal подпоследовательности (1.3).

**Слабейший используемый здесь достаточный signed вход** можно потребовать только на этой семье:
\[
 \boxed{
 z_{m,w}^*C_m^0z_{m,w}
 \le(2r-\vartheta_w)X_w(m)+e_w(m),
 \qquad\vartheta_w>0,\quad e_w=o(X_w).
 }
 \tag{7.3 — UNPROVED}
\]
Последовательность исходных ячеек при этом должна быть неограниченной; выбор (1.3) уже общий для всех \(P\)-векторов. Мы не объявляем (7.3) all-\(P\) оценкой или новой найденной леммой.

Полная проверка достаточности без бесплатных расходов:
\[
 A_m=C_m^0-H_d\preceq C_m^0,
\]
\[
 z^*K_mz\ge-(2r-\vartheta_w)X_w-e_w-D_w(50L+8).
 \tag{7.4}
\]
Совместно с (7.1) это дало бы
\[
 \vartheta_wX_w\le e_w+D_w(50L+8)+\rho_K,
\]
что противоречит \(L/X_w\to0\). Это только проверка более слабого consumer interface; (7.3) **не** получено из (7.1).

На этой же семье формула (6.1) сохраняет полный комплексный Fourier-квадрат и все self/cross terms:
\[
 z_{m,w}^*C_m^0z_{m,w}
 =-\int_1^m E(x)\,\frac d{dx}
 \left[z_{m,w}^*\mathsf W_m(x)z_{m,w}\right]dx.
 \tag{7.5}
\]
Замена \(z\) на \(|z|\), произвольный bump, отдельные packet-пробы или среднее независимых фаз здесь не разрешена. **Новой оценки правой части (7.5) в Q43 нет.** Старые PNT/Poisson и adverse-pole расчёты не повторялись как положительный вход.

Полностью законный fallback на этой семье:
\[
 z^*C_m^0z\le D_w(s_{\rm keep}+4).
 \tag{7.6}
\]
При \(0<\delta<1/2\) отношение данного allowance к \(X_w\) имеет ведущую степень \(1/2-\delta\), поэтому (7.6) не поставляет зазор (7.3). Это вывод о достаточности выписанной оценки, **не** нижняя граница actual формы.

Практическое изменение выбора: после этого отката не требуется сначала доказать самостоятельную норму \(H^{-1}\), знак каждого primitive-канала или верх на всех \(P\)-векторах. Достаточен один независимый signed факт на принятой целой source-pair семье. Утверждение, что этот более узкий факт легче или уже доказан, не делается.

---

## 8. Статусы, сильнейшее возражение и границы отказа

**Сильнейшее возражение:** «Факториальная свёртка и её малая ошибка не уменьшили главный долг; ты снова вернулся к \(C^0\)». Это верно. Поэтому главный результат помечен `NO_PROGRESS`, а не `PROOF_PROGRESS`. Сокращение полюсов Q42 и приведённые здесь source-identification формулы не используются как доказательство новой степени.

**Первая неоплаченная арифметическая строка:** (6.2), либо более слабая (7.3). Ни одно из этих утверждений не было включено в предпосылки якобы завершённого доказательства.

**Что не утверждается:** нижняя норма настоящей резольвенты, нижняя спектральная оценка CCM из цены Young, невозможность source cancellation, невозможность применения всех primitive/energy методов, отсутствие литературы, существование конкретного внепрямого нуля. Новых внешних оценок здесь не было, а семантическая полка остаётся в её заявленном `INCOMPLETE`-статусе.

Две точные дальнейшие записи — не два новых поручения и не обещания:

| Представление | Полная цена карты | Отличающий критерий / эффект | Стоимость проверки |
|---|---|---|---|
| Выбранный rollback: actual source-pair S8 | (7.2), arch один раз; остальная форма точна | Новый bound должен дать фиксированный \(\vartheta_w>0\) после всех расходов | Один полный фазированный scalar pairing; арифметический input пока отсутствует |
| Полное \(N_\star\) из S7 на исходном \(P\) | \(O_\epsilon(m^{2\epsilon})\) один раз | Верх \(m^{\theta(\epsilon)}\), \(\theta\to0\), **до** разделения source/test | Uniform polarized matrix estimate; аналитическая карта готова, знак открыт |

**DISCRIMINATOR:** полный finite kernel action / формула (3.6), а не значение одного germ. Кандидат обязан одновременно вернуть скачок \(y(v)\), smooth weight derivative, верхний seam, оба знака \(\mathcal E_U\) и все настоящие \(\Lambda(p^j)\). Для pair-пути численный или символический показатель сравнивается с \(X_w\), не с нормой одной вспомогательной свёртки.

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_T_GT_R_UPPER_OR_ACCEPTED_SOURCE_PAIR_RECEIVER
ACTUAL_CONSUMER_REQUIREMENT: >-
  A one-sided original-P upper with eta(epsilon)->0 and full returns,
  or an independently proved strict coefficient margin on the accepted
  whole actual-source pair. Common cofinal production cells are permitted.
ORIGINAL_REQUESTED_OBJECT: JOINT_DIFFERENTIATED_BALANCED_PRIMITIVE_TRANSFER
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_INTERFACES: 'Equation (7.3) implies the unchanged source-pair contradiction via (7.1)-(7.4).'
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: >-
  Explicit joint source correspondence and its factorial/endpoint return;
  no new independently favorable signed arithmetic inequality found.
REOPEN_TRIGGER: >-
  A proved actual-coefficient inequality controlling the full first signed
  pairing, not only a primitive norm, short moment, local residue, or a
  hypothesis equivalent to that pairing.
KILL_SCOPE: NONE
MATHEMATICALLY_DEAD: NONE
CLOSES: []
OPENS: []
```

**Один ограниченный CODEX DIRECTIVE для проверки, без отправки нового запроса:** проверить (2.5)–(2.7), свёртку (3.2), оба знака (4.6), границы (5.6)/(5.9) и недвойную цену (6.5)/(6.6). В gate-результате оставить (6.2) и (7.3) открытыми, если не предъявлен отдельный новый арифметический аргумент. Никакого продвижения состояния Route B или main export из этого документа не следует.

```yaml
iteration: Q43
status: NO_PROGRESS
failed_strategy: PRIMITIVE_CONTRACTION_WITHOUT_NEW_SIGNED_SOURCE_CONTROL
cognitive_operator_used: REPRESENTATION_SHIFT
new_gap_name: NONE_ORIGINAL_SIGNED_SOURCE_RETAINED
invariant_learned: >-
  The full Mangoldt convolution of the balanced primitive is psi minus the
  complete short factorial source. Its two quadrature errors cancel, while
  the original centered discrepancy keeps coefficient one.
forbidden_future_move: >-
  Treat a small factorial correction or the Y/s contraction as an upper
  on the complete differentiated source; discard an intermediate endpoint
  trace or use a derivative input as if it still belonged to P.
next_decisive_test: BOUNDED_READ_ONLY_AUDIT_OF_JOINT_DISTRIBUTIONAL_AND_FACTORIAL_RETURN
route_score_primary: 2
RH_CLAIM: NOT_MADE
```

---

## 9. Воспроизводимые проверки и их точная область

Пререгистрация новых executable controls записана **после аналитического вывода, но до запуска проверяющего кода**; она не выдаётся за предварительную регистрацию уже выполненной бумажной работы. Все прогнозы в ней относятся к проверке source map и её пределов, а не к обнаружению благоприятного арифметического знака.

Проверяющий использует стандартную библиотеку Python, `Fraction` и формальные рациональные координаты \(1,\log2,\log3,\ldots\). Проверены:

- полные actual-\(\mu\) коэффициенты \(\ell_U+\Lambda*y_U=\Lambda\) в трёх конфигурациях;
- \(\Pi_U=\psi-J_U\) на целых и нецелых границах, включая \(v\) и \(m\);
- конечная Stieltjes-сборка с **ненулевым** terminal-test и с нулевым terminal-test;
- actual \(U=67\), удовлетворяющий точному cofinal-предикату, и пять рационально ограждённых проверок (5.4);
- шесть намеренных дефектов: удаление balancing-атома, неверный знак факториальной части, удаление proper powers, потеря weight derivative, удаление terminal term и замена complex adjoint транспонированием.

Итог программы: 330 коэффициентных индексов, 21 floor-проверка, шесть endpoint-спариваний и пять interval-проверок. Это не число новых математических результатов. Малые \((m,U)\) выбраны для алгебры, **не** являются production-ячейками \(U=\lfloor m^\epsilon\rfloor\), \(\epsilon<1/32\). Условие для \(U=67\) не заменяет доказанный cofinal input. Generic complex-product контроль также не является actual CCM-вектором.

Рациональные логарифмические интервалы получены из atanh-ряда с явным хвостом. Это не float-знак и не Arb. Общие кванторы в §§2–7 основаны на бумажных выводах и отмеченных inherited inputs, не на панели.

| Прогноз | Судьба |
|---|---|
| P1: полная свёртка возвращает \(\psi-J_U\) | Подтверждён конечной алгеброй и exact controls |
| P2: производная требует weight term, скачков и upper seam | Подтверждён распределительным расчётом; чувствительные ошибки обнаружены |
| P3: factorial error сокращается, \(C^0\) сохраняет коэффициент один | Подтверждён (4.6)–(4.7) и формальными source checks |
| P4: короткий возврат не даёт полного signed upper | Вспомогательный бюджет доказан; главный требуемый upper не получен |

Выполнены самопроверка алгебры, source-map аудит самим автором и приведённые exact controls. **Нового независимого математического аудитора не было.** Не запускались Lean, Arb, production-спектр, исторический код, новые внешние арифметические запросы или repository writes. Наличие исполняемого кода не сертифицирует все PAPER-доказательства.


## 10. Manifest всех десяти исходников

Строки — физические LF-строки канонического TXT; delimiter LF не входит в source body.

| ID | Файл | Bytes | LF | Строки TXT | SHA256 |
|---|---|---:|---:|---|---|
| S1 | `CCM_Q42_CONCLUSION.md` | 3515 | 65 | 28–92 | `4051d5e9d438cf6e446a010cc7b9794f7c424ae405ccf4234b592ebccc6da7e9` |
| S2 | `PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_VERDICT_2026-10-26.md` | 73103 | 1313 | 97–1409 | `1ee3011c7dff10d052ef23b60992ff5b8f4551da8124bbaac2149df09efef893` |
| S3 | `CCM_POST_Q42_WEIGHTED_CONTRACTION.md` | 4999 | 90 | 1414–1503 | `2c225499191d914fe3d1f82b9c8717480eed8886f38f9cb230a755d2985e02ad` |
| S4 | `CCM_POST_Q42_MULTISCALE_SCREEN.md` | 3118 | 57 | 1508–1564 | `4cb686fe44063d054d1a872b730a36270e200a75be16f63b8868dfa833d871bb` |
| S5 | `CCM_JOINT_Q04_CONCLUSION.md` | 5036 | 92 | 1569–1660 | `617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086` |
| S6 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 | 123 | 1665–1787 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` |
| S7 | `CCM_Q32_CONCLUSION.md` | 3625 | 64 | 1792–1855 | `183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245` |
| S8 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 | 69 | 1860–1928 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` |
| S9 | `CCM_Q40_CONCLUSION.md` | 5988 | 111 | 1933–2043 | `e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06` |
| S10 | `CCM_Q20_SELBERG_PAIR_ATTEMPT.md` | 10197 | 190 | 2048–2237 | `4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f` |

## 11. Воспроизведение четырёх приложений

Сохрани этот Markdown и канонический TXT. Команда извлекает только четыре
новых приложения Q43, проверяет их хеши, запускает один стандартно-библиотечный
проверяющий и сравнивает его JSON с включённым результатом. Исторический код
в source bodies не исполняется.

```bash
python3 - \
  PROSHKA_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43_VERDICT_2026-10-26.md \
  PROSHKA_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43_2026-10-26.txt \
  q43_replay <<'PY'
from pathlib import Path
import hashlib, json, re, subprocess, sys
md=Path(sys.argv[1]); packet=Path(sys.argv[2]).resolve(); out=Path(sys.argv[3]).resolve()
out.mkdir(parents=True,exist_ok=True); data=md.read_bytes(); assets={}
pat=re.compile(rb'^BEGIN_Q43_ASSET ([A-Za-z0-9_.-]+) BYTES=(\d+) SHA256=([a-f0-9]{64})\n```[^\n]*\n',re.M)
for hit in pat.finditer(data):
    name=hit[1].decode(); size=int(hit[2]); start=hit.end(); body=data[start:start+size]
    if name in assets or len(body)!=size or hashlib.sha256(body).hexdigest()!=hit[3].decode():
        raise ValueError('Asset fingerprint mismatch: '+name)
    if data[start+size:start+size+4]!=b'```\n': raise ValueError('Invalid closing fence')
    assets[name]=body; (out/name).write_bytes(body)
expected={'preregistration_q43.json','q43_manifest.json','check_q43.py','q43_results.json'}
if set(assets)!=expected: raise ValueError('Unexpected asset set')
run=subprocess.run([sys.executable,str(out/'check_q43.py'),str(packet)],
                   cwd=out,check=True,capture_output=True,text=True)
(out/'check_q43.stdout').write_text(run.stdout,encoding='utf-8')
if (out/'q43_results.json').read_bytes()!=assets['q43_results.json']:
    raise ValueError('Replay differs from embedded result')
print(json.dumps({'assets':len(assets),'checks_run':1,'json_byte_identical':True,
                  'historical_code_run':False},sort_keys=True,indent=2))
PY
```

Первые два аргумента — реальные пути к сохранённым Markdown и TXT. Третий —
каталог извлечения. Например, при сохранении в Downloads замени первый путь
на `"$HOME/Downloads/PROSHKA_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43_VERDICT_2026-10-26.md"`,
второй — на соответствующий путь к TXT. Ничего внутри canonical/source bodies
для запуска менять не требуется.

### `preregistration_q43.json`

BEGIN_Q43_ASSET preregistration_q43.json BYTES=1296 SHA256=c3bd6d3b86315ad5168c692d026267ae418ebea99f49dd66ffc17ce50de9dd9c
```json
{
  "request_id": "Q43_ORIGINAL_METRIC_SIGNED_PRIMITIVE",
  "stage": "After full source reading and analytic derivation; before new executable mathematical checks. This is not advance registration of the analytic derivation.",
  "mechanism": "Joint differentiated balanced primitive: retain Mangoldt convolution and both adjoints, evaluate the exact factorial cumulative source, and return its complete signed quadrature error.",
  "predictions": {
    "P1": "The actual Mangoldt-primitive convolution equals psi minus the complete finite factorial sum, including the balancing atom and all prime powers.",
    "P2": "The derivative must contain both the exponential-weight term and every jump. The finite upper-cutoff seam cancels only after its exact return.",
    "P3": "The two copies of the factorial error cancel jointly; the centered prime discrepancy survives with coefficient one.",
    "P4": "The paid short correction has a vanishing-epsilon exponent, but no independent favorable upper for the remaining signed discrepancy is supplied by this calculation."
  },
  "not_predicted": ["RH", "A new all-P exponent", "An actual-source impossibility theorem"],
  "checks_scope": "Exact finite arithmetic and algebra; rational logarithm enclosures. No production CCM matrix, Lean or Arb."
}
```
END_Q43_ASSET

### `q43_manifest.json`

BEGIN_Q43_ASSET q43_manifest.json BYTES=2719 SHA256=4507e8cf135d5f72101082af790b4f5eaba137c14b00185f69f6eba92ae4b3f7
```json
{
  "bytes": 129190,
  "file": "PROSHKA_CCM_ORIGINAL_METRIC_SIGNED_PRIMITIVE_Q43_2026-10-26.txt",
  "lf": 2240,
  "sha256": "17b8e7a51d140e0807ed8d12959ccad06d7ba06cbb52b08100293e42612272db",
  "sources": [
    {
      "bytes": 3515,
      "end_line": 92,
      "id": "S1",
      "lf": 65,
      "name": "CCM_Q42_CONCLUSION.md",
      "sha256": "4051d5e9d438cf6e446a010cc7b9794f7c424ae405ccf4234b592ebccc6da7e9",
      "start_line": 28
    },
    {
      "bytes": 73103,
      "end_line": 1409,
      "id": "S2",
      "lf": 1313,
      "name": "PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_VERDICT_2026-10-26.md",
      "sha256": "1ee3011c7dff10d052ef23b60992ff5b8f4551da8124bbaac2149df09efef893",
      "start_line": 97
    },
    {
      "bytes": 4999,
      "end_line": 1503,
      "id": "S3",
      "lf": 90,
      "name": "CCM_POST_Q42_WEIGHTED_CONTRACTION.md",
      "sha256": "2c225499191d914fe3d1f82b9c8717480eed8886f38f9cb230a755d2985e02ad",
      "start_line": 1414
    },
    {
      "bytes": 3118,
      "end_line": 1564,
      "id": "S4",
      "lf": 57,
      "name": "CCM_POST_Q42_MULTISCALE_SCREEN.md",
      "sha256": "4cb686fe44063d054d1a872b730a36270e200a75be16f63b8868dfa833d871bb",
      "start_line": 1508
    },
    {
      "bytes": 5036,
      "end_line": 1660,
      "id": "S5",
      "lf": 92,
      "name": "CCM_JOINT_Q04_CONCLUSION.md",
      "sha256": "617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086",
      "start_line": 1569
    },
    {
      "bytes": 5633,
      "end_line": 1787,
      "id": "S6",
      "lf": 123,
      "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
      "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
      "start_line": 1665
    },
    {
      "bytes": 3625,
      "end_line": 1855,
      "id": "S7",
      "lf": 64,
      "name": "CCM_Q32_CONCLUSION.md",
      "sha256": "183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245",
      "start_line": 1792
    },
    {
      "bytes": 6174,
      "end_line": 1928,
      "id": "S8",
      "lf": 69,
      "name": "CCM_SPARSE_BAND_RECEIVER.md",
      "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
      "start_line": 1860
    },
    {
      "bytes": 5988,
      "end_line": 2043,
      "id": "S9",
      "lf": 111,
      "name": "CCM_Q40_CONCLUSION.md",
      "sha256": "e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06",
      "start_line": 1933
    },
    {
      "bytes": 10197,
      "end_line": 2237,
      "id": "S10",
      "lf": 190,
      "name": "CCM_Q20_SELBERG_PAIR_ATTEMPT.md",
      "sha256": "4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f",
      "start_line": 2048
    }
  ]
}
```
END_Q43_ASSET

### `check_q43.py`

BEGIN_Q43_ASSET check_q43.py BYTES=10367 SHA256=fe66eb3e62ff173dfe45894b5e12a3a3db53758606e2a07123363737abac85d8
```python
#!/usr/bin/env python3
"""Q43 exact source/endpoint checks. Standard library only, no spectral claims."""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
from functools import lru_cache
import argparse
import hashlib
import json
import re


def factor(n):
    out = {}; d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0)+1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0)+1
    return out


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1)**len(fs)


# A vector of rational coefficients: coordinate 0 denotes 1, coordinate p log(p).
# Comparing vectors is exact; no floating-point logarithms are used.
def add(a, b):
    c = a.copy()
    for p, v in b.items(): c[p] = c.get(p, F())+v
    return {p:v for p,v in c.items() if v}


def scale(a, v):
    return {p:F(v)*x for p,x in a.items() if F(v)*x}


def sub(a, b): return add(a, scale(b, -1))


def logq(q):
    q = F(q)
    if q <= 0: raise ValueError('positive logarithm argument required')
    a = {p:F(e) for p,e in factor(q.numerator).items()}
    return sub(a, {p:F(e) for p,e in factor(q.denominator).items()})


def lam(n):
    fs = factor(n)
    return {next(iter(fs)):F(1)} if len(fs) == 1 else {}


def sumvec(rows):
    a = {}
    for r in rows: a = add(a, r)
    return a


def conv(a, b, m):
    c = [F()]*(m+1)
    for d in range(1, m+1):
        if not a[d]: continue
        for k in range(1, m//d+1):
            if b[k]: c[d*k] += a[d]*b[k]
    return c


def make(U, m):
    if m < U+1: raise ValueError('m must retain the balancing atom')
    v = U+1; a = sum((F(mu(d),d) for d in range(1,U+1)), F()); tau = v*a
    u = [F()]*(m+1)
    for d in range(1,U+1): u[d] = F(mu(d))
    u[v] = -tau
    one = [F()]+[F(1)]*m
    g = conv(one,u,m)
    y = [-x for x in g]; y[1] += 1
    return v,a,tau,u,g,y


def math_checks():
    summaries=[]; failures={}; source_cases=[(2,40),(5,80),(67,210)]
    counts={'integer_coefficient_checks':0,'real_floor_checks':0,
            'endpoint_pairings':0,'scalar_error_intervals':0}
    captured = None
    for U,m in source_cases:
        v,a,tau,u,g,y = make(U,m)
        assert sum((u[d]/d for d in range(1,m+1)),F()) == 0
        assert all(y[n] == 0 for n in range(1,U+1))
        assert y[v] == F(mu(v))+tau
        ls=[{} for _ in range(m+1)]; cs=[{} for _ in range(m+1)]
        for d in range(1,m+1):
            if u[d]:
                for k in range(1,m//d+1):
                    ls[d*k]=add(ls[d*k],scale(logq(k),u[d]))
        for n in range(1,m+1):
            for d in range(2,n+1):
                if n%d == 0 and y[n//d]:
                    cs[n]=add(cs[n],scale(lam(d),y[n//d]))
            assert add(ls[n],cs[n]) == lam(n)
            counts['integer_coefficient_checks'] += 1
        psi=[{} for _ in range(m+1)]; J=[{} for _ in range(m+1)]
        Pi=[{} for _ in range(m+1)]; logfac=[{} for _ in range(m+1)]
        for n in range(1,m+1):
            psi[n]=add(psi[n-1],lam(n)); J[n]=add(J[n-1],ls[n])
            Pi[n]=add(Pi[n-1],cs[n]); logfac[n]=add(logfac[n-1],logq(n))
        points={F(1),F(v)-F(1,2),F(v),F(v)+F(1,2),F(2*v),F(m)-F(1,2),F(m)}
        for x in sorted(points):
            if not 1 <= x <= m: continue
            N=int(x)
            exactJ=sumvec(scale(logfac[int(x/d)],u[d]) for d in range(1,v+1))
            h=lambda z: F(1)-sum((u[d]*int(z/d) for d in range(1,v+1)),F())
            exactPi=sumvec(scale(lam(n),h(x/n)) for n in range(2,N+1))
            assert exactJ==J[N]
            assert exactPi==Pi[N]==sub(psi[N],exactJ)
            if x<v: assert not exactPi and exactJ==psi[N]
            counts['real_floor_checks']+=1
        # Step-function integration, including the upper atom. Each coordinate is formal log(p).
        for w in (lambda x:F(1)+F(x,3), lambda x:F((x-1)**2*(m-x)**2)):
            direct=sumvec(scale(cs[n],w(n)) for n in range(2,m+1))
            integral=sumvec(scale(Pi[n],w(n+1)-w(n)) for n in range(1,m))
            returned=sub(scale(Pi[m],w(m)),integral)
            assert returned==direct
            counts['endpoint_pairings']+=1
            if w(m) and Pi[m]:
                failures['drop_terminal_primitive_term']=(scale(integral,-1)!=direct)
        # Full signed return E - R + e*(x-1), no separate moduli.
        beta=scale(sumvec(scale(logq(d),u[d]/d) for d in range(1,v+1)),-1)
        for x in (F(v),F(2*v)+F(1,2),F(m)):
            if x>m: continue
            N=int(x); E=sub(psi[N],{0:x-1}); RU=sub(J[N],scale(beta,x-1))
            e=sub({0:F(1)},beta)
            assert sub(add(E,scale(e,x-1)),RU)==Pi[N]
        if U==5: captured=(v,a,tau,u,g,y,psi,J,Pi,ls,cs)
        summaries.append({'U':U,'m':m,'tau':str(tau),'jump_y_at_v':str(y[v]),
                          'production_sparse_band_cell':False})
    v,a,tau,u,g,y,psi,J,Pi,ls,cs=captured
    failures['omit_balancing_atom']=sum((F(mu(d),d) for d in range(1,v)),F())!=0
    failures['wrong_factorial_subtraction_sign']=any(add(psi[n],J[n])!=Pi[n] for n in range(2,len(Pi)))
    failures['delete_prime_powers']=sumvec(lam(d) for d in range(2,5) if 4%d==0 and len(factor(d))==1 and next(iter(factor(d).values()))==1)!=logq(4)
    # Density on a constant primitive segment: (d/dt+sigma)e^(-sigma*t)h=0.
    # Removing sigma leaves -sigma*h, a nonzero smooth term in addition to the jumps.
    sig=F(1,2); h=y[v]
    assert h != 0  # actual U=5 first primitive plateau
    assert -sig*h+sig*h==0
    failures['omit_weight_derivative_term']=(-sig*h != 0)
    # A generic polarized check: transpose is not a complex adjoint.
    # Gaussian rationals are represented by (real,imaginary), still exact.
    def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
    z=(F(1,3),F(2,5)); w=(F(3,7),F(-1,2))
    true=mul((z[0],-z[1]),w)[0]
    wrong=mul(z,w)[0]
    assert true!=wrong
    failures['replace_adjoint_by_transpose']=true!=wrong
    assert all(failures.values()) and len(failures)==6
    # Exact outward logarithm enclosures test the actual cofinal U=67 and all seams.
    U=67; m=210; v,a,tau,u,g,y=make(U,m)
    assert U*abs(a)<=F(1,2)
    beta=scale(sumvec(scale(logq(d),u[d]/d) for d in range(1,v+1)),-1)
    blo,bhi=evaluate_interval(beta)
    assert F(1,5)<=blo<=bhi<=F(9,5)
    S=sum(abs(u[d]) for d in range(1,v+1))
    panel=[]
    for x in (F(v),F(2*v-1,2),F(2*v+1,2),F(2*v),F(3*v)+F(1,2),F(m)):
        if x<v: continue
        jf=sumvec(scale(sumvec(logq(k) for k in range(1,int(x/d)+1)),u[d]) for d in range(1,v+1))
        RU=sub(jf,scale(beta,x-1)); lo,hi=evaluate_interval(RU)
        lx,_=log_interval(x)
        lower_cap=S*(1+lx)+F(9,5)
        assert max(abs(lo),abs(hi))<=lower_cap
        counts['scalar_error_intervals']+=1
        panel.append({'x':str(x),'verified_bound':'|R_U(x)| <= S_U*(1+log(x))+9/5'})
    # Elementary integrals used in the budget, checked as rational coefficients.
    # Antiderivative of (1+log x)x^(-3/2) is -2x^(-1/2)(log x+3).
    # Coefficient of log x and constant in its derivative:
    assert (F(1), F(3)-F(2))==(F(1),F(1))
    assert F(4,5)*2 == F(8,5)
    return {'status':'EXACT_DIAGNOSTICS_NOT_PRODUCTION_SIGN_CERTIFICATE',
            'source_cases':summaries,'counts':counts,'actual_cofinal_predicate_U':67,
            'actual_factorial_remainder_panel':panel,'planted_failures_detected':failures,
            'planted_failure_count':len(failures),'new_arithmetic_gain':False,
            'production_spectrum':False,'lean':False,'arb':False}


@lru_cache(None)
def log_interval(q):
    q=F(q)
    if q<=0: raise ValueError('log requires a positive rational')
    if q<1:
        a,b=log_interval(1/q); return -b,-a
    k=0
    while q>2: q/=2; k+=1
    def near(r):
        t=(r-1)/(r+1); N=32
        lo=2*sum((t**(2*j+1)/F(2*j+1) for j in range(N)),F())
        rem=2*t**(2*N+1)/(F(2*N+1)*(1-t*t))
        return lo,lo+rem
    a,b=near(q); c,d=near(F(2))
    return a+k*c,b+k*d


def evaluate_interval(vec):
    lo=hi=vec.get(0,F())
    for p,a in vec.items():
        if p==0: continue
        x,y=log_interval(F(p))
        if a>=0: lo+=a*x; hi+=a*y
        else: lo+=a*y; hi+=a*x
    return lo,hi


def verify_packet(path, manifest):
    data=path.read_bytes(); data.decode('utf-8',errors='strict')
    if (len(data),data.count(b'\n'),hashlib.sha256(data).hexdigest()) != (manifest['bytes'],manifest['lf'],manifest['sha256']):
        raise ValueError('canonical file fingerprint mismatch')
    pat=re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([a-f0-9]{64})\n')
    pos=data.index(b'BEGIN_SOURCE S1 ')
    for expected in manifest['sources']:
        mt=pat.match(data,pos)
        if not mt: raise ValueError('invalid source header')
        start=mt.end(); end=start+int(mt[3]); body=data[start:end]
        body.decode('utf-8',errors='strict')
        row={'id':mt[1].decode(),'name':mt[2].decode(),'bytes':len(body),'lf':body.count(b'\n'),
             'sha256':hashlib.sha256(body).hexdigest(),
             'start_line':data[:start].count(b'\n')+1,'end_line':data[:end].count(b'\n')}
        if row!=expected or row['lf']!=int(mt[4]) or row['sha256']!=mt[5].decode():
            raise ValueError('source fingerprint mismatch: '+row['id'])
        suffix=b'\nEND_SOURCE '+mt[1]+b'\n'
        if data[end:end+len(suffix)]!=suffix: raise ValueError('source end frame mismatch')
        pos=end+len(suffix)
        while pos<len(data) and data[pos:pos+1] in (b'\n',b'\r',b' ',b'\t'): pos+=1
    if pos!=len(data): raise ValueError('unframed trailing data')
    return {'canonical_bytes':len(data),'canonical_lf':data.count(b'\n'),
            'canonical_sha256':manifest['sha256'],'source_count':len(manifest['sources']),
            'all_frames_match':True,'historical_code_executed':False,
            'hashes_certify_mathematics':False}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('canonical_txt',type=Path)
    args=ap.parse_args(); root=Path(__file__).resolve().parent
    manifest=json.loads((root/'q43_manifest.json').read_text(encoding='utf-8'))
    result={'manifest':verify_packet(args.canonical_txt,manifest),'mathematics':math_checks()}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (root/'q43_results.json').write_text(text,encoding='utf-8'); print(text,end='')

if __name__=='__main__': main()
```
END_Q43_ASSET

### `q43_results.json`

BEGIN_Q43_ASSET q43_results.json BYTES=2109 SHA256=a94d0c24835d4b986f542cf52d37634e5e09ee1a433bce228c56e69970879c70
```json
{
  "manifest": {
    "all_frames_match": true,
    "canonical_bytes": 129190,
    "canonical_lf": 2240,
    "canonical_sha256": "17b8e7a51d140e0807ed8d12959ccad06d7ba06cbb52b08100293e42612272db",
    "hashes_certify_mathematics": false,
    "historical_code_executed": false,
    "source_count": 10
  },
  "mathematics": {
    "actual_cofinal_predicate_U": 67,
    "actual_factorial_remainder_panel": [
      {
        "verified_bound": "|R_U(x)| <= S_U*(1+log(x))+9/5",
        "x": "68"
      },
      {
        "verified_bound": "|R_U(x)| <= S_U*(1+log(x))+9/5",
        "x": "137/2"
      },
      {
        "verified_bound": "|R_U(x)| <= S_U*(1+log(x))+9/5",
        "x": "136"
      },
      {
        "verified_bound": "|R_U(x)| <= S_U*(1+log(x))+9/5",
        "x": "409/2"
      },
      {
        "verified_bound": "|R_U(x)| <= S_U*(1+log(x))+9/5",
        "x": "210"
      }
    ],
    "arb": false,
    "counts": {
      "endpoint_pairings": 6,
      "integer_coefficient_checks": 330,
      "real_floor_checks": 21,
      "scalar_error_intervals": 5
    },
    "lean": false,
    "new_arithmetic_gain": false,
    "planted_failure_count": 6,
    "planted_failures_detected": {
      "delete_prime_powers": true,
      "drop_terminal_primitive_term": true,
      "omit_balancing_atom": true,
      "omit_weight_derivative_term": true,
      "replace_adjoint_by_transpose": true,
      "wrong_factorial_subtraction_sign": true
    },
    "production_spectrum": false,
    "source_cases": [
      {
        "U": 2,
        "jump_y_at_v": "1/2",
        "m": 40,
        "production_sparse_band_cell": false,
        "tau": "3/2"
      },
      {
        "U": 5,
        "jump_y_at_v": "4/5",
        "m": 80,
        "production_sparse_band_cell": false,
        "tau": "-1/5"
      },
      {
        "U": 67,
        "jump_y_at_v": "6763244587410648983528/77042368147845755449795",
        "m": 210,
        "production_sparse_band_cell": false,
        "tau": "6763244587410648983528/77042368147845755449795"
      }
    ],
    "status": "EXACT_DIAGNOSTICS_NOT_PRODUCTION_SIGN_CERTIFICATE"
  }
}
```
END_Q43_ASSET

