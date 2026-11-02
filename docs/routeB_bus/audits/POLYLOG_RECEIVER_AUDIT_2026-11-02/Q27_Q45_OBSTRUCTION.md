# Где остановились Q27 и Q45 — одна страница

DIAGNOSTIC_NEVER_A_PROOF. Проверены закреплённые тексты на base
`d7951a2bfdbdbc6b1dd6cc3ec4f96454c39fb573`; это фиксация границы архива,
не новый благоприятный source sign. H0 ниже — старый complex polylog
receiver; он не отождествляется молча с новым even H_m.

**Q27, §§6–8, особенно (6.3), (7.4), (7.5).** Полная causal-инверсия дала

    A0 = -Hdecay + V_m - R_(m,u,H) + E_m,
    ||V_m||=O(L²(log L)²),  ||E_m||=o(1),  0<=Hdecay<=4I,
    R=He sum_(Re rho-1/2>u, |Im rho|<H)
          r_rho m^(rho-1/2) S0(rho-1/2).

Здесь S0=(1/L)Pi0(v_+v_+^T+v_-v_-^T)Pi0 — аналитические квадраты
с transpose, не adjoint. Контакты убирают главный полюс и leading tail,
но не делают эту матрицу PSD. **Первая неоплаченная строка:** общий
lower `R>=-b_m I`, b_m=m^o(1), либо более слабое достаточное совместное
сравнение с Hdecay/на всей actual pair. Оно дало бы нужный UPPER A0.
Оценка каждого вычета модулем в (7.5) теряет фазы и направления и стоит
O(sqrt(m)L²log L); остаётся более дешёвый fallback A0<=12sqrt(m)I.
Меньший analytic-return, меньшая размерность и положительность другой
метрики этого знака не дают. Для отдельного H0 receiver all-P перенос
не нужен; для all-P неоплачены ещё complement/coupling (§9).

**Q45, A1–A6 и completion budget.** Для действительной источниковой
комплексной пары g,k доказан fixed-strip analytic correlation C и
growing-order budget C0^(q+1)(q!)². При y=L-2log L, D=floor(m/L^6)
Euler–Maclaurin оплачивает весь d<=D prefix с cutoff tails как o(1).
Остаётся ТОЧНЫЙ signed scalar

    J_long=sum_(k<L^6) log(k)/sqrt(k)
       sum_(D<d<=m/k) mu(d)/sqrt(d)
          [C(y-log(dk))+C(y+log(dk))] + o(1).

**Первая неоплаченная строка:** независимая направленная оценка этих
длинных mu-сумм, достаточная для actual-pair margin. Из k<L^6 не следует
их cancellation. Гипотеза |M(t)|<=K t^beta дала бы при 1/2<=beta<1 цену
O_(w,beta)(K m^(beta-1/2)L^(7-8beta)log L)+o(1);
строгое beta-1/2<delta хватило бы для o(negative-signal scale).
Такая гипотеза НЕ поставлена. Trivial beta=1 даёт лишь
O_w(sqrt(m)(log L)²/L), хуже сохранённой endpoint цены sqrt(m)/L.

Q45 — reduction для actual pair, не uniform prime upper на всех H0 или P.
Буквальный перенос его strip analyticity на все compactly supported
автокорреляции невозможен: C_f=0 на (L,infinity), C_f(0)=1; holomorphic
strip extension тогда противоречила бы identity theorem. Это ограничение
данного переноса, не no-go всех методов. Оба архива оставляют открытым
нужный односторонний source bound; новый centered Gram budget его не заменяет.
