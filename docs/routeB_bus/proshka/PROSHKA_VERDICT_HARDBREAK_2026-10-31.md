# STATUS: TRY_HARDBREAK_LAGUERRE_MOMENT_WITH_EXACT_MEAN_GUARD
```yaml
OPERATIVE_CLASS: TRY_HARDBREAK_LAGUERRE_MOMENT_WITH_EXACT_MEAN_GUARD
DATE: 2026-10-31
AUTHORITY: DIRECT_OWNER_DOUBLE_LOCK_REQUEST_IN_CURRENT_MESSAGE
PREDECESSOR: PROSHKA_VERDICT_SCALEJET_2026-10-31.md
PREDECESSOR_SHA256: 599e50b77946d7e9da82943f3dbfeef48ffa66d5dba6aca6a5727ec32d8669fb
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
CARRIER: LITERAL_CCM_N_EQUALS_M_L_EQUALS_LOG_M
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
NEW_SOURCE_IDENTITY: FIRST_LOG_MOMENT_EQUALS_LAGUERRE_DENSITY_MINUS_ARCH_AND_NEAR
NEW_ONE_SIDED_BOUND: NEGATIVE_FIRST_MOMENT_CONTROLLED_BY_WEIGHTED_POLYNOMIAL_DERIVATIVE_GRAM
POLYNOMIAL_IN_K_BOUND_PROVED: false
MOMENT_SIGN_FOR_ALL_K: NOT_DETERMINED
DILATION_SUPPLIES_REQUESTED_FIRST_LOG_MOMENT: false
EXACT_FINITE_JET_MEANS_FORBID_NEGATIVE_LEAKAGE: REFUTED
COUNTEREXAMPLE_PRESERVES_BACKGROUND_H_MEAN: true
COUNTEREXAMPLE_PRESERVES_ALL_FINITE_JET_CROSS_MEANS: true
STRONGER_COUNTEREXAMPLE_PRESERVES_FIRST_LOG_MOMENTS: true
COUNTEREXAMPLE_IS_LITERAL_PRIME_SOURCE: false
COUNTEREXAMPLE_PRESERVES_ENTIRE_INFINITE_THETA_RADICAL: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS: SOURCE_ONE_SIDED_INEQUALITY_AND_EXACT_MEAN_THEOREM_SHAPE_REFUTATION
COGNITIVE_OPERATOR: DUALIZE
ROUTE_SCORE: 3
VERIFIER: PAPER
EXACT_SYMBOLIC_GROUPS_PASSED: 7
SCALEJET_EXACT_REPLAY: 8_GROUPS_PASSED_WITH_MATCHING_SCRIPT_HASH
LITERAL_FIRST_MOMENT_PROBE: K_3_FLOATING_DIAGNOSTIC_NOT_CERTIFICATE
NEW_CCM_BOTTOM_SCAN: false
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
RH_PROVED: false
T_PROVED: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Решение

**Окончательного доказательства RH в этом батче нет.** Приказ содержит две предполагаемые импликации. Первая — «нулевая Weil-энергия автоматически даёт полиномиальную цену первого логарифмического момента» — не следует из продифференцированного радикального тождества. Вторая — «точное среднее запрещает большую отрицательную часть» — ложна. Её опровергает контроль, сохраняющий не только среднее фона `h`, но все квадратичные и смешанные равенства любого заранее заданного конечного джета.

Работа не остановлена на этих возражениях. Для **настоящего источника** выведено новое точное представление первого момента:

\[
\boxed{
 M_r^{\mathrm{full}}+J_r
 =\frac1\pi\int_{\mathbb R}P(t)^2
       \bigl(H'(t)^2-H(t)H''(t)\bigr)\,dt,
 \qquad \widehat r=P H.
}
\tag{0.1}
\]

Оно сохраняет всю недиагональную структуру. Из него получен односторонний бюджет, которому **не нужна норма `T_3(r)` для первого момента**:

\[
\boxed{
 M_r^{\mathrm{far}}\ge
 -\bigl(\mu_K+18/25+C_{s_0}^{(1)}\bigr)\|r\|_{\mathscr G}^2,
 \quad r\in\mathcal R_K,
}
\tag{0.2}
\]

где `mu_K` — явно определённая конечная норма дифференцирования полиномов с весом `H²`, см. §5. Утверждение `mu_K <= C K²` **не доказано**; его не заменяют ни график, ни слово «радикал». Однако теперь первый момент сводится к конкретному Gram-поставщику без полного экспоненциального пространственного мажоранта.

Результаты — PAPER с явно перечисленными унаследованными входами. Самопроверка и две численные реализации не являются независимой рецензией. Нового разрешения на запись этого файла в GitHub нет; прежние разрешения были привязаны к другим путям. Репозиторий не менялся.

## 1. Source lock, обозначения и обязательный знак

### 1.1 Фактически прочитанные источники

| Код | Источник | Использование |
|---|---|---|
| S1 | `PROSHKA_VERDICT_SCALEJET_2026-10-31.md`, 63246 bytes, 985 LF, SHA256 `599e50b77946d7e9da82943f3dbfeef48ffa66d5dba6aca6a5727ec32d8669fb` | Полный текст: точное среднее (4.4), хвост, Gram-метрика, степень, локализация, отрицательный контроль |
| S2 | `PROSHKA_VERDICT_SCALEBRIDGE_2026-10-31.md`, SHA256 `9e0b544b6953e520016f6e62e8a05e4bfe53f37f74b210fd805ff9e852af19d2` | Используются указанные в S1 fixed-profile и positive-average consumers, без объявления нового полного аудита |
| S3 | `PROSHKA_VERDICT_CONFINE_2026-10-30.md`, SHA256 `57088a914942b0dd1c3d1835edaca2f223a59831d78350c0a092356024852ddb` | §1: theta, полная форма, явная формула, область смешанного радикального тождества |
| S4 | `PROSHKA_VERDICT_ENERGYBOUND_2026-10-31.md`, SHA256 `255309f7a0c5bbd4240b626370b7ef3e0e854335c225a50187c880084bdfae26` | Фиксированная энергетическая норма и унаследованный конечный возврат |
| P | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13` | Получен через GitHub connector, включая конец |
| E1 | N. Elkies, Math 259, `zeta2.pdf`, pp.1–2, `prod.pdf`, theorem p.1 | Порядок 1 завершённой xi, произведение Адамара и суммируемость обратных квадратов нулей |
| E2 | NIST DLMF 25.4.3–25.4.4, 25.10(i) | Нормировка xi, функциональное уравнение, безусловная полоса нулей |
| E3 | G. Csordas, A. Ruttan, R. S. Varga, *The Laguerre inequalities with applications to a problem associated with the Riemann hypothesis*, Numerical Algorithms 1 (1991), abstract | Название стандартного выражения `(H')²-HH''`; никакая его глобальная положительность не импортируется |

У Elkies символ `xi` обозначает мероморфную завершённую функцию без множителя `s(s-1)/2`. Здесь этот множитель восстановлен; произведение применяется к **целой** функции `H`. Текст PDF прочитан; обе попытки web-screenshot вернули `Cache miss`. Никакого визуального аудита этих PDF не заявлено. Все использованные формулы присутствуют в полученном тексте.

### 1.2 Унаследованный буквальный объект

**[ABSTRACT | PAPER; source definitions]**

\[
 h(x)=\sum_{n\ge1}(16\pi^2n^4e^{9x/2}-24\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}},
 \qquad H(t)=\widehat h(t)=4\xi(1/2-it),
\]
\[
 \widehat f(t)=\int f(x)e^{-itx}dx,\quad
 Q_f(s)=2\operatorname{Re}\int\overline{f(x)}f(x+s)dx,
 \quad p_f(t)=|\widehat f(t)|^2/(2\pi).
\]

For real even functions the `Re` is redundant. Let

\[
 d\nu(s)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)-e^{s/2}ds,
 \quad
 j_+(s)=\frac{e^{-5s/2}}{1-e^{-2s}},
\]
\[
 c_0=4-\gamma-\log(8\pi)-\pi/2,
 \quad
 \mathcal H_+[f]=\int_0^\infty j_+(s)(2\|f\|_2^2-Q_f(s))ds,
\]
\[
 \mathscr G[f]=\|f\|_2^2+\mathcal H_+[f]
 =\frac1{2\pi}\int w(t)|\widehat f(t)|^2dt.
\]

For the admissible exponentially decaying smooth tests used below, including their modulations, the **full** source is

\[
 \mathfrak k[f]=c_0\|f\|_2^2+\mathcal H_+[f]-\int_0^\infty Q_f(s)d\nu(s).
 \tag{1.1}
\]

This is the same compensation as before. For complex auxiliary modulations it retains both pole sectors: `p(x)p(y)-q(x)q(y)=2 cosh((x-y)/2)`. The odd pole is not silently removed on those auxiliary tests.

Set

\[
 \mathcal R_K=\operatorname{span}_{\mathbb R}\{h,h'',\ldots,h^{(2K-2)}\},
 \quad r=\sum_{i=0}^{K-1}\alpha_i h^{(2i)},
\]
\[
 P(t)=\sum_{i=0}^{K-1}(-1)^i\alpha_i t^{2i},\qquad \widehat r=P H,
\]
\[
 M_r^{\rm full}=\int_0^\infty sQ_r(s)d\nu(s),\quad
 M_r^{\rm far}=\int_{(s_0,\infty)}sQ_r(s)d\nu(s),\quad
 J_r=\int_0^\infty s j_+(s)Q_r(s)ds.
 \tag{1.2}
\]

All these integrals converge absolutely for each fixed polynomial `P`; every prime power is included. `M_near` includes a possible atom at `s0` and `M_far` excludes it.

The exact source average from S1 is

\[
 \int p_r\overline B_M
 =\mathcal H_+[r]+c_0\|r\|_2^2-\mathcal S^{\rm near}[r]
   -\beta_M M_r^{\rm far}+\mathcal E_M(r),
 \qquad \beta_M>0.
 \tag{1.3}
\]

**For an upper bound in (1.3), the dangerous sign is the negative part of `M_r`, not its whole absolute value.** The meaningful coordinate-invariant quantity is

\[
 \gamma_K^-=
 \max\{0,-\lambda_{\min}(G_K^{-1/2}\mathbb M_K^{\rm far}G_K^{-1/2})\}.
 \tag{1.4}
\]

Raw matrix entries depend on the normalization of the derivative basis. A statement that the raw matrix «grows polynomially» is not the appropriate invariant supplier. Also, a bound `gamma_K^- <= C K^p` would permit `K` of order `(log M)^(1/p)` through the first moment. To reach `sqrt(log M)` in this way one needs `p<=2`, not merely an unspecified polynomial. The source tail and detector leakage must still be paid.

## 2. What differentiation of radicality actually supplies

### Lemma 1. Dilation gives a different moment

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** Let `r` be any fixed finite theta-jet and let

\[
 r_a(x)=a^{1/2}r(ax),\quad a>0.
\]

Then `||r_a||=||r||`, `Q_{r_a}(s)=Q_r(as)`, and

\[
 \left.\frac d{da}\mathfrak k[r_a]\right|_{a=1}
 =-\int_0^\infty sQ_r'(s)(j_+(s)ds+d\nu(s))=0.
 \tag{2.1}
\]

**Proof.** Differentiation under the integrals is justified by the exponential weighted bounds of the fixed profiles. On the physical side the derivative is `2 Re k(r, r/2+xr')`, which is zero by the full bilinear radical identity in S3. On the correlation side differentiating `Q_r(as)` gives `sQ_r'(s)`. The constant norm term has derivative zero. ∎

Equation (2.1) is a legitimate virial identity. It is **not** a formula for `int sQ_r dnu`. Integrating it by parts moves differentiation onto the distribution `s dnu`; the prime atoms produce differentiated distributions. It does not recreate the original first-moment measure.

Also `r_a` is not in general radical for `a != 1`: its Fourier transform is `a^(-1/2)P(t/a)H(t/a)`, whose zeros do not remain at the zeros of `H(t)`. A derivative at a single radical point is not an identity at all scales.

A minimal algebraic control is `A(epsilon)=epsilon diag(e^K,-e^(2K))`. At epsilon=0 the entire space is radical, while its first derivative has unrestricted signed growth. This control is not CCM and refutes only the generic inference from a value zero to a bound for a parameter derivative.

### Lemma 2. The correct first moment is a modulation/Poisson response

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER; literal source]** Put `r_v(x)=e^{ivx}r(x)`. Then

\[
 \boxed{M_r^{\rm full}+J_r
 =\frac1\pi\int_{\mathbb R}\frac{\mathfrak k[r_v]}{v^2}\,dv.}
 \tag{2.2}
\]

The integrand at v=0 has its removable continuous interpretation. Equivalently, let

\[
 \mathcal W_\epsilon(r)=c_0\|r\|^2+
 \int_0^\infty j_+(s)(2\|r\|^2-e^{-\epsilon s}Q_r(s))ds
 -\int_0^\infty e^{-\epsilon s}Q_r(s)d\nu(s).
\]

Then `W_0(r)=0`, but

\[
 \mathcal W'_0(r)=M_r^{\rm full}+J_r.
 \tag{2.3}
\]

**Proof.** Exactly `Q_{r_v}(s)=cos(vs)Q_r(s)`. Subtract (1.1) at v=0, use `k[r]=0`, and obtain

\[
 \mathfrak k[r_v]=\int_0^\infty(1-\cos(vs))Q_r(s)(j_+(s)ds+d\nu(s)).
\]

Now use `int_R (1-cos(vs))/(pi v²) dv=s` for s>0. Fubini is valid because

\[
 \int_0^\infty s|Q_r(s)|(j_+(s)ds+d|\nu|(s))<\infty.
\]

Near zero `s j_+` is bounded; at infinity the full prime and continuous terms are paid by any fixed exponential weight larger than 1/2. This proves (2.2) and absolute integrability. Direct differentiation proves (2.3). Averaging `k[r_v]` with the Cauchy density `epsilon/[pi(epsilon²+v²)]` gives `W_epsilon`, since its cosine transform is `exp(-epsilon s)`. ∎

The modulated tests `r_v` are generally **not** radical. Their sign has not been fixed by `k[r]=0`. Thus neither (2.2) nor (2.3) yields an unearned sign.

The archimedean correction is already uniformly bounded:

\[
 \boxed{|J_r|\le \frac{18}{25}\|r\|_2^2.}
 \tag{2.4}
\]

Indeed `|Q_r|<=2||r||²` and `int s j_+ <=9/25`. This auxiliary bound does not replace the target signed prime form by its modulus.

## 3. Exact reduction of the literal moment to a Laguerre density

### Theorem 3. The complete off-diagonal moment matrix

**THIS STEP IS PROVED HERE, conditional only on the inherited full explicit formula in S3 and the standard Hadamard theorem, not on RH. [ABSTRACT | PAPER]** Define

\[
 \mathcal L_H(t)=H'(t)^2-H(t)H''(t).
\]

For every fixed real even polynomial P and `r` with `rhat=P H`,

\[
 \boxed{M_r^{\rm full}+J_r
 =\frac1\pi\int_{\mathbb R}P(t)^2\mathcal L_H(t)dt.}
 \tag{3.1}
\]

The function `L_H` is real, even, and nonsingular, including at real zeros of H. It is the standard first Laguerre expression. No assertion that it is nonnegative on the whole real axis is made here.

**Proof, including zeros off the line and all exchanges.** Write `z_rho=i(rho-1/2)` and `R=P H`. The inherited explicit formula applied to the complex modulation `r_v` gives

\[
 \mathfrak k[r_v]=\sum_\rho R(z_\rho-v)^2.
 \tag{3.2}
\]

There is no absolute-square replacement: R is real entire, so conjugation in the Weil pairing produces this square, and nonreal zeros occur with their conjugates. For fixed P, R and R' have uniform exponential decay on every fixed horizontal strip. This follows by shifting the Fourier contour of the analytic, doubly exponentially decaying theta kernel, with the fixed spatial exponential weight needed for that strip.

For every zero z with large `|Re z|=gamma`, `|Im z|<=1/2`, splitting the v-integral into `|v|<=1`, `1<|v|<=gamma/2`, and `|v|>gamma/2` gives

\[
 \int_{\mathbb R}\frac{|R(z-v)|^2}{v^2}dv\le C_P/(1+\gamma^2).
 \tag{3.3}
\]

On the first interval use `R(z)=0` and the derivative bound; on the second use exponential decay; on the third use `v^-2<=4/gamma²` and a strip-uniform L² bound. Finitely many remaining zeros are harmless. The zero sum of `(1+gamma²)^-1` converges by the genus-one product theorem, so termwise integration in (3.2) is legitimate.

For each zero, set u=z-v. The integral becomes the integral of `R(u)^2/(u-z)^2` on the horizontal line through z. The apparent pole at z is removable because R vanishes there, even when that zero is simple. Move this line to the real axis; the vertical ends tend to zero by the stated strip decay. Thus

\[
 \int_{\mathbb R}\frac{R(z-v)^2}{v^2}dv
 =\int_{\mathbb R}\frac{R(u)^2}{(u-z)^2}du.
 \tag{3.4}
\]

This real-axis series is also absolutely integrable. For `|u|<=gamma/2` the denominator gives `O(gamma^-2)`. For `|u|>gamma/2` and `|u-z|>=1` use decay; on `|u-z|<1` use `R(u)/(u-z)=int_0^1 R'(z+t(u-z))dt`. The same summable bound as (3.3) follows.

Because H is entire of order 1 and H(0) is nonzero, Hadamard factorization yields, away from its zeros,

\[
 -\left(\frac{H'}H\right)'(u)=\sum_\rho\frac1{(u-z_\rho)^2}.
 \tag{3.5}
\]

The possible exponential linear factor has zero second logarithmic derivative. Multiplication by `R(u)^2=P(u)^2H(u)^2` removes every real-axis singularity. Combining (2.2)–(3.5) proves (3.1). All multiplicities remain in the sum. No location of a nontrivial zero within the critical strip was assumed. ∎

### Corollary 4. Hankel structure with computable physical entries

**[ABSTRACT | PAPER]** Put `n=i+j`. Then

\[
 \boxed{
 (\mathbb M_K^{\rm full}+\mathbb J_K)_{ij}
 =(-1)^n\left[4\|x h^{(n)}\|_2^2
                  -2n\|h^{(n-1)}\|_2^2\right].}
 \tag{3.6}
\]

At n=0 the second term is omitted; no negative derivative order is defined. For the actual far cutoff,

\[
 \mathbb M_K^{\rm far}=\mathbb L_K-\mathbb J_K-\mathbb N_K,
 \quad
 (\mathbb N_K)_{ij}=\int_{(0,s_0]}sQ_h^{(2i+2j)}(s)d\nu(s).
 \tag{3.7}
\]

**Proof.** Polarization gives the `ij` entry of (3.1) as `(-1)^n/pi int t^(2n)L_H(t)dt`. Integration by parts gives

\[
 \int t^{2n}\mathcal L_H
 =2\int t^{2n}(H')^2-n(2n-1)\int t^{2n-2}H^2.
\]

Plancherel and `D^n(xh)=x h^(n)+n h^(n-1)` then give (3.6), using `int x h^(n)h^(n-1)=-||h^(n-1)||²/2`. All endpoints vanish by theta decay. Equation (3.7) restores the declared far cutoff exactly. ∎

This is a complete formula for the off-diagonal entries, not an assumption of diagonal dominance or positivity. It evaluates the first-moment matrix without an infinite prime sum once the inherited explicit-formula identity is used. It does **not** make the matrix positive or bound its degree growth by inspection.

For example, a hypothetical conjugate pair `a+ib,a-ib` contributes to (3.5)

\[
 \frac{2((t-a)^2-b^2)}{((t-a)^2+b^2)^2},
 \tag{3.8}
\]

which is negative for `|t-a|<|b|`. Other zeros may compensate it; this is not a sign theorem about the full H. Under RH the zero contributions in (3.5) are nonnegative, giving `L_H>=0`. That conditional observation cannot be used as an unconditional supplier.

## 4. Why neither sign nor a degree rate follows just from radicality

**[ABSTRACT | PAPER; logical audit]** The equality `k[r]=0` fixes a complete cancellation at zero modulation. The first moment measures a derivative of a *different* family of quadratic forms, or equivalently an integral of forms on modulations that are no longer radical. Formula (3.1) identifies the unpaid information rather than discarding it.

Two distinctions matter:

* The matrix in derivative coordinates can have very large entries simply because `||h^(2i)||` is large. A normalized bound must use `G_K`.
* S1 gave an upper majorant `D_K=exp(4K log K+O(K))`; it did not prove that the actual source moment grows at that rate. Conversely, lack of a sharp rate in S1 does not prove a polynomial rate.

No claim is made here that the polynomial bound requested by the owner is false. Its proposed justification is invalid; the actual rate remains an analytic question. The next section gives a strictly more specific source reduction than the old `T3` error bound.

## 5. A new one-sided source estimate without the first-moment T3 bound

### Theorem 5. Only a weighted polynomial differentiation price is needed for this part

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER; literal source]** Let

\[
 \mu_K=\sup_{0\ne P\in\mathbb R[t^2],\ \deg P\le2K-2}
 \frac{\int (P')^2H^2\,dt}{\int w P^2H^2\,dt}.
 \tag{5.1}
\]

It is finite for every K; `mu_1=0`. Define the explicit fixed near constant

\[
 C_{s_0}^{(1)}=2\sum_{2\le n\le e^{s_0}}
       \frac{\Lambda(n)\log n}{\sqrt n}
       +2\int_0^{s_0}s e^{s/2}ds.
\]

Then (0.2) holds for every r in `R_K`.

**Proof.** Integration by parts and completion of the square give the exact identity

\[
 \int P^2\mathcal L_H
 =2\int\left(PH'+\tfrac12P'H\right)^2
        -\tfrac12\int(P'H)^2.
 \tag{5.2}
\]

The omitted total derivative is precisely `(P² H H')'`, whose integral is zero. Thus (3.1) yields

\[
 M_r^{\rm full}\ge
 -\frac1{2\pi}\int(P'H)^2-J_r
 \ge-(\mu_K+18/25)\mathscr G[r].
\]

Subtract the near moment using `|M_near|<=C_s0^(1)||r||²`. This proves (0.2). Only an auxiliary near error and the bounded archimedean correction were estimated in absolute value; no full norm of Z or modulus of the full target was introduced. ∎

The differentiation Gram matrix has an entirely physical formula:

\[
 (D_K^{\rm der})_{ij}=
 \begin{cases}
 4ij(-1)^{i+j}\|h^{(i+j-1)}\|_2^2,& i,j\ge1,\\
 0,&i=0\text{ or }j=0,
 \end{cases}
\]
\[
 \boxed{\mu_K=\lambda_{\max}(G_K^{-1/2}D_K^{\rm der}G_K^{-1/2}).}
 \tag{5.3}
\]

This is a fixed explicit weight and a finite generalized eigenvalue. No uncontrolled inverse eigenvalue of the CCM bottom occurs.

### Conditional degree repair — precise, not claimed supplied

**[COFINAL_FAMILY | CONDITIONAL]** Suppose a new theorem proves

\[
 \mu_K\le C K^2\quad\text{for every }K,
 \tag{5.4}
\]

with one constant C. Since `beta_M<=1/log M`, (0.2) bounds the adverse first-log correction uniformly for `K<=c sqrt(log M)`. The remaining S1 error satisfies

\[
 t_M D_K=\exp[-\tfrac52\log M+O(\sqrt{\log M}\log\log M)]\longrightarrow0
\]

on that scale. The Fourier return factors from S1 §6 are also small: their coefficient prices are `exp(O(K log K))=M^{o(1)}`, whereas their return factors have fixed negative powers of m. Thus (5.4) would repair the **first** quantitative lock at the stated degree, without demanding a two-sided moment norm bound.

**(5.4) is not proved here.** It is a weighted Markov-type inequality for the specific measure `H(t)^2dt` against `wH²dt`, including its infinitely many real zeros. Standard inequalities for a different positive weight cannot simply be substituted.

Even under (5.4), `K` of order `sqrt(log M)` is only consistent with the necessary concentration threshold in S1. It is not a theorem of sufficient localization, does not pay all frequencies, and does not eliminate the negative outside contribution.

## 6. Exact means do not bound the Jordan negative part

### Lemma 6. A fixed signed mean is a difference, not two separate bounds

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]** For any positive weight p and real B,

\[
 \int pB=c\quad\Longleftrightarrow\quad
 \int pB_+-\int pB_-=c.
 \tag{6.1}
\]

This does not bound either term individually. In particular it does not imply that `p_h(t)B(t)` is nonnegative or that its negative mass is small. The density `p_h` itself is nonnegative by definition; the *symbol* multiplying it may have either sign.

A counterexample using the **actual theta background** is immediate. Choose `a>s0` and then `b>a` with `0<Q_h(b)<Q_h(a)`. Such b exists because h is strictly positive and Q_h tends to zero. Put

\[
 c=Q_h(b)/Q_h(a)\in(0,1),\qquad
 D(t)=\cos(bt)-c\cos(at).
\]

Then, exactly,

\[
 \boxed{\int p_h(t)D(t)dt=0,\qquad D(0)=1-c>0.}
 \tag{6.2}
\]

The continuous bounded D must be negative on an open set: otherwise its integral against the positive-a.e. density p_h would be positive. Multiplication by any A>0 preserves the mean and makes both the positive peak and the negative weighted mass arbitrarily large. This is a **synthetic symbol tested against the real theta density**, not a different theta kernel or a claimed CCM counterexample.

Adding such a null perturbation to a symbol preserves its background mean exactly, including any prescribed constant on the right. So replacing a one-sided mean inequality by an exact equality does not repair the alleged inference.

### Lemma 7. All finite-jet cross means and first moments can be preserved together

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER; SYNTHETIC SOURCE PERTURBATION]** Fix K, a finite scale-average with minimum logarithmic scale `ell>s0`, and a target t0. There is a smooth signed perturbation of the source supported strictly in `(s0,ell)` such that:

1. every quadratic and mixed mean for the full finite jet `R_K` is unchanged;
2. every first-log moment for the same jet is unchanged;
3. the near source and all late tail remainders for that jet are unchanged;
4. the average symbol at t0 increases strictly, and can be scaled arbitrarily.

**Construction and proof.** Choose an interval `J` with closure inside `(s0,ell)` and a nonnegative smooth bump `eta` supported on its closure, positive in its interior. Set

\[
 f_n(s)=Q_h^{(2n)}(s),\quad 0\le n\le2K-2,
\]
\[
 \mathcal V_K=\operatorname{span}\{f_n,sf_n:0\le n\le2K-2\}
 \subset L^2(J,\eta(s)ds).
\]

No independence assumption is needed; use the orthogonal projection onto the actual span. Below the minimum scale, the exact averaged filter is `q(s)=1-beta s`. Define

\[
 g(s)=(1-\beta s)\cos(t_0s),\quad
 v=\Pi_{\mathcal V_K}g,\quad
 b(s)=\eta(s)(g(s)-v(s)).
 \tag{6.3}
\]

The residual is nonzero. Indeed Q_h and all its fixed derivatives are real analytic and decay faster than every exponential along the real axis. If g equalled a finite combination of `f_n,sf_n` on J, analytic continuation along the real axis would make the equality global; its right side would decay at infinity while its left side would not. This is impossible.

Consequently

\[
 \int b(s)f_n(s)ds=\int s b(s)f_n(s)ds=0,
 \qquad
 \int b(s)g(s)ds=\|g-v\|_{L^2(\eta)}^2>0.
 \tag{6.4}
\]

Perturb the source by `dnu -> dnu + A b(s)ds`. The change in the symbol average is

\[
 \Delta\overline B(t)=2A\int_J(1-\beta s)b(s)\cos(ts)ds.
 \tag{6.5}
\]

For every r in R_K, `Q_r` is a linear combination of `f_n`, including all cross terms. Both its zeroth and first source moments therefore vanish against b. This proves the exact mean and M preservation. Since J lies below every scale and above s0, neither near terms nor tails change. Finally

\[
 \boxed{\Delta\overline B(t_0)=2A\|g-v\|_{L^2(\eta)}^2>0.}
 \tag{6.6}
\]

The perturbation symbol is even, real, smooth and band-limited to the same permitted source band, with no artificial frequency-zero atom. Because its h-mean is zero, its negative h-weighted mass is nonzero and scales linearly with A. ∎

**Exact scope.** This perturbation changes the arithmetic measure: it is not the literal prime comb minus the fixed continuum, and it does not preserve the entire infinite theta radical. It refutes only the proposed inference from the available **finite** exact equalities, even with cross moments and M retained. It does not refute a source-specific sign theorem. No K-uniform estimate for the amplitudes of this perturbation inside every prior numerical envelope is asserted.

This is stronger than the old SCALEJET negative-baseline example: its equalities are exact and it does not add a source atom at zero. Arithmetic rigidity beyond these equalities would have to exclude it.

### A closed-form replayable finite-jet example

**[ABSTRACT | PAPER; Gaussian control, not CCM]** For `p(t)=exp(-t²)/sqrt(pi)`, set `N=2K-1` and

\[
 D_K(t)=\sum_{j=0}^{N}(-1)^{N+j}\binom Nj e^{(j+1)/4}
                  \cos(\sqrt{j+1}\,t).
 \tag{6.7}
\]

Then

\[
 \int t^{2l}p(t)D_K(t)dt=0\quad(0\le l\le2K-2),
 \qquad D_K(0)=e^{1/4}(e^{1/4}-1)^N>0.
 \tag{6.8}
\]

To prove this, the Gaussian cosine moment equals `exp(-(j+1)/4)` times a polynomial in j of degree l. The Nth finite difference annihilates it for l<N. Thus every quadratic mean of `P(t²)` with degree in `t²` below K, and every cross mean, is exactly preserved. The executable code checks K=1,...,5 with exact algebra; the finite-difference proof covers every K. Scaling D_K produces arbitrarily deep negative compensation with all those exact means zero.

## 7. What would actually close the two steps

**[COFINAL_FAMILY | CONDITIONAL; no supplier asserted]** For the first step, the weakest useful new output in this representation is not `||M_K||` but an upper price for `gamma_K^-`, for example from (5.4). This would control `-beta M` on a larger growing jet, with the source tail and carrier return still handled separately.

For the second step, writing the exact mean does not improve the identity

\[
 F_M(t_0)\le D_M\delta+
 \frac{\int F_M\,d\sigma_r+\int_{I^c}(-F_M)_+\,d\sigma_r}{\sigma_r(I)}.
 \tag{7.1}
\]

The first integral is now known more precisely; the second is a different functional. Knowing a signed linear functional does not determine its Jordan negative part. To use a background h, one would need an independent source bound on its positive or negative part and a paid comparison of the localized density with the background. `p_r/p_h=P(t)^2` is generally unbounded on the whole line; it is not a uniformly dominated detector.

The two legitimate candidate representations are:

| Route | Concrete deciding test | Kill-power / cost |
|---|---|---|
| Signed first-moment via (3.7), (5.3) | Prove a degree bound for the actual polynomial differentiation Gram or directly for its adverse Laguerre form, with the real H weight | High for lock 1 / medium finite diagnosis, high all-K proof |
| Exact dual majorant in the frequency variable | Construct a source-derived upper majorant, or a detector-plus-background comparison paying the outside negative part, that fails the finite-moment null perturbation in Lemma 7 for an identified arithmetic reason | High for final upper bound / high analytic cost |

Neither route is mandated as the only possible RH route. Source-preserving direct prime/continuum estimates remain allowed. No universal operator-norm estimate for the full Z is requested.

### Exact remaining assertions

- `mu_K <= C K²` (or a weaker detector-specific adverse first-moment estimate sufficient at the chosen resolution) is unpaid.
- A sufficient source upper bound on the actual outside negative contribution in (7.1) is unpaid.
- A proof of useful concentration at the required width and all-height coverage is unpaid; the necessary order threshold in SCALEJET is not a sufficient theorem.
- Therefore the cofinal upper `bar B_M <= C w`, and RH, are not established.

## 8. Computation: what was executed and what it proves

### 8.1 Exact replay

SCALEJET Appendix A was extracted without changes. Its SHA256 was exactly

`413c12c2de43567f67a357eef79dc9dada96ca28699c2e6d3f229a3b813e47de`.

All eight previous groups passed. Seven new groups also passed: dilation, the full total derivative in (5.2), polynomial-factor Laguerre algebra, the physical Hankel coefficient, all finite-jet Gaussian equalities, the parameter-derivative negative control, and the off-real-pair curvature sign.

The first new script attempted structural equality of a SymPy derivative with an unevaluated `Subs` object and failed. Applying `.doit()` and comparing the simplified difference fixed that representation issue. The mathematical identity was not changed. The final script was rerun successfully.

### 8.2 Literal-source floating diagnostic, K=3

The diagnostic evaluates `r=h,h'',h^(4)` using the actual theta summands. It compares two independently coded formulas, not two independent reviewers:

1. direct first-log prime sum minus the continuum, plus the archimedean J;
2. the physical derivative expression (3.6).

Finite settings: six theta summands, primes/powers through 40, continuous s integration through 3.5, physical quadrature halfwidth 3 about the correlation midpoint. **No complete tail or roundoff enclosure is supplied for these settings.** These are diagnostic numbers, not certified signs.

For full moments the approximate matrix is

\[
 \mathbb M_3^{\rm full}\approx
 \begin{pmatrix}
 -0.901290281&-1.216515919&134.289432812\\
 -1.216515919&134.289432812&-9555.771379288\\
 134.289432812&-9555.771379288&837151.414958573
 \end{pmatrix}.
\]

For `s0=log 2`, the generalized eigenvalues of `(M_far,G)` were approximately

\[
 -0.1834347534,\quad -0.0605426580,\quad 0.1298278864.
\]

The polynomial-derivative price at K=3 was approximately `mu_3=0.2053658172`. The maximum relative discrepancy between the two moment formulas, normalized by `max(1,|rhs|)`, was below `3e-13` in these six entries.

These observations suggest that the small matrix is genuinely signed and that raw coordinate magnitudes are not the normalized cost. They do **not** prove a sign for an exact finite matrix, a polynomial K rate, or any cofinal assertion. The proof of (3.1) is analytic and does not rely on these numbers.

### 8.3 Reproduction

The standalone script is `PROSHKA_HARDBREAK_CHECKS_2026-10-31.py`. Its default mode runs only exact algebra. `--diagnostic` additionally runs the deliberately non-certified floating probe.

```bash
uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py
uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py --diagnostic --output hardbreak_probe.json
```

`hardbreak_probe.json` is the output path in the current directory; replace it with a chosen path such as `/tmp/hardbreak_probe.json`. `K=3`, the cutoffs, and their diagnostic status are explicit in the code. The local run used the installed Python environment; no Lean or Arb run occurred.

## 9. Strongest attack and dependency epistemics

**Attack on the new identity:** moving a zero-side contour might cross poles or lose multiplicity. Answer: in (3.4) each denominator is canceled by the same zero of R, multiplicity remains in the outer sum, and (3.3) supplies summable absolute bounds. The order-one factorization is essential; a quadratic exponential factor for an order-two toy H would add a nonzero correction. The theorem is for the actual xi H, not arbitrary entire functions.

**Attack on the negative control:** it changes the primes. Correct. It only kills the claimed *logical inference* from finite exact means, not the literal source upper bound. Its role is to demand a stated arithmetic premise where the proof distinguishes the actual comb from a moment-invisible perturbation.

**Attack on the proposed degree repair:** defining mu_K merely renames the problem. The new inequality (0.2) is an actual one-sided consequence of the source and a positive square, with all constants. It does not itself supply the missing all-K estimate. We count the change as a useful representation and supplier reduction, not a completed cofinal upper bound.

**[ABSTRACT | PAPER; dependency ledger]**

- DOWNSTREAM_CONSUMER: SCALEBRIDGE averaged-symbol criterion on the literal CCM family, with its inherited PAPER premises.
- ACTUAL_CONSUMER_REQUIREMENT: one source-derived uniform upper bound for the complete averaged symbol or a sufficient quadratic version.
- ORIGINAL_REQUESTED_OBJECT: polynomial normalized first-moment growth plus exclusion of negative leakage from exact means.
- ORIGINAL_OBJECT_IS: UNKNOWN as a necessary package; it is not mandatory for every route to RH.
- KNOWN_WEAKER_INTERFACES: control only the adverse moment sign as in (0.2); direct source upper bounds may bypass jets.
- FAILURE_TYPE: NO_DERIVATION for the all-K source price; COUNTEREXAMPLE for exact-finite-means-imply-no-negative-leakage.
- EPISTEMIC_STATUS: RESEARCH_DEBT for the actual arithmetic bounds; MATHEMATICALLY_DEAD only for the finite-mean logical inference at its exact stated scope.
- KILL_SCOPE: THEOREM_SHAPE, not ROUTE_FAMILY.
- KILL_EVIDENCE_KIND: exact mean-null finite-jet perturbation, Lemmas 6–7; exact replayable special case (6.7)–(6.8).
- NOVELTY_AXIS: LITERAL_FIRST_LOG_MOMENT_TO_LAGUERRE_DENSITY_AND_ADVERSE_DERIVATIVE_GRAM.
- REOPEN_TRIGGER: a genuine weighted derivative/sign estimate and a source-specific outside-leakage comparison, not a declaration that cancellation implies either.
- DISCRIMINATOR: does the additional argument use an arithmetic property absent from Lemma 7, and does its K/height cost survive the desired cofinal schedule?

## 10. Predictions, closeout, and one next directive

Predictions P1–P5 were registered before the new symbolic and numerical checks. P1 (dilation gives Q-prime) and P2 (exact finite means do not control negative mass) are confirmed by proofs and exact controls. P3 (the modulation response is not radical) is confirmed at the formula level. P4 (the proposed Laguerre representation) survived the complete derivation and the direct floating factor check; it has not received an independent mathematical audit. P5 (no numerical cofinal promotion) was maintained.

What became smaller: the adverse first-moment supplier no longer has to be paid through the full `T3²` majorant. What was killed: only the assertion that exact finite theta means forbid large signed compensation. What must not recur: differentiating a zero value as if it were an identity in the new parameter; treating a signed mean as a bound on total variation; confusing a necessary concentration threshold with sufficiency.

**CODEX DIRECTIVE — read-only audit and degree test for the actual first-moment supplier.**

Independently audit (2.2), (3.1)–(3.7), and (5.2), specifically the complex modulation with both poles, the contour shift through removable zeros, the absolute zero-sum exchanges, and the normalization by `2pi`. Then address exactly the weighted inequality (5.4), or an explicitly weaker adverse-moment estimate on the concentration optimizer, with the real H and energy Gram. A finite generalized-eigenvalue calculation is a falsifier/calibration only. Do not import a Markov inequality for a different weight and do not claim that exact means pay the outside negative part. Return `SIGNED_FIRST_MOMENT_DEGREE_BOUND` only with a cofinal proof and paid constants, otherwise the first exact missing estimate or an actual counterexample. No repository writes, state promotion, or RH claim are authorized by this local research directive.

Strategy memory:
```yaml
iteration:
  target: double_lock_from_exact_radicality_and_exact_means
  status: PARTIAL
  failed_strategy: exact_signed_mean_excludes_negative_compensation
  cognitive_operator_used: DUALIZE
  new_gap_name: actual_theta_weighted_derivative_price_and_signed_detector_leakage
  invariant_learned: first_log_moment_is_a_modulation_response_not_a_dilation_value
  forbidden_future_move: infer_positive_and_negative_mass_bounds_from_their_difference
  next_decisive_test: independent_Laguerre_crosswalk_audit_then_weighted_K_squared_estimate
```

## 11. External source locators

```text
https://people.math.harvard.edu/~elkies/M259.02/zeta2.pdf
https://people.math.harvard.edu/~elkies/M259.02/prod.pdf
https://dlmf.nist.gov/25.4
https://dlmf.nist.gov/25.10
https://doi.org/10.1007/BF02142328
```

The Laguerre expression is standard; no novelty priority claim is made for it. The source-specific first-log-moment crosswalk is the derivation in this document. No new zero-free region or disputed recent theorem is used.

**Final state: the two proposed automatic implications do not close the argument. The literal one-sided source target and RH remain unproved here.**

## Appendix A. Complete executable code

```python
#!/usr/bin/env python3
"""Exact checks and an optional literal-source FLOATING diagnostic.

Run:
  uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py
  uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py --diagnostic --output hardbreak_probe.json

The exact tests check algebra, not RH. The diagnostic has UNPAID quadrature,
truncation, and floating errors; its numbers are NOT interval certificates.
--output is the JSON path to create; e.g. hardbreak_probe.json in the current directory.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    x,a=s.symbols('x a',real=True)
    Q=s.Function('Q'); H=s.Function('H')(x); P=s.Function('P')(x)
    assert s.simplify(s.diff(Q(a*x),a).subs(a,1).doit()-x*s.diff(Q(x),x))==0
    print('PASS dilation: s Q-prime, not s Q')
    LH=s.diff(H,x)**2-H*s.diff(H,x,2)
    complete=2*(P*s.diff(H,x)+s.diff(P,x)*H/2)**2-(s.diff(P,x)*H)**2/2
    assert s.simplify(P**2*LH-complete+s.diff(P**2*H*s.diff(H,x),x))==0
    print('PASS square completion with full total derivative')
    R=P*H; LR=s.diff(R,x)**2-R*s.diff(R,x,2)
    assert s.simplify(LR-P**2*LH-(s.diff(P,x)**2-P*s.diff(P,x,2))*H**2)==0
    print('PASS polynomial-factor Laguerre identity')
    n=s.symbols('n',integer=True,nonnegative=True)
    assert s.expand(4*(n*n-n)-2*n*(2*n-1))==-2*n
    print('PASS physical Hankel coefficient')
    # Gaussian equality-null symbols: exact ALL cross moments, not just diagonals.
    for K in range(1,6):
        order=2*K-1
        for ell in range(2*K-1):
            total=s.Integer(0)
            for j in range(order+1):
                hv=s.expand(s.hermite(2*ell,s.sqrt(1+j)/2))
                total+=(-1)**(order+j)*s.binomial(order,j)*(-1)**ell*hv/s.Integer(2)**(2*ell)
            assert s.simplify(total)==0
        y=s.symbols('y',real=True)
        peak=sum((-1)**(order+j)*s.binomial(order,j)*y**j for j in range(order+1))
        assert s.expand(peak-(y-1)**order)==0
    print('PASS all finite-jet equalities K=1..5 and strictly positive peak')
    eps,N=s.symbols('eps N',positive=True)
    A=s.diag(eps*s.exp(N),-eps*s.exp(2*N))
    assert A.subs(eps,0)==s.zeros(2)
    assert s.diff(A,eps).subs(eps,0)==s.diag(s.exp(N),-s.exp(2*N))
    print('PASS zero at one parameter does not fix the signed derivative')
    u,b=s.symbols('u b',real=True,nonzero=True)
    pair=1/(u-s.I*b)**2+1/(u+s.I*b)**2
    assert s.simplify(pair-2*(u*u-b*b)/(u*u+b*b)**2)==0
    print('PASS off-real zero-pair curvature sign')
    print('ALL 7 EXACT GROUPS PASSED')


def diagnostic() -> dict:
    import numpy as np
    from numpy.polynomial import Polynomial
    from scipy.integrate import quad
    from scipy.linalg import eigvalsh
    import scipy, sympy

    K=3  # h, h'', h^(4); no growing-K or CCM-bottom inference.
    theta_terms=6
    prime_cutoff=40
    s_cutoff=3.5
    physical_halfwidth=3.0
    p=[Polynomial([0.,-24.,16.])]
    for _ in range(2*(K-1)):
        q=p[-1]
        p.append(.5*q+Polynomial([0.,2.])*q.deriv()-Polynomial([0.,2.])*q)
    ns=np.arange(1,theta_terms+1,dtype=float)
    def hd(x: float,k: int=0) -> float:
        v=abs(float(x)); y=math.pi*ns*ns*math.exp(2*v)
        out=math.exp(v/2)*float(np.sum(p[k](y)*np.exp(-y)))
        return -out if x<0 and k%2 else out
    def integral(fun,a,b):
        return quad(fun,a,b,epsabs=1e-9,epsrel=2e-11,limit=140)[0]
    def corr(s,i,j):
        mid=-s/2
        return 2*integral(lambda x:hd(x,2*i)*hd(x+s,2*j),
                          mid-physical_halfwidth,mid+physical_halfwidth)
    def vm(n: int) -> float:
        for q in range(2,n+1):
            if n%q==0:
                z=n
                while z%q==0: z//=q
                return math.log(q) if z==1 else 0.
        return 0.
    atoms=[(n,vm(n)) for n in range(2,prime_cutoff+1) if vm(n)]
    M=np.zeros((K,K)); J=np.zeros_like(M); G=np.zeros_like(M)
    near=np.zeros_like(M); D=np.zeros_like(M); entries=[]
    s0=math.log(2); total=K*(K+1)//2; done=0; start=time.monotonic()
    for i in range(K):
        for j in range(i,K):
            q=lambda s:corr(s,i,j)
            primes=sum(v*math.log(n)/math.sqrt(n)*q(math.log(n)) for n,v in atoms)
            continuum=integral(lambda s:s*math.exp(s/2)*q(s),0,s_cutoff)
            jterm=integral(lambda s:(.5 if s==0 else s*math.exp(-2.5*s)/(-math.expm1(-2*s)))*q(s),0,s_cutoff)
            n=i+j
            rhs=(-1.)**n*(4*integral(lambda x:x*x*hd(x,n)**2,-physical_halfwidth,physical_halfwidth)
                -(2*n*integral(lambda x:hd(x,n-1)**2,-physical_halfwidth,physical_halfwidth) if n else 0.))
            M[i,j]=M[j,i]=primes-continuum; J[i,j]=J[j,i]=jterm
            near[i,j]=near[j,i]=math.log(2)*s0/math.sqrt(2)*q(s0)-integral(lambda s:s*math.exp(s/2)*q(s),0,s0)
            ip=integral(lambda x:hd(x,2*i)*hd(x,2*j),-physical_halfwidth,physical_halfwidth)
            # The tiny s interval and all truncations are diagnostic approximations.
            energy=integral(lambda s:math.exp(-2.5*s)/(-math.expm1(-2*s))*(2*ip-q(s)) if s>1e-7 else 0.,0,s_cutoff)
            jt=sum(math.exp(-(2*k+2.5)*s_cutoff)/(2*k+2.5) for k in range(15))
            G[i,j]=G[j,i]=ip+energy+2*ip*jt
            if i and j:
                D[i,j]=D[j,i]=4*i*j*(-1.)**(i+j)*integral(lambda x:hd(x,i+j-1)**2,-physical_halfwidth,physical_halfwidth)
            relative=abs(M[i,j]+jterm-rhs)/max(1.,abs(rhs))
            entries.append(dict(i=i,j=j,M_full=float(M[i,j]),J=float(jterm),physical_rhs=float(rhs),relative_difference=float(relative)))
            done+=1; elapsed=time.monotonic()-start; eta=elapsed*(total-done)/done
            filled=20*done//total
            print('['+'#'*filled+'-'*(20-filled)+f'] {done}/{total} ETA {eta:.1f}s',flush=True)
    far=M-near
    return dict(status='FLOATING_DIAGNOSTIC_NOT_CERTIFICATE',K=K,
        theta_terms=theta_terms,prime_cutoff=prime_cutoff,continuum_cutoff=s_cutoff,
        physical_halfwidth=physical_halfwidth,s0=s0,entries=entries,
        M_full=M.tolist(),M_far=far.tolist(),G=G.tolist(),polynomial_derivative_Gram=D.tolist(),
        normalized_full_eigenvalues=eigvalsh(M,G).tolist(),
        normalized_far_eigenvalues=eigvalsh(far,G).tolist(),
        mu_K=float(eigvalsh(D,G)[-1]),
        versions=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=sympy.__version__))


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diagnostic',action='store_true',help='also run the non-certified K=3 literal-source probe')
    parser.add_argument('--output',type=Path,default=Path('hardbreak_probe.json'),help='diagnostic JSON destination')
    args=parser.parse_args()
    exact_checks()
    if args.diagnostic:
        data=diagnostic()
        args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(data,indent=2))
        print(f'WROTE {args.output}')


if __name__=='__main__':
    main()
```

## Appendix B. Execution hashes

```json
{
  "PROSHKA_HARDBREAK_CHECKS_2026-10-31.py": "6d77404d1fc623680acadab2b4ec9cb3d364c0ea4b6dfa4c37a71970ea8c8c1a",
  "predictions.txt": "cccd70a738f696a036aa550e434f620839f7d674d40760b02ae56a916dfc2d8d",
  "final_probe.json": "b84225d10df4f78ab0de623d991507199347e33bbacece8c32f79d3629b195d9",
  "final_stdout.txt": "1a25542e9a47649d4c64dde900e405e3ddb10d15a3b319621d64f1569e9994fe",
  "scalejet_replay_stdout.txt": "fbd5f38d0eb31cef07140825695dda292411e0d93ee77055447a53dc6992e0d4"
}
```
