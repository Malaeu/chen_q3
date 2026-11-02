# Moving-kappa quiet-space residual: independent PAPER audit

```yaml
STATUS: PAPER_AUDIT_ACCEPTED
DATE: 2026-11-02
SOURCE_BRANCH: proshka_inbox_2026-10-31
SOURCE_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md
SOURCE_GIT_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_SHA256: fb0176935d103209bea3feff8362605024da7635c568768dc5355f441e5ddd14
SOURCE_LINES: 615
REVIEW_CLASS: ADVERSARIAL_READ_ONLY
REVIEWER: Codex root, independent of the Proshka source author
SCOPE: COFINAL_FAMILY_PAPER_SECTIONS_1_THROUGH_5
ITEM_1_RANK: CONFIRMED
ITEM_2_THETA_D: CONFIRMED
ITEM_3_GONEK_AND_K: CONFIRMED
ITEM_4_FULL_OPERATOR_AND_GRAM: CONFIRMED
SOURCE_EDITED: false
NEW_EIGENPROBLEMS: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
NUMERICAL_ONSET_EXTRACTED: false
SIGNED_UPPER_COUNT_PROVED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
PX_RH_CLAIM: NOT_MADE
```

This is an independent read-only mathematical review of the pinned source, followed by delivery of this review as requested by the owner. No source verdict, Lean declaration, route status, or admission registry is changed. Acceptance is bounded PAPER acceptance of the stated rank/residual supplier, not kernel verification or a conclusion about the signed upper count.

Line references below are 1-based lines in the exact source blob above.

| Requested item | Verdict | Source locations |
|---|---|---|
| 1. Dimension lower bound and Bellotti–Wong rank estimate | **CONFIRMED** | lines 96–145; (1.1)–(1.5) |
| 2. Uniform theta,D and exact identity | **CONFIRMED** | lines 194–284; especially 253–273 |
| 3. Unconditional Gonek at both endpoints, multiplicities, b_m,k_m | **CONFIRMED** | lines 291–399; (3.1)–(3.9) |
| 4. Full-operator residual, arbitrary g, relative Gram inequality | **CONFIRMED** | lines 403–547; (4.1)–(5.3) |

No ERROR or unresolved GAP was found in these four scoped claims. The following records the independent derivations and endpoint checks.

## 1. Dimension and rank — CONFIRMED

Work over the complex even carrier of dimension m+1. For a lower-half-plane zero rho, the functional equation sends rho to 1-rho in the upper half-plane. Their spectral arguments are negatives, so evenness makes the corresponding value rows identical. Upper-half-plane zeros may still give dependent or automatic rows; that only improves the lower bound. Counting them with multiplicity overestimates the rank. Thus rank-nullity gives

    dim J_m >= m+1-N(T).

The strict cutoff in J_m versus the inclusive definition of N(T) is safe in this direction. No simplicity assumption, equality of rank with N(T), or derivative constraint at a multiple zero is used.

Theorem 1.1 of Bellotti–Wong v2 gives an error bounded by
0.10076 log t + 0.24460 log log t + 8.08344 for t>=e.
Writing y=log t>=1 and using log y<=y shows this is below log t+10. The weaker error E(t) used in the source therefore follows for its entire stated range.

Since log(T/(2 pi e))=L-h+log(1+epsilon), the expansion (1.3) is exact. With epsilon=ch/L and L>=16:

    c h^2/L^2 - (1+epsilon)log(1+epsilon)/L
      >= (ch/L^2)(h-1-epsilon) >= 0.

Here h-1=log L and epsilon<=h/L<=log L. Also T<=2 Omega<=m. Consequently 1-E(T)>=1-L-10>=-2L, proving (1.4). Condition (1-c)mh>=4L^2 yields (0.3). For each fixed 0<c<1 this condition eventually holds on the full integer sequence.

Primary source: [Bellotti–Wong, Theorem 1.1, p.1](https://arxiv.org/pdf/2412.15470v2), read directly. Its global bound includes endpoint heights; left limits used later follow by continuity of M and E.

## 2. Disk geometry and shrinking-gap constants — CONFIRMED

The cosine Fourier formula and the substitution z^2/Omega^2=(1+w)^2/(4w) reproduce (2.2). Each denominator in (2.1) factors with both roots on the unit circle; the double roots at the endpoint modes do not invalidate the bound by (1-r)^(-2). The coefficient l1 bound is sqrt(2m+1)||f||.

For the inverse Joukowski branch, |eta|<1 and Re(z/Omega)>=s imply
(|eta|+|eta|^(-1))/2>=s. Monotonicity on (0,1) gives (2.4), also for complex arguments.

For an upper zero use -z_rho=gamma-i(Re rho-1/2), which has positive real part. Evenness permits this sign change. Distinct upper zeros give distinct squared arguments and hence distinct w-nodes. Nonautomatic zeros in U<gamma<=V have no sinc zero and no modal pole; they really force F_f(w_j)=0. Dividing by their finite Blaschke product on the radius-R disk is therefore valid for every f in J_m. For |w|<=v, |a|<=u the maximum factor is R(u+v)/(R^2+uv), attained with opposite phases. This proves (2.7).

The exact subtraction is

    1 - R(u+v)/(R^2+uv) = (R-u)(R-v)/(R^2+uv).

For 0<epsilon<=1, alpha<=4/3 and alpha+sqrt(alpha^2-1)<3, so

    1-u >= sqrt(epsilon)/2,
    1-R >= sqrt(epsilon)/4,
    1-v >= sqrt(epsilon)/2.

Since R-v>=R-u and R^2+uv<=2, 1-theta>=epsilon/32. Further, (1+v)^4<=16 and the product of the squared denominator factors is at least epsilon^2/64, giving D<=1024/epsilon^2. Finally -log theta>=1-theta. These are inequalities for the entire stated interval, not an extrapolation of fixed-kappa constants. The leading orders (2.9) agree as well, but are not needed.

## 3. Zero band, Gonek, automatic rows, and multiplicity — CONFIRMED

M'(t)=log(t/(2 pi))/(2 pi), the width V-U=epsilon Omega/3, and U>=Omega yield the first lower bound (3.2); E(U)+E(V)<=4L. Since log L/L<=1/4 for L>=16, its second inequality follows. Under epsilon m>=48L, subtraction of 4L leaves at least epsilon m/6.

At any ordinate in (U,V], the total jump of N is at most 2E(gamma), by taking the two one-sided limits around that height. An individual zero's multiplicity is no larger than the total jump. Hence

    mult(rho) <= 2(log V+10) <= 4L.

This also handles several distinct zeros at the same height.

I visually checked Theorem 1 on printed p.92 of Gonek's primary PDF and its continuation on p.93. Its four error terms are exactly the four terms in source (3.5). This is the unconditional uniform theorem for x,Y>1; Theorem 2 on p.93 assumes RH and is not used. Uniformity permits one absolute C_G>=1 dominating the four implied constants, independent of c,epsilon,m,U,V.

Apply that theorem twice, at x=m and Y=U,V, and subtract. The main term is -(V-U)Lambda(m)/(2 pi)<=0. The bounds in line 349 are valid: log(2m)<=2L, log log(3m)<=h, log(2Y)<=2L, L min(Y,m/<m>)<=LY<=4 pi m<=mL, and the last minimum is <=log Y/L<=1. Their sum is <=6mLh. Thus Re S_m<=12C_G mLh. Both endpoint remainders are paid, and subtracting inclusive sums gives exactly U<gamma<=V, including a zero at V and excluding a zero at U.

For an automatic row, Re rho=1/2 and gamma L is a multiple of 2 pi, so m^rho=sqrt(m), with multiplicity. Every remaining term has real part >=-m. Therefore

    Re S_m >= sqrt(m)(n_m-b_m)-m b_m,

which gives (3.7), including its positive-part convention. Under (3.8),

    sqrt(m)n_m - Re S_m >= epsilon m^(3/2)/12,
    b_m >= epsilon sqrt(m)/24,
    k_m >= b_m/(4L) >= epsilon sqrt(m)/(96L).

These counts are of actual complex zeros, not a critical-line projection. No assumption excludes exact sinc resonance. The absolute C_G is not numerically extracted, so this proves an eventual cofinal assertion rather than a numerical onset at m=16,24,32,40.

Primary source: [Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1, pp.92–93](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf).

## 4. Full residual and relative Gram — CONFIRMED

The inherited source formula is CONFINE (1.4), with physical Fourier convention and all zeta zeros counted with multiplicity. I checked it against the unconditional Weil formula and polarization in [Connes–Consani–Moscovici v1, (3.2), (3.5)–(3.11), Proposition 3.2](https://arxiv.org/html/2511.22755v1#S3). In logarithmic physical coordinates it yields source (4.1), including the conjugated argument in the first factor. It is not an RH-based sum of absolute squares.

The extension to the two zero-extended finite cosine functions is justified at fixed m. They are compactly supported BV and bounded. A nonnegative smooth approximate identity preserves a uniform BV and sup-norm bound, keeps supports in a common compact, and has Fourier multiplier bounded by exp(eta/2) in |Im z|<=1/2. Integration by parts against the BV derivative gives O((1+|Re z|)^(-1)); the product in the zero sum is absolutely summable by N(t)=O(t log t). On the arithmetic side there are finitely many prime powers on the common support, convergent continuous correlations, convergent poles, and the uniform translation bound

    |2<g_eta,f_eta> - Q_{g_eta,f_eta}(s)|
        <= 2 ||g_eta||_infinity TV(f_eta) |s|.

It pays the O(1/s) archimedean kernel near zero. Thus smoothing and passing to the limit adds no endpoint term. This is a fixed-m extension, not a uniform asymptotic estimate in disguise.

For f in J_m, only |gamma|>=T remains. Equality at T is correctly retained. Parity handles both signs. Bound the f factor with (2.7), but bound the other factor for arbitrary g in V_m with (2.3). As |z_rho|>=|gamma|, their product is bounded by

    4 D (2m+1) sqrt(m)/(L gamma^2)
        * theta^k_m ||g|| ||f||.

Stieltjes integration gives
sum_(gamma>=T) gamma^(-2)
= -N(T^-)/T^2 + 2 integral_T^infinity N(t)/t^3 dt.
Dropping the nonpositive first term and inserting M+E gives
log(T/(2 pi))/(pi T)+(log T+21/2)/T^2, no larger than Z(T). Both signs of gamma supply the separate factor 2. This reproduces exactly (4.4), an estimate of ||A_m f||, not merely of the compression to J_m.

For every coefficient vector x and every exact basis synthesis B_m,

    ||A_m B_m x||^2 <= delta_m^2 ||B_m x||^2.

Self-adjointness of the original finite A_m gives
B_m^* A_m^2 B_m <= delta_m^2 G_m. Since B_m has independent columns, G_m>0; conjugation by G_m^(-1/2) proves (4.7). There is no columnwise-to-operator inference and no unbudgeted smallest-Gram-eigenvalue loss. The interpolation coefficient/Gram formulas (4.8) also agree with partial fractions; distinct active squared nodes, including removable modal evaluations, are what must be imposed.

Finally Z(T)<=2(log T+1)/T, log T+1<=2L, and 2m+1<=3m give 48D sqrt(m)L/(pi kappa). Substituting the verified D bound and theta^k_m<=exp(-epsilon k_m/32) gives (5.1) and the exact constants in (0.4). Its exponent dominates every fixed multiple of log m for fixed 0<c<1. All four conditions (5.2) eventually hold, proving the claimed o(m^(-B)) full residual together with positive growing rank on the same J_m.

## Reproducibility and boundary

The source bytes were independently hashed to the blob and SHA-256 in the header. Two exact symbolic checks were executed: the theta factorization and the rank main-term expansion. The interval-wide inequalities and analytic passages above were checked by derivation, not by the author's reported 160 parameter samples. No new eigenproblem, spectral scan, Lean run, paid call, or interval computation was used.

Primary PDF byte hashes independently downloaded in this audit:

- Gonek: SHA-256 7c68870fc4fe095115ddb1279b3fa8fa718f31e6ea350e3e29168ec91bd787a4.
- Bellotti–Wong v2: SHA-256 9299073e0fbb836ca744790e5ac2c03a496df3194409aaa87832ba6161ead3b5.

Pinned repository normalization suppliers were read at a412a678a4ae1df4f03106d1a46cf5453451c65a:

- CONFINE, blob 1879347b72d1aa55cf506f5387de37059f929122: physical convention, arithmetic form and unconditional (1.4).
- NOESCAPE, blob 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc: original finite even carrier and matrix convention.

The cofinal rank and full residual supplier passes this bounded independent PAPER audit. The signed upper spectral count required by NOESCAPE L12/L13 remains unproved. The audit does not establish saturation, a lower floor, T, or RH, and does not automatically admit a Lean or registry consumer.
