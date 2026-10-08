# Restricted prime-operator receiver on the same full CCM family

2026-10-08. Root derivation and independent read-only ccm_window_transport PASS on the complete written theorem, including inherited E return, finite Gram correction and exact source cancellation. Conditional adverse alternative only. No off-critical zero is asserted. No prime spectral bound, SP or RH is proved. Not sent while Q6 is pending.

## Objects and theorem

Keep the original full carrier j=-m,...,m, L=log m, d=2m+1 and literal K_m. Let phi_j(t)=L^(-1/2) exp(2pi i j t/L) on [0,L]. Let v_± be the finite Fourier coefficients of exp(±t/2), b=ones/sqrt(d), and P_m the orthogonal projection onto span{b,v_+,v_-}^perp. P_m depends only on m, not on a zero or moment order. This is a subspace of the same original family, not another production matrix or reindexing.

THEOREM (conditional restricted adverse alternative). If xi(1/2+w)=0 with w=delta+i gamma, delta>0, there are c_w>0 and m_0(w) such that on EVERY original cell m>=m_0(w),

    lambda_min(K_m restricted to ran P_m)
        <= -c_w m^delta/(log m)^(2delta).                       (1)

Constants may depend on the fixed zero, its multiplicity r and its normalization, but not on m. Thus a subpolynomial lower floor on this restricted space suffices for the RH receiver. Neither restricted nor full floor is proved here.

## Fixed-source filter

Use the accepted separators in NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md, sections Answer10 and Root refinement: M_(H_w)(w)=1, zero at every other distinct zeta zero, and double-exponential tails for every fixed derivative. The partner is wdagger=-conj(w). Mellin convention: M_f(z)=int_R f(t)exp(zt)dt.

Define separately for each partner

    Htilde_w=(partial²-1/4)H_w/(w²-1/4).

The denominator is nonzero because xi(0),xi(1) are nonzero. Integration by parts gives

    M_(Htilde_w)(z)=(z²-1/4)M_(H_w)(z)/(w²-1/4).               (2)

Its value at w stays1; all other zeta-zero values stay0; both moments at ±1/2 vanish. Normalize the partner by its own denominator. An unnormalized filter on the already-combined pair would not justify its sign.

For tau_h f(t)=f(t-h), set

    utilde_h=exp(-i h gamma)tau_h Htilde_w
              -exp(i h gamma)tau_(-h) Htilde_wdagger.

The two nonzero zero evaluations remain +exp(delta h),-exp(delta h). The accepted FULL signed zero formula, with multiplicity, gives

    W(utilde_h)=-2r exp(2delta h),    ||utilde_h||_2²<=D_w.       (3)

Translations preserve both zero Laplace moments. The filter is fixed on the source profiles, so their fixed derivative and double-exponential tail bounds persist. No fullband multiplier norm m² is spent.

## Cutoff and original Fourier projection

Put a=L/2, h=a-log L and use the SAME compact cutoff chi_a from the accepted refinement, zero near ±a, with uniformly bounded derivatives. Transitions are distance at least log L-1 from the translated profiles. Set f_a=chi_a utilde_h. The accepted weighted integrated-translation E estimate applies to these new fixed profiles:

    ||(1-chi_a)utilde_h||_E <= C_w exp(h)exp(-c_w L²),
    ||utilde_h||_E <= C_w exp(h).

The accepted form continuity inequality gives cutoff error <=C_w m exp(-c_w L²). Each fixed unweighted derivative L1 norm of f_a is uniformly bounded. Hence the SAME third-derivative Fourier projection estimate from that audit gives

    |W(F_m f_a)-W(f_a)| <= C_w m^(-1)L^(3/2).                 (4)

Only profile-dependent constants change. Both zero-extension jump strips remain paid; E has not been replaced by L2 continuity.

Translate f_a from [-a,a] to [0,L]; translation preserves W and derivative norms. Before cutoff the Laplace moments vanish; cutoff residuals are bounded by m^C exp(-c_w L²), by integration of the same tails with exp(±t/2). Let c be all Fourier coefficients, c_m their |j|<=m truncation. Vanishing near the endpoints allows three integrations by parts:

    |c_j|<=C_w L^(5/2)|j|^(-3) (j!=0),
    ||c_(|j|>m)||_2<=C_w L^(5/2)m^(-5/2).                    (5)

Since its endpoint value is zero and the Fourier series converges absolutely, sum_j c_j=0. Therefore

    |b*c_m|<=C_w L^(5/2)m^(-5/2).                             (6)

Coefficients use the original [0,L] convention of Q, with the same translated synthesis; no extra phase is dropped.

## Exact finite constraint correction

Set vhat_±=v_±/||v_±||. The explicit coefficients in CCM_CONTINUOUS_RANK_TWO_TEST.md imply

    ||v_+||²=m+O(L),   ||v_-||²=1+O(L/m),
    |vhat_+*vhat_-|=O(L/sqrt(m)),
    |b*vhat_±|=O(sqrt(L/m)).                                 (7)

Indeed the full exponential norms squared are m-1,1-1/m, and their Fourier tail norms squared are O(L),O(L/m). The full cross inner product is L; deleting tails changes it by O(L/sqrt(m)). The b overlaps follow by conjugate pairing of denominators: sum_(|j|<=m)(1/2)/(1/4+omega_j²)=O(L). Thus the Gram matrix of b,vhat_+,vhat_- tends to I and has least eigenvalue>=1/2 eventually.

The cutoff Laplace residual and Cauchy-Schwarz against the omitted Fourier tail give

    |vhat_±*c_m|<=C_w L^(5/2)m^(-5/2)+m^C exp(-c_w L²).       (8)

Division by ||v_+||~sqrt(m), respectively ||v_-||~1, cancels the corresponding full exponential norm; it is essential. Equations(6)–(8) and the Gram bound yield

    ||(I-P_m)c_m||<=C_w L^(5/2)m^(-5/2)+m^C exp(-c_w L²).     (9)

The accepted full envelope ||K_m||<=40sqrt(m)L and bounded ||c_m|| imply that replacing c_m by z_m=P_m c_m costs in the quadratic form at most

    C_w m^(-2)L^(7/2)+m^C exp(-c_w L²).                       (10)

This bounds correction of this PARTICULAR witness; it is not a small operator-norm return on all vectors. Combining(3),(4),(10) and cutoff error gives

    z_m*K_m z_m <= -2r m^delta L^(-2delta)+o(m^delta L^(-2delta)),
    ||z_m||²<=D_w.

Eventually the form is negative, so z_m!=0. Normalize and obtain(1). All errors vanish relative to the fixed-zero negative signal on every sufficiently late cell.

## Exact continuous cancellation on the restricted space

Let A_m=sum_(2<=n<=m) Lambda(n)/sqrt(n) Q(log n) be the FULL prime-power translation matrix, retaining Q(L)=0. The literal source is

    K=B-A_m+G_full-H_full,
    B=A_arch-c_A I+2H_full.

The continuous-kernel identity G_full+H_full=v_+v_-*+v_-v_+* gives EXACTLY

    P_m K_m P_m=P_m(A_arch-c_A I-A_m)P_m.                     (11)

The continuous terms cancel after this justified restriction; they are not discarded on the full carrier. From ||B||<=50L and ||H_full||<=4,

    ||A_arch-c_A I||<=50L+8.                                 (12)

A sufficient remaining theorem is therefore

    for every eta>0, lambda_max(P_m A_m P_m)
        <= C_eta m^eta eventually.                           (13)

Equations(11),(12) then give a restricted lower floor, contradicting(1) for any off-critical zero by taking eta<delta. Positive-part moments of P_m A_m P_m with one finite polynomial exponent independent of arbitrarily large fixed even orders suffice for(13). P_m and A_m are independent of moment order; no short arithmetic cutoff is needed for this receiver.

Estimate(13) is OPEN. The deterministic prime shifts and projections are not independent random graph edges. The OpenAI divisor-graph mechanism still requires an exact source map. No graph analogy or low-rank argument proves(13). Full SP, old G1/G3 and RH remain unproved.


This is a checked candidate receiver, not a silent activation or closure of the ongoing full-SP consumer. Q6 remains the sole pending question in its existing phase. Compare its terminal result before adopting a changed exact consumer or opening another phase.

## Bounded primary-source alias return

Dictionaries queried: prime dilation/translation adjacency nontrivial spectrum; Weil quadratic form with Mellin zeros at plus/minus one half; Sonine/co-Poisson/de Branges constrained spaces. All three ask.sh queries returned INCOMPLETE due to q3_docs freshness, not absence. Researcher long_positive_alias found no mapped supplier in this bounded pass.

Existing shelf source: Enrico Bombieri, Remarks on Weil's quadratic functional in the theory of prime numbers, I, Rend. Lincei Mat. Appl.11(2000),183–233. PDF docs/routeB_bus/litreview/pdfs/bombieri_weil_quadratic_functional_2000.pdf, SHA25620bd544fc5297766966630092aba4c1e10c6a7e663d14be89bbe1d0c8220b7fd. Primary URL https://www.bdim.eu/item?fmt=pdf&id=RLIN_2000_9_11_3_183_0. Root independently read the rendered printed p191 theorem; local PDF used after web fetch timed out.

Theorem1, section3, p191 begins: “The Riemann Hypothesis holds if and only if”. Its condition is positivity of sum_rho gtilde(rho) conjugate(gtilde(1-rho)) for every nonzero complex smooth compactly supported g on the positive half-line. Section2,p186 defines gtilde(s)=int g(x)x^(s-1)dx. With g(x)=x^(-1/2)f(log x), gtilde(s)=M_f(s-1/2); our Laplace constraints are gtilde(0)=gtilde(1)=0. This maps the zero functional, not a source-only upper bound on A_m. Our inherited form-projection estimate, not that theorem, pays the finite Fourier return.

Disposition: verified discovery evidence for the classical Weil criterion, NOT a supplier for(13). Invoking its positive conclusion would assume an RH-equivalent premise. The source does not estimate the constrained prime spectrum unconditionally. The conditional off-critical witness in(1) is the relevant negative discriminator: killing pole moments alone cannot make its negative signal disappear. No new graph or stochastic hypothesis is imported. Compare this scoped result with terminal Q6 before choosing a next consumer.
