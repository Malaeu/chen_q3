# Mobius source return and the finite-window boundary block

Status: auxiliary PAPER results and bounded own attempt independently checked.
No G1/G3 status change. Source: Proshka answer 6/10, captured verbatim in
`PROSHKA_MOBIUS_SOURCE_RETURN_INLINE_2026-10-06.md`.

Independent `/root/mobius_source_audit` checked (1)-(16), retaining the
previously established two-column mass estimate as an inherited input.
It found no mismatch in source, Gaussian bounds, window, complex metric
or sign. It also checked the full-band boundary-block identity and the
sample-replacement error estimates below. `/root/signed_obstruction_map`
separately checked (17)-(22). No new source sign is accepted.

## Root check of the return obstruction

The elementary Mellin integral, with s=1/2-i*gamma, is

    psihat(gamma)=pi^(-s/2)[12 Gamma(s/2+1)-8 Gamma(s/2+2)]
                 =2s(1-s) pi^(-s/2) Gamma(s/2).

It is nonzero at fixed positive real gamma. The derivative operation on
exp(t/2) P(v) exp(-v), v=pi exp(2t), is
P -> P/2+2v(P'-P). Applying it twice to 24v-16v^2 gives
150v-660v^2+448v^3-64v^4. A Python Fraction calculation independently
checked these exact rational coefficients; this is algebra only.

For Re(s)=1/2, comparing sums with integrals gives a uniformly bounded
error in sum_(n<=X) n^(-s) and sum_(n<=X) n^(-s) log n, including the
fractional last interval. The derivative integrals are 2|s| and 2+4|s|.
The constants C_s,D_s in answer6 safely cover the lower and upper endpoints.
Substituting beta_k(r)=log r-sum_(c|r,c<=k) Lambda(c) therefore gives
answer6 (18)-(20); sum_(c<=k) Lambda(c)/sqrt(c)<=2sqrt(k)log(k), and
A_k<=log(k)(1+log(k))=o(log J).

Eventually Q<m/2 and r<=J=floor(m/(k+1))<=m/2. Thus r floor(m/r)
is at least m-r>=m/2, and every k<r<=J has a nonempty d range. At two
fixed distinct positive critical-line zero ordinates gamma1,gamma2, all
translates of g_z have zero Fourier value. Transform ONLY the finite
expression F_mu-Tg, never the infinite Mobius expansion. The resulting
two rows are (z0-gamma_l^2 z2) B(gamma_l) B_(k,J)(s_l).
Their normalized limiting matrix is invertible; the J^(i gamma_l)
factors are unitary row phases. Equation (9) pays the right half-line,
so the left-exterior L1 lower bound (17) follows by the triangle inequality.
This uses existence of two critical-line zeros, not RH or simplicity.

The Fourier integrals exist: psi and its two derivatives are integrable
at both ends; G and G'' have the established even Gaussian tails. The
source identity Ghat=-4 xi is already recorded in ODD_TRIAL_SIGN at the
exact coefficient decomposition. It also follows by Mellin integration
where Re(s)>1 and analytic continuation, using the Gaussian Mellin factor
above; it does not require interchanging an infinite Mobius sum on Re(s)=1/2.
Independent `/root/signed_obstruction_map` checked (17)-(22), including
the fixed-frequency asymptotic, two-column singular-value bound and
left-exterior subtraction, without an algebraic finding. Root discharged
its stated integrability/source-identity qualifications as above.

This obstructs discarding the whole-line source-inversion remainder ONLY.
It gives no adverse sign for the finite-window complementary correlation.

## Own attempt: exact band projection and cyclic boundary return

Let I=[-L/2,L/2], X=1_I g_z, and let P be the orthogonal FULL Fourier
band projector with frequencies +/-{m+1,...,3m} on L2(I). It includes
sine as well as cosine modes. Since X is even, p=PX is the existing
even cosine-band projection. A cosine-only projector would not commute
with translation and cannot be used in the following argument.

For 0<=a<=L let V_a be periodic translation on I, and let

    B_a f(t)=1_(t>L/2-a) V_a f(t),
    T_a f(t)=1_(t<=L/2-a) f(t+a)=V_a f(t)-B_a f(t).

P commutes with V_a. Hence the exact mixed block is

    P T_a (1-P)=-P B_a (1-P).

For the same real signed weights w_dr=nu(d)beta_k(r)/sqrt(dr) and product
cut Q<=dr<=m, set B=sum w_dr B_(log dr), T=sum w_dr T_(log dr). Then

    2 Re<p,T(X-p)>=-2 Re<p,B(X-p)>.

This is a boundary-return representation, not a sign estimate. Each
M_a=1_(t>L/2-a) is an orthogonal multiplication projection, so
||P M_a(1-P)||<=1/2 (square its norm and use A-A^2<=1/4 for A=P M_a P).
Since V_a commutes with P, ||P B_a(1-P)||<=1/2 as well. Consequently
the generic bound is A_m ||p|| ||X-p||, where
A_m=sum|w_dr|<=2sqrt(m)L(1+L). It fails to give the needed relative
source estimate: ||X-p|| is of fixed source size while ||p|| is tiny.
This failure of an upper certificate is not a lower bound on the correlation.

### Pay the actual-sample versus projected-source difference

The supplied rho uses full-line Fourier samples, whereas p uses window
coefficients. For m>=3 the complete even Gaussian source satisfies

    integral_(R\I) |g_z| <= (2 C_G/pi) m^(13/4) exp(-pi m) ||z||.

There are 2m cosine modes, each coefficient error is bounded by
sqrt(2/L) times that L1 tail. Thus

    ||rho-p|| <= D_m ||z||,
    D_m=(4 C_G/pi) m^(15/4) L^(-1/2) exp(-pi m).

Put C_X=(||G||_2^2+||G''||_2^2)^(1/2), a fixed finite constant.
The difference between C_rho=2 Re<rho,T(X-rho)> and C_p is bounded by

    |C_rho-C_p| <= 2 A_m D_m (3 C_X+D_m) ||z||^2.

Indeed write rho=p+delta, expand, and use ||p||<=||X||<=C_X||z||.
Using Ehat=||rho||^2>=mu_m||z||^2/4, its relative error is at most
8 A_m D_m(3 C_X+D_m)/mu_m=o(1/m), because T_m=O(m/log m).
The similar replacement in 2 Re<rho,F_mu> costs at most
8 D_m(A_m C_X+J_m)/mu_m relative to Ehat, by answer6 (11).

Thus the boundary-block representation can be used at the required
relative precision. But Type II shifts have log(dr)>=log Q>L/2
eventually: their wrap strips reach the source center. Gaussian smallness
at the physical endpoints cannot make this block small by itself.
The unpaid requirement is the signed weighted boundary block together
with the low arithmetic range and explicit Type I endpoints.

Negative control: for unrestricted input, projection and a sharp window
have a nonzero mixed block, and replacing the complementary input by its
negative reverses its real pairing. Projection contraction alone supplies
no sign. The actual theta source imposes extra relations which must be used.

Next step: a source-specific finite-section/Hankel estimate with an actual
signed bound, or a rigorous reason to abandon this mechanism; do not count
the identity above as progress on the missing sign.

## Bounded alias return

Object dictionaries: finite-section Wiener-Hopf/Hankel boundary block;
time-frequency limiting and projection commutator; Sonin-space compressed
dilation and reflection positivity. Shelf queries were INCOMPLETE: the
semantic index freshness check failed, and root's Wiener Hopf query also
hit ask.sh's unset LOCAL_CANDIDATE_RECORDS array. No absence is inferred.

One verified partial analogue: Connes--Consani, arXiv:2006.13771v1,
https://arxiv.org/abs/2006.13771, Theorem 1, printed p.3, equation (4).
Local PDF: `../litreview/pdfs/2006.13771.pdf`; SHA-256
`b8e0b54ade8535cf3ca633d1ef325bfc5c793b407da577a83d111726935b58e0`.
Exact short quote: "vanishing at" i/2 "and 0. Then one has"
W_infinity(g*g*) >= Tr(vartheta(g) S vartheta(g)*).
Root independently inspected the rendered original p.3: the fraction is
i/2, NOT 2i as the text extraction can suggest.

Hypotheses: smooth multiplicative test supported in [2^(-1/2),2^(1/2)],
the two stated transform vanishings, and the infinite Sonin projection S.
With t=log x, dilation maps to translation, but their S does not map to
our finite band P, and their positive trace is not the mixed block above.
The theorem controls only the archimedean functional; its short support
excludes prime contributions. Our interval grows like log m, retains all
prime powers, and the zero-extended band is not automatically a smooth
compact test. These are OPEN/INAPPLICABLE hypotheses, not cosmetic changes.
Negative control: enlarging support until a prime translation is present
leaves the theorem's domain. Its archimedean positivity pays no such atom.
Verdict: VERIFIED discovery evidence, PARTIAL ANALOGUE, not a sign supplier.
No new PDF was needed; the source was already on the shelf.

## Continuation 7/10 (sent 2026-10-06, 18:06 Europe/Berlin)

Sent once through the existing Missing T7 Lemma chat. Browser DOM readback
shows this exact user message; read_thread reports active. The browser's
live stream reports a disconnected connection while retaining Stop;
this is not a completed answer or a reason to resend. Next check: read
the matching answer after completion; do not send question 7 again.

Continuation 7/10, same source-transfer route and prescribed-U G1 discriminator. The owner now explicitly directs Codex Mac and you to complete RH by the fastest justified route, using our accumulated work and alias-hunt, with minimal bookkeeping. This is not permission to assume an open bound or call a candidate proof.

Answer6 has been processed. Independent bounded audits accepted (1)-(16), including the actual source normalization, cutoffs, Gaussian constants, window restoration and exact complex metric, conditional on the previously checked mass input. A separate audit accepted (17)-(22): two fixed critical-line zeros obstruct dropping the whole-line Mobius return. Root checked the integrability and -4xi source identity. We accept these auxiliary results only; (24), U, G1 and G3 remain OPEN.

Our own attempt makes the complementary correlation an exact boundary block, with the actual-source replacement error paid:
I=[-L/2,L/2], X=1_I g_z. Let P be the FULL symmetric Fourier band +/-{m+1,...,3m}, INCLUDING sine modes. On even X its projection p=PX is the cosine-band source projection. For 0<=a<=L define periodic translation V_a, B_a=1_(t>L/2-a)V_a and truncated translation T_a=V_a-B_a. P commutes with V_a, so P T_a(1-P)=-P B_a(1-P).
Use the unchanged Type II weights w_dr=nu(d)beta_k(r)/sqrt(dr), d,r>k, Q<=dr<=m. With B=sum w_dr B_log(dr), T=sum w_dr T_log(dr), exactly
C_p(z)=2Re<p,T(X-p)>=-2Re<p,B(X-p)>.
This is not a sign theorem. For each a, ||P B_a(1-P)||<=1/2, but the absolute weighted bound A_m||p||||X-p||, A_m<=2sqrt(m)L(1+L), loses the relative scale. Moreover log(dr)>=log Q>L/2 eventually, so wrap strips reach the source center; small Gaussian endpoint values do not pay this block.

Your rho uses full-line Fourier samples. Source evenness and the complete Gaussian tail give
||rho-p||<=D_m||z||,
D_m=(4 C_G/pi)m^(15/4)L^(-1/2)exp(-pi m).
For C_X=(||G||_2^2+||G''||_2^2)^(1/2), the replacement in C costs at most
8 A_m D_m(3C_X+D_m)/mu_m
relative to Ehat. Replacement in F=2Re<rho,F_mu> costs at most
8 D_m(A_m C_X+Jmath_m)/mu_m,
where Jmath_m is your (11) local error envelope. Both are o(1/m). An independent checker verified the boundary identity and these estimates.

Alias return: three shelf queries were INCOMPLETE, so no absence claim. We reread and rendered Connes-Consani arXiv:2006.13771v1 Theorem1 p3 Eq4 (already on our shelf). It concerns W_infinity and an infinite Sonin projection, fixed support [2^-1/2,2^1/2], vanishings at i/2 and 0; not 2i, an OCR trap. It does not bound our finite-band mixed block or include our prime-power range. Do not import its positive trace without a proved map and paid correction.

Please make one concrete source-specific attack on the SIGN of this boundary-return block together with P_low+End and F_mu. The target is still your (24), equivalently a sufficient R_m(z)<=(kappa_m+1/(256m))*Ehat_m(z) for every complex z on one unbounded ORIGINAL subsequence, with every replacement error paid. The full compensated Qhat, retaining positive image and pole terms, is also allowed if its source lower bound is genuinely proved. A useful result must be a signed gain at the required scale or a rigorous source obstruction; another exact renaming, norm contraction, or paid tail alone does not decide this candidate.

Strategic context that now matters: while you worked, the selected-shell G4 scalar/phase crosswalk and G3c projection bridge were PAPER checked under accepted HMODE/chi. The same scaled trial differs from fixed 4 h_CCM by O(lambda^-2) on its window; the E_star L2 error is O(m^-1/4), and the fixed inversion-even Gaussian target has Fourier tail O(log m/m). Thus the selected trial converges on the actual consumer strip |Im z|<1/2. Ground-to-trial G3 is still OPEN. Under the existing matched T1-T6, alpha_m=O(m^-1/4(log m)^A), fixed A>=0, is sufficient; all-height superpolynomial T7 is stronger than needed. This does not identify the ground vector with the trial or supply G1.

If this bounded signed attack still produces no source-signed gain, explicitly diagnose the mathematical stall and recommend the next single proof obligation within source transfer using that weaker actual consumer. Explain what evidence it would add; do not declare U false from finite cells or declare source transfer dead. Preserve one-family semantics, all prime powers, original quantifiers and normalization. No Lean or repository writes.
