# Q05 own attempt 1: quantitative return of logarithmic Mobius correlation

2026-10-20. Bounded supplier preflight after Q04; no Pro request.
The missing object is a weighted, growing-shift, joint matrix correlation,
not merely a scalar statement that Mobius signs cancel. Preserve original
N=m,L=log(m),M=R=floor(m^epsilon), actual P and all k-cross terms.

## Exact return point and search dictionaries

Q01 verdict (14),(24)–(30),(38),(39):
 B_d=sum_(dk<=m) log(k)/sqrt(dk) P Q_M(log(dk))P,
 ||B_d||<=b_m/sqrt(d), b_m=40+16Omega;
 O_D=sum_(1<=h<D)(1-h/D) sum_(D<d<=2D-h)
     mu(d)mu(d+h){B_d,B_(d+h)};
 T²<=2J G_m, G_m=diagonal+sum_D O_D>=0,
 diagonal<=b_m² log(m/R)P, J=O(log m).
This is a stronger sufficient squared certificate, not the original necessary
one-sided goal. Q04 cheap inverse3+6Omega remains available but supplies no
estimate of O_D. Every intermediate P in B_d B_e remains.

Search dictionaries: shifted multiplicative-function correlations; weighted
operator Fejer/Gram averages; entropy decrement and near independence under
logarithmic sampling. UNVERIFIED hint1: transfer scalar logarithmic correlations
by summation by parts to actual kernel weights. UNVERIFIED hint2: use the Q01
cofinal trace average instead of adaptive-W control. Both require new return
estimates; neither is accepted below.

Three ask.sh queries (logarithmically averaged Chowla Mobius correlations;
multiplicative functions short intervals mean square; operator weighted Mobius
shifted correlation) all ended ASK_STATUS: INCOMPLETE, semantic-index freshness
validation failed. This is not absence. Direct Q01 source already displays the
unpaid weighted correlations, so a bounded primary-source check follows.

## Source-verified partial analogue, not a supplier

Terence Tao, arXiv:1509.05422v4 (29 July2016), pp5–6, Theorem1.3,
Corollary1.5 and the Mobius example following Remark1.6.
URL https://arxiv.org/pdf/1509.05422v4
Local ccm_q05_sources/tao_1509.05422v4.pdf
SHA256467329ae414b669808555fddf131be3bc07025777ae3af8ccdea6e98db6722e9.
Verbatim short locator quote, p6:
"at least one of g1, g2 is equal to the Möbius function µ."
(The source uses mathematical subscripts.)

The source establishes logarithmically averaged two-point cancellation for
fixed affine forms under a nonpretentiousness hypothesis; p6 explicitly
includes sum_(n<=x)mu(n)mu(n+1)/n=o(log x). Theorem1.3's threshold A depends
on the requested error and affine coefficients. The window parameter must
grow for the asymptotic form. No polynomial rate or the actual CCM matrix
weight is supplied by this quoted result.

Mapping: n=d, affine coefficients a1=a2=1,b1=0,b2=h, g1=g2=mu.
Actual h ranges up toD with m, while the theorem fixes the affine forms.
The actual weight is ReTr(W B_d B_(d+h)), containing both finite k sums,
all mode couplings and m-dependent P. It is not the scalar1/d weight.
A dyadic d-window has logarithmic ratio2; one cannot insert omega=2 into
the omega->infinity conclusion. Allowing larger logarithmic windows still
leaves the growing h, kernel variation and rate returns unpaid.
Negative control: g1=g2=1 has a nonzero logarithmic mean and fails the source's
nonpretentiousness input. Arbitrary source-adaptive matrix weights may undo
sign cancellation; Q01 §7.2 provides that separate planted model, not CCM.

## Own quantitative test: grant MORE than the source and count all shifts

Suppose, solely as a hypothetical stronger supplier, for every source block,
every1<=h<D and every W>=0 supported onP with TrW=1, the actual correlation
(after its kernel weight and full k sums) satisfied

 |sum_(D<d<=2D-h) mu(d)mu(d+h)
       ReTr(W B_d B_(d+h))| <= C b_m² D^(-kappa),  0<kappa<1.       (H)

This is NOT imported from Tao and NOT assumed in the target proof.
The anticommutator trace equals twice this real trace. Counting h, retaining
the triangular coefficients <=1, gives
 Tr(W O_D)<=2C b_m² D^(1-kappa).
Sum dyadicD to m. The geometric constant may depend on fixed kappa, giving
 O_m <= C_kappa b_m² m^(1-kappa)P.
Q01 then yields
 ||T|| <= C_kappa b_m sqrt(J[log(m/R)+m^(1-kappa)]).
Since b_m=O_epsilon(m^epsilon/log m), the resulting power is
 epsilon+(1-kappa)/2 up to logs, followed by the already paid3epsilon/2
short return if a scalar T bound is returned to K.

Consequences of THIS per-shift absolute-payment mechanism:
- To beat the inherited full3/8 exponent at fixed epsilon, need
  kappa>1/4+2epsilon (strict margin for logs).
- To reach eta(epsilon)->0, need kappa(epsilon)->1, as well as legitimate
  uniformity and all kernel-weight costs. kappa=1 gives only extra logs;
  constants may depend on fixed epsilon, not m.
- Qualitative o(1) normalized correlations give no such power. Even granting
  the much stronger uniform actual-weight bound C b_m²/log(D), the same
  shift count is O(b_m² m/log m), retaining exponent1/2+epsilon up to logs.
  The model rate1/log D is o(1) but exceeds every D^(-a), a>0, eventually,
  even on every unbounded subsequence. This is a rate-implication control,
  not a lower bound or model of actual Mobius correlations.

Thus neither scalar qualitative cancellation nor cofinal selection by itself
pays the Q01 certificate. This calculation does NOT forbid summing shifts
jointly with signs, another receiver, or a stronger quantitative theorem.
It rejects only this automatic transfer of the identified theorem.

## Decision

One own no-full-gain preflight completed after Q04. Do not send Q05 yet.
Next bounded candidate should control the joint aggregate of shifts/weights,
or prove a source-specific cancellation before the squared certificate.
Stop a proposed import before computation if it only supplies fixed-shift
qualitative/logarithmic savings. No new full arithmetic exponent, Lean/Arb,
actual prime panel or RH result. Independent read-only review ccm_q01_return_review: bounded PASS for
source mapping, full hypothetical return, thresholds and negative-control scope.
