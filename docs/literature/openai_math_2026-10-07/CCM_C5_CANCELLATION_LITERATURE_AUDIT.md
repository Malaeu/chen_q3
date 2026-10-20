# C5: bounded cancellation-mechanism hunt

2026-10-20. Source baseline 29cd3a57. Outcome: no sufficient signed supplier
found in this bounded search. C5, full SP and RH remain OPEN. No new Lean run,
external review send, or mathematical admission.

## Brief and invariant

The difficult object is a prime-weighted sum of truncated translations, tested
on the original constrained Fourier space. Positive arithmetic weights do not
fix its spectral sign. A successful mechanism must control the joint form,
including its off-diagonal entries, for every required test vector.

Keep N=m, L=log m, M=floor(m^alpha), R=floor(m^beta), original three-constraint
P, and H(t)=P Q_M(log t)P/sqrt(t). The surviving prime-only matrix is

    Pi = sum_(R<p<=m, p prime) log(p) H(p).

Required: an absolute finite c, for every sufficiently small fixed alpha,beta>0,

    lambda_max(Pi) <= C_(alpha,beta) m^(c(alpha+beta)) eventually.

This supplies C5 through the paid comparison in
CCM_C5_SIGNED_SUBLEMMA_ATTEMPT.md; its converse holds after enlarging c.
The consumer is the original sparse-band receiver on the full source, NOT a
full-M=m floor. All proper powers are restored through their existing
O(L^2) fee; all small primes cost O(sqrt(R)log R). W5 pays the separate
weighted-LCM return O(m^(alpha+beta)L^2), not Pi.

Negative control outside the arithmetic family: a positive single translation
V_s+V_s* has whole-line multiplier 2cos(s xi) of both signs. Thus positivity of
weights alone is insufficient. Likewise an L2-small function can have a large
peak; an exceptional set cannot be removed when the test vector is adaptive.
Neither control is a counterexample to the actual CCM.

Search dictionaries: (1) prime Mellin twists / logarithmic Dirichlet polynomial;
(2) Perron explicit formula / zero-free vertical shift; (3) bilinear prime
correlation / Gallagher local variance. UNVERIFIED bridge hints were a uniform
twisted-primitive return and a short-interval-variance-to-compressed-form return.
The latter still requires an estimate and a quantitative matrix bridge.

## Local shelf

Read the exact C5 attempt, CCM_MOMENT_Q08_CONCLUSION, CCM_MOMENT_Q10_CONCLUSION,
CCM_FIXED_PRIME_COMPRESSION_TEST, CCM_LOG_DENSITY_CANCELLATION and sparse receiver.
Literal search found Gallagher already discussed in
PROSHKA_VERDICT_FULL_CCM_ONE_SIDED_Q06.md, especially the discussion near line722:
it retains the mixed centered correlations but does not bound them.

Three ask.sh --defer-external dictionary queries returned INCOMPLETE because
q3_docs freshness failed. Direct source reads remain evidence; those search
failures are not a complete denominator or a literature-absence claim. External
primary-source checks below were therefore made with this limitation explicit.

## Candidate 1: zero-free-region cancellation, worked full-source return

Primary authored exposition: Terence Tao, 246B Notes4 (2021), Remark25,
https://terrytao.wordpress.com/2021/02/12/246b-notes-4-the-riemann-zeta-function-and-the-prime-number-theorem/
Quote: “the classical zero-free region”. It states
psi(x)-x=O(x exp(-a sqrt(log x))), a>0. This is an unconditional scalar
cancellation estimate, not a CCM theorem. The proof mechanism moves the Perron
contour past the pole at1 into a zero-free region; the pole supplies the main
term and the permitted contour displacement controls the error.

Here is our separate matrix transfer, with no frequency average or lost entry.
Put Delta(t)=psi(t)-(t-1). Delta(1)=0 and H(m)=0. The existing source derivative
bound is ||H'(t)||<=(1+D_M)t^(-3/2), D_M=(2+8pi M)/L. Exact Abel gives

    sum_(2<=n<=m) Lambda(n)H(n)
      = integral_1^m H(t)dt - integral_1^m Delta(t)H'(t)dt.

The original v_plus,v_minus constraints give integral H=-P H_(1/2)P,
with ||H_(1/2)||<=4; see CCM_LOG_DENSITY_CANCELLATION.md before L1.
Splitting the error integral at sqrt(m), use the elementary
|Delta(t)|=O(t log(2t)) below it and the source estimate above it. Thus

    ||sum Lambda(n)H(n)||
      <= 4 + C(1+D_M)[m^(1/4)L + sqrt(m)exp(-a sqrt(L/2)) + 1].

Constants absorb the fixed initial range. Removing proper powers and primes
<=R costs only O(L^2+sqrt(R)log R). This yields a valid budget of size
m^(1/2+alpha-o(1)) for Pi, supplemented by those smaller fees. It is NOT a
lower bound on Pi and NOT a no-go theorem for sharper signed use of the source.
For arbitrarily small alpha,beta this budget is too large for c(alpha+beta).
Even before the derivative factor, a subexponential scalar error saving does
not remove the fixed 1/2 power introduced by the n^(-1/2) normalization.

Classification: VERIFIED source evidence; valid but insufficient direct bridge.
No theorem supplied the required signed improvement. This crude transfer may
be weaker than other available bounds and is not advertised as optimal.

## Candidate 2: Gallagher/Plancherel cancellation through local correlations

Primary paper: Coppola–Laporta, arXiv:1411.1739v1, p1 equation(star), p2 Lemma,
proof in section2, https://arxiv.org/pdf/1411.1739 . Short exact quote:
“the series S(t)” / “is absolutely convergent”. Finite Dirichlet polynomials
satisfy that hypothesis. The p1 consequence, with nu=log(n)/(2pi), is

    integral_(-T)^T |sum_n a_n n^(it)|^2 dt
      << T^2 integral_0^infinity |sum_(y<n<=y exp(1/T)) a_n|^2 dy/y.

For primes use a_p=log(p)/sqrt(p) on the literal retained interval; all other
coefficients vanish. Centering requires retaining the corresponding continuous
measure and every cross term in its squared local mass. The published discrete
formula alone does not certify that mixed measure bridge.

Decisive mechanism: Plancherel converts oscillation to local correlations. It
preserves those correlations rather than proving they are small. The source
gives no parameter-proportional bound for our centered right-hand side, and no
uniform adaptive CCM form bound is established here. Replacing the square by
its diagonal assumes the missing cancellation. The L2 peak control above
explains why averaging alone is not a uniform spectral certificate.

Classification: VERIFIED partial mechanism, already on the shelf; OPEN variance
estimate and OPEN exact matrix return. No C5 exponent supplied.

## Candidate 3: bilinear cancellation — test the phase before importing it

Tao, 254A Notes8, Theorem14(ii) and Proposition18,
https://terrytao.wordpress.com/2015/03/30/254a-notes-8-the-hardy-littlewood-circle-method-and-vinogradovs-theorem/
Quote: “Minor arc exponential sums are small”. The theorem concerns the additive
phase e(theta u v), with rational-approximation restrictions for minor arcs.
Our scalar Fourier ingredients have logarithmic phase (u v)^(it).

An elementary diagnostic pinpoints the failed import. On a rectangular block,

    sum_(u,v) a_u b_v (uv)^(it)
      = (sum_u a_u u^(it))(sum_v b_v v^(it)).

After differencing in v, the phase (v1/v2)^(it) is independent of u. The inner-u
oscillation exploited in the additive bilinear theorem is absent. The generic
coefficient control a_u=u^(-it), b_v=v^(-it) makes every summand one. These are
NOT the actual Mobius/prime coefficients. This rejects a coefficient-blind
transfer only, not Vaughan identities or every arithmetic Type-II argument.
The actual product cutoff and matrix factors have not been replaced by this
rectangle: it is a test of the proposed generic imported estimate.

Classification: VERIFIED source theorem; INAPPLICABLE direct phase mapping.
No C5 exponent can lawfully be imported from it.

## Candidate 4: cancellation for the correct logarithmic phase

Tao, 254A Notes5, Proposition6,
https://terrytao.wordpress.com/2015/02/07/254a-notes-5-bounding-exponential-sums-and-the-zeta-function/
Quote: “only in the regime when”. For f(x)=t log(x)/(2pi) on [N,2N],
T comparable to |t|, the two derivative hypotheses hold with an absolute A;
for 0<T<=N/(2A), the unweighted sum is O(N/T). Partial summation adds the
n^(-1/2) factor to give O(sqrt(N)/T). With N comparable to m and top band
frequency |t| comparable to M/L, this proxy budget is m^(1/2-alpha)L.
Bounded |t| leaves a sqrt(m) budget; t=0 is outside the derivative hypothesis.
Crucially, the theorem has no prime weights: this is NOT a bound for Pi.

The same source, paragraph following Exercise4, states the Vinogradov–Korobov
PNT error x exp(-a(log x)^(3/5)/(loglog x)^(1/5)). Substituting it into our
Candidate1 Abel argument improves the subexponential factor but still yields
m^(1/2+alpha-o(1)), not the C5 power.

Classification: VERIFIED partial analogue, missing prime-coefficient control.
This excludes direct use of this theorem, not all logarithmic-phase methods.

## Existing conditional alternative and excluded leads

CCM_MOMENT_Q10_CONCLUSION.md already retains a conditional 3/8 envelope under
its stated zeta-only ZF78 input. That is a fixed power, not c(alpha+beta) tending
to zero. It is not freshly re-proved here and is not an unconditional fallback.

A theorem for an oscillatory high-frequency subrange cannot pay the entire
retained band, including low frequencies. No such unpaid restriction is made.

## Validation

Root reread the cited primary statements. Independent read-only review found
no material defect in the own Abel/PNT matrix return and the log-phase
separability control; it did not re-audit the external theorems. Exact fetched
source bytes and hashes are listed in CCM_C5_CANCELLATION_SOURCES.json.

## One next bridge, with a stopping condition

A new candidate must provide a bound for the centered local correlations in
Candidate2 AND control their pairing with the actual compressed spectral
weight. Before any numerical scan, calculate the resulting power including
frequency cutoff, tails, and original mixed entries. Stop that bridge if it
leaves a fixed positive power independent of alpha,beta, or replaces the
adaptive weight by a frequency average. No current source here supplies those
inputs; this is a bounded research question, not a selected successful method.

AUTOPSY: dropped=THEOREM_SHAPE; note=zero-free scalar cancellation has an insufficient direct matrix budget; Gallagher preserves but does not estimate the needed joint correlations; C5 remains OPEN.
