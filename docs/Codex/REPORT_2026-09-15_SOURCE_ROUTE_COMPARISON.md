# Source route comparison after the reconstruction and marginal hunts

STATUS: ANALYTIC_PAPER_CANDIDATE / ROUTE_AUDIT. Source base aa692d341c853bfcd69fae6dec7683eca2a3d4d7. No new RH route is declared proved or selected by this audit. V remains parked, native goal remains paused, canonical admission remains false.

## 1. What the current zero-exclusion proof actually uses

The CRITICALSTRIP response (raw SHA256 c84d367a7d3a30fed8671c482380c9c754f67d356846e9f6806e2a4c327f706c) and accepted intake I1-I2 (SHA256 f28495620937793b270bf28208019c0d3c6915cd4de00932fe48f351c37b6e21) give a useful stronger reading of the proof.

Fix ANY finite list of positive rates lambda_1,...,lambda_N, with lambda_1=min lambda_n=:lambda. Let r be the density of the sum of independent shape-two gammas with those rates. Define

G(x)=sqrt(r(e^(2x))r(e^(-2x))),
M(z)=integral_R G(x)e^(-izx)dx / integral_R G(x)dx.

Exactly the same factorization from the first gamma term gives, for N>=2,

r(t)=c exp(-lambda t) integral_(sum s_n<t) (t-sum s_n) product_(n=2)^N s_n exp(-(lambda_n-lambda)s_n) ds.

The logarithmic substitution t=e^xi, s_n=e^(y_n) gives log integrand
xi+log(1-sum exp(y_n-xi))+2sum y_n-sum (lambda_n-lambda)exp(y_n),
up to an additive constant. It is jointly concave on its convex support. The differences need only be nonnegative; equality is allowed. Prékopa therefore makes
L(xi)=log[exp(lambda e^xi)r(e^xi)] concave. The N=1 case is affine directly.
It follows that

-(log G)''(x)>=4lambda cosh(2x)>=4lambda.                    (R1)

All finite positive-rate convolutions have a polynomial times exp(-lambda t) large-t tail, including tied minimum rates, and a power t^(2N-1) at zero. Thus G has double-exponential tails and the tilted integration-by-parts argument is valid just as in the accepted proof. For every real v,

Var_v(X)<=1/(4lambda),
|M(u+iv)|>=1-u^2/(8lambda)>0 when |u|<sqrt(8lambda).          (R2)

The proof of the modulus bound is the same centered cosine inequality and M(iv)>=1 from evenness. This generalization does not claim any new theorem about arbitrary large u.

For our actual lambda_n=pi n^2, the final bound therefore sees lambda=pi and the fact lambda_n>=pi; it does NOT use the exact square spacing of the remaining rates. Reciprocal symmetry of the full infinite r is used elsewhere to identify the limit as the exact Phi/xi. It is not used to control cancellation outside (R2).

This diagnoses the dependence of this particular proof. It does not prove that square spacing must appear in every possible proof, that a unique additional property is necessary, or that no stronger theorem can use coarser hypotheses.

## 2. An exactly soluble comparison makes the distinction concrete

If every finite rate equals lambda, then r(t)=lambda^(2N)t^(2N-1)exp(-lambda t)/Gamma(2N). Hence

G(x)=lambda^(2N)/Gamma(2N) exp(-lambda cosh(2x)).             (R3)

The normalized G and its normalized transform are independent of N. For lambda=pi this is exactly the previously proved first-member Bessel model, including its real-zero theorem. It is not a new Bessel result. Making the finite family easier in this way does not approximate our full theta source: it simply repeats the same normalized model. This supplies a transparent check on the idea that a more tractable reconstruction necessarily moves toward the original target.

## 3. Map of retained advantages and unpaid transfers

| Proved input or construction | Where it already works | What it does not currently supply |
|---|---|---|
| Fixed infinite gamma product with rates pi n^2 | Exact probability density r; additive TN of every order; controlled finite-source convergence | Zero location of its Mellin transform |
| Exact reciprocal identity r(1/t)=t^(5/2)r(t) | Correct centered even source Phi and the exact xi limit | Cancellation control at all complex frequencies |
| Geometric finite family | Entire normalized Fourier transforms and exact limit; central zero-free slab by R1-R2 | C6 for arbitrary R; the stronger all-real fixed-N route is already excluded for every N>=13 |
| Arithmetic reciprocal family H_N | Entire source, no square-root branch, expanding Fourier strips and the same xi limit | A sufficient zero-exclusion property; it loses the uniform positive curvature mechanism |
| Exact Gaussian/radial-angular representation of H_N | All weights and normalization retained; radial integral explicitly evaluated | Small global interactions: sphere Lip(log Q_N)=N-1/N, and 2N Q_N returns to the full source in probability |
| Barvinok non-cancellation theorem | A genuine sufficient theorem for its stated product measures and budgets | The tested affine, natural latent, and positive global-Lipschitz Gaussian representations fail its relevant hypotheses |

The old RH_ROUTE_AUDIT and JOINTSOURCE_Y intake already identified additive TN versus Mellin zero-location as a missing transfer. This is not a newly discovered gap. The new comparison adds R1-R3 and incorporates the intervening successful central-slab result and the exact reconstruction tests. The prior full-plane gamma exclusion does not exclude compact critical-strip C6, and no historical cofinal-real-zero proposal is reopened.

## 4. Decision before further descent

There is a proved source advantage: additive all-order positivity and exact arithmetic reciprocity. There is also a demonstrated finite-family zero-exclusion mechanism. What is missing is a verified operation combining source information with control of the remaining oscillatory cancellations, without assuming the target zero property.

No currently supplied theorem/application card closes that combination. A new Gaussian coordinate change or another name for C6 is not evidence that difficulty decreased. The known strongly log-concave negative control shows why the scalar shape estimate alone does not settle general zero location; it is not a counterexample satisfying the full arithmetic source assumptions.

Keep the direct Barvinok implementations parked after the two bounded preflights. Keep the arithmetic reconstruction as an exact alternative and the geometric slab as an actual result. The next allowed discovery question is whether a specific published mechanism uses the exact rate-product or reciprocal operation in a way the scalar bound does not; first reconcile earlier TN/Mellin, Bessel and Lee-Yang findings. This is exploratory discovery, not an assignment to prove that an unverified analogy implies RH.

Before a proof task is selected, require one concrete application: known source property, exact map, theorem hypotheses on that mapped object, full sufficient output, and a scoped falsifier. Reject a candidate that merely assumes Mellin zero-freeness, needs the already excluded full-plane approximant property, or loses weights/boundaries. No new Proshka request is prepared by this audit, and no proof progress is counted from the number of representations or reports.
