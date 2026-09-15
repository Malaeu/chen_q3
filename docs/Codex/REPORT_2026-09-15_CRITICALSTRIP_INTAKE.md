# CRITICALSTRIP intake and comparison of two exact source assemblies

STATUS: ANALYTIC_PAPER_CANDIDATE; scope is a uniform central zero-free slab and an explicit assembly tradeoff, not RH or full C6.

## 1. Exact receipt

Proshka request REQ-2026-09-15-CRITICALSTRIP was answered by commit
08b6b69c5ff269297b04a87df128d8459ee3471b on codex_mac/gamma-reciprocity-20260914.
Raw: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_CRITICALSTRIP_2026-09-15.md.
SHA256 c84d367a7d3a30fed8671c482380c9c754f67d356846e9f6806e2a4c327f706c; 45903 bytes,464 LF,CR0,UTF-8.
Independent exact-raw verdict: ACCEPT_UNIFORM_GAMMA_ZERO_FREE_SLAB_ONLY.
The raw response is preserved unchanged. The living chat subsequently returned this same commit and is idle; completed agent message 61d4c2b0-ab8c-46fc-ab21-b9243333cb2f.

## 2. The mechanism that actually transfers

Let r_N be the exact density of sum_(n<=N) Gamma(2,1)/(pi n^2), and
G_N(x)=sqrt(r_N(e^(2x))r_N(e^(-2x))). Write lambda_n=pi n^2.
Extracting the first gamma rate gives

r_N(t)=c_N exp(-pi t) integral_(sum s_n<t) (t-sum s_n) product_(n=2)^N [s_n exp(-(lambda_n-pi)s_n)] ds,
c_N=product_(n=1)^N lambda_n^2.

For N>=2, substitution t=e^xi and s_n=e^(y_n) makes the logarithm of the integrand of exp(pi e^xi)r_N(e^xi), apart from a constant,

xi+log(1-sum exp(y_n-xi))+2 sum y_n-sum (lambda_n-pi)exp(y_n).

This is jointly concave on the convex support sum exp(y_n-xi)<1. Prékopa's marginal theorem therefore makes
Q_N(xi)=log[exp(pi e^xi)r_N(e^xi)] concave. For N=1, Q_1 is affine directly. Consequently

-(log G_N)''(x)>=4 pi cosh(2x)>=4 pi.                         (I1)

This is a property of the actual finite gamma family, not a generic wish for a positive representation. Primary: A. Prékopa, 1973, Theorem 6 (PDF page8), https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, SHA256 2bb16932ce23fa31a0f9a44fc60bee6439883ad837f500277ef95dda250b3fc3. The marginal integral inequality in its proof was checked, including the conclusion's typographic omission.

## 3. Exact benefit and exact limit

For real v let E_(N,v) be expectation in density proportional to e^(vx)G_N(x). The endpoint expansions in the raw proof justify integration by parts; (I1) gives

Var_(N,v)(X)<=1/(4 pi), for all N>=1 and v real.

Put M_N(z)=integral G_N(x)e^(-izx)dx / integral G_N(x)dx. Center the tilted random variable and use 1-cos t<=t^2/2. Since evenness implies M_N(iv)>=1,

|M_N(u+iv)|>=1-u^2/(8 pi)>0, for |u|<sqrt(8 pi).              (I2)

In particular |M_N(u+iv)|>=1/256 for every N>=1, |u|<=5, and every real v. Thus the earlier C6 condition is proved for R<=5 with N0=1. The same bound passes to normalized xi at each fixed z by the established source limit.

This is not claimed to improve known low-height zero exclusion for xi. The research increment is an exact source argument uniform in all the finite gamma approximants. C6 requires every fixed R, so its arbitrary-R part remains open. Neither full V positivity nor RH follows from (I2).

The raw proof also gives a different positive even strongly log-concave source whose Fourier transform has nonreal zeros. Its optional double-exponential tail modification still has nonreal zeros. This excludes inference from scalar curvature plus a qualitative tail alone; it is not a counterexample satisfying the full gamma/TN source assumptions. The actual rate-product structure must remain available for any next argument.

## 4. What the arithmetic reconstruction gains and loses

Our independent arithmetic assembly is

H_N(x)=[e^(5x/2)r_N(e^(2x))+e^(-5x/2)r_N(e^(-2x))]/2.

The adjacent AR1-AR4 report proves that H_N is entire in the source variable, has no square-root source branch, and has the same limit Phi. Its normalized Fourier transforms converge to normalized xi uniformly on every fixed horizontal strip eventually in N. For each fixed N the defining integral has strip |Im z|<4N+1/2; it is not claimed entire.

There is an additional, now decisive comparison. The finite exponential-polynomial density has the convergent expansion

r_N(t)=C_N t^(2N-1)(1+O_N(t)), C_N>0, near t=0.

This expansion can be differentiated termwise. Together with the exponentially small large-t term it implies, for x->+infinity,

log H_N(x)=log(C_N/2)-(4N+1/2)x+O_N(e^(-2x)),                 (I3)

where the error remains O_N(e^(-2x)) after one or two x derivatives. Indeed the reflected term has an analytic factor 1+O_N(e^(-2x)); the direct term and each of its first two derivatives are super-exponentially small relative to the displayed exponential tail. Hence

-(log H_N)''(x)->0.                                         (I4)

For every fixed N, H_N therefore fails any global lower curvature bound by a positive constant. In particular it does not retain (I1). This does not prove a zero of its transform, non-log-concavity, or impossibility of other useful estimates. It says precisely which newly successful mechanism an automatic switch would lose.

## 5. Route decision

Both constructions recover the same exact source and have proved but different advantages. Keep both results. Do not select arithmetic reconstruction solely because it has no source square-root branches; those branches are not themselves the target Fourier-zero obstruction, and the geometric family now has a demonstrated source mechanism.

The next useful search must ask what extra structure lets a marginal/integral argument control oscillatory cancellation beyond a variance bound, while preserving the exact gamma rate product and reciprocal coupling. Any complex or oscillatory analogue of Prékopa is a candidate to inspect, not a theorem whose existence or applicability is asserted here. Renaming the remaining Fourier real/imaginary cancellation equations does not reduce that obligation.

Stopping filter: a candidate that gives only a bound from the same scalar curvature or needs the unknown zero-free property as a premise supplies no new bridge. Record that failure and return to the source structure rather than start another chain of residuals. No new Proshka request, native-goal replacement, canonical admission, or source-sign counter reset is made by this intake.
