# All fixed finite renewal prefixes: accepted scope and route consequence

STATUS: INDEPENDENTLY_REVIEWED_PAPER.
VERDICT: ACCEPT_ALL_FIXED_FINITE_RENEWAL_PREFIX_OBSTRUCTION_ONLY.
FULL_V_SIGN: OPEN. RH_PROVED: false. CANONICAL_ADMISSION: false.

## Exact received source and review

The assigned response was received through the existing Git path watch,
without another request or a new chat:

- Commit: `ff52205538b09b9c10a0993a9f660ddbe6af8845`.
- Path: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_FINITEPREFIX_2026-09-16.md`.
- SHA256: `75fd001c35880d185e5b2e14948f57ffe8fbd9e888613dce24cd8c091f8adb9c`.
- Exact payload: 53549 bytes, 660 LF, UTF-8.
- Request: `REQ-2026-09-16-FINITEPREFIX`, request commit
  `37e6a29aff33914966bbdb8f0b21c2e3517b4bbd`.
- Independent checker: `/root/sibling5_check`; review SHA256
  `dcfe2267ca6a50f04d017f314cadbb07614dfb5e2d8b26582829f98e0d5a04c8`.

The parent read the complete response, reconstructed the density induction,
the full signed diagonal limit, both-variable continuation, and the distinction
between absolute and relative convergence. The independent checker accepted
the same exact bytes. This is analytic PAPER acceptance, without Lean or a
numerical substitute. The raw response is preserved unchanged.

## What has been proved

Use the original full density r of
T=sum Gamma(2,1)/(pi n^2), mu=pi/3, and H with density
lambda^(-1/2)-1 on (0,1). The original finite renewal law S_m has density q_m.
For every fixed integer m>=1,

    q_m(t)/r(t) ~ c_m (log t)^(m-1),
    c_m=2^(m-1)/(m-1)!,                 t -> infinity.

This is one induction, not a collection of small-depth checks. Source
equations F10--F13 also give a full majorant with finite recursively specified
constants for each m. Nothing is asserted uniformly in m.

The mechanism can be verified directly. Write rho(t)=exp(pi t)r(t). The
entire square-rate product gives

    0 <= 4pi^2 t-rho(t) <= 6pi.

If beta_m(t)=exp(pi t)v_m(t), where v_m is the density of H S_m, then

    t beta_m(t)/(log t)^(m-1) -> 2c_m.

For A_m(t)=integral_0^t beta_m and D_m(t)=integral_0^t u beta_m(u)du,

    exp(pi t)q_(m+1)(t)
      =4pi^2(t A_m(t)-D_m(t))-E_m(t),
    0 <= E_m(t) <= 6pi A_m(t).

Here A_m(t)/(log t)^m -> 2c_m/m, while D_m and E_m vanish after the
required normalization. Thus c_(m+1)=2c_m/m. Both convolution endpoints
and the complete source error remain in this argument.

For the unchanged cutoff-aware prefix kernel K_m, the exact diagonal is

    K_m(x,x)=mu/(2A^2) a integral_a^infinity
       sqrt(u) r(u)^2 [q_m(u/a)/r(u/a)] log(u) du,
    a=exp(2x), A=||Phi||_2.

After dividing by a(log(1/a))^(m-1), its limit is mu c_m J/(2A^2), where

    J=integral_1^infinity (u^(1/2)-u^(5/2)) r(u)^2 log(u)du < 0.

This sign uses exact theta reciprocity. Full domination at zero and infinity
precedes the limit; the cutoff has not been dropped inside an equality.
Joint holomorphy and the accepted all-rank propagation lemma then imply:

> For each fixed m>=1 and every nonempty negative open interval J0, there
> are finitely many nodes in J0 and real, hence admissible complex,
> coefficients for which K_m[c]<0.

This includes the original interval I=(-log(2)/2,0). There is no claimed
rank bound, explicit in-I witness, or common witness across all m.

## Why this does not decide V

The full form is the limit for each fixed original row. Its exact finite-depth
multiplier is

    theta_m(t)=mu q_m(t)/(t r(t)),
    K_m[c]=2 Re integral_0^infinity
       theta_m(exp(2X)) conjugate(P_c(X)) Q_c(X)dX.

The terminal size-biased density is q_infinity(t)=t r(t)/mu, so its multiplier
is exactly one. At fixed t the multipliers tend to one, whereas at fixed m
they tend to zero as t tends to infinity. The response proves both statements;
it does not interchange the limits. Even uniform absolute density convergence
does not give a uniform relative bound after division by the tiny t r(t).

On the terminal diagonal the corresponding full-line Mellin integral cancels
exactly, leaving a positive boundary tail. Mixed finite families still require
their own joint sign proof. A negative K_m row does not decide that sign:
the row may depend on m, and the remaining telescope may compensate it.

## Consequence for the research route

The excluded claim is precisely

    exists fixed m>=1: K_m is PSD on every finite original row.

Increasing a fixed initial prefix cannot establish it. The general-m audit
and the earlier K2 pilot are one construction-level exclusion; they are not
m independent failed approaches, and do not reset a full-sign progress counter.

The useful retained data are the exact source recursion, the fixed-depth
tail law, and the explicit failure of uniform relative convergence. None is
a new lower bound for V. In particular, convergence of the telescope cannot
be used as a sign theorem.

The original full-sign consumer is unchanged. Reopening a renewal positivity
route requires an independently justified inequality for the complete signed
mean pair (with its physical cutoff and mixed terms), or a genuinely different
block construction with stated hypotheses. Neither is supplied here.

The arithmetic used in this exclusion is the full square-rate product and
theta reciprocity. Unique factorization into primes is not used to obtain
the sign. No claim of a new prime-specific mechanism is made.

The native goal remains active. The next bounded local check concerns the
entire K2 leading interaction matrix and its compensation by the remaining
telescope; until separately reviewed, it is not an accepted additional result.
