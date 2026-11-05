# Task C: fixed-Gaussian envelope threshold

DIAG only. No finite matrices, growth fits, RH claim, or claim about (7.4).
`task_c.json` contains all 26 right-hand DH census rows and the planted quartet.

For u=delta+i*gamma, the positive-frequency pair's magnitude envelope is

    E_rho(L)=2*|F(u)|^2*exp(delta*L/2),
    log(2*|F(u)|^2)=log(2)+4*log|u|+2*log|u^2-1/4|+(delta^2-gamma^2)/2.

This is the exact factor specified by the task. The full quartet also has a
left-hand pair. An envelope crossing does not locate a negative oscillation:
its phase may have either sign. We charge the on-line magnitude sum
`A=2*sum_{gamma>0}|F(i*gamma)|^2`; taking the absolute value of the oscillatory
sum instead would define a different, phase-dependent first crossing.
The JSON also reports `log_m_star_q_target_online_envelope`: keeping the
prescribed growing amplitude unchanged but charging `4A`, the uniform
on-line envelope of the Task B target `2W[g]+2h(L/2)`. This alternative
records the normalization convention explicitly. It shifts the first DH
crossing by about 8.99 in log(m); the plant crossing is unchanged at the
displayed precision because its return-error bound dominates.
DH rows use the DH on-line census; the planted world uses the zeta on-line
zeros through height 60. Both include the explicitly stated positive tail below.

The Task B bound is used literally:

    E(L)=1e27*(1+L)*exp(3L/4-L^2/256)
         +1e27*(1+L)^4*exp(-5L/4),
    B(L)=27*E(L)*(4e5*exp(L/4)+E(L)),  L>=1.

For the planted world use 32 in place of 27: the quartet bilinear form costs
at most `4/(1-a^2)=4.5` additional weighted-norm units at a=1/3. The vector
return-error estimate E is unchanged. This bound is extremely conservative.
For DH, this is a formula comparison with the requested Task B zeta bound;
we do not claim a separate DH arithmetic-source return theorem from it.

The continuous crossing solves `E_rho(L)=A+B(L)`. It is unique in the
relevant range. Indeed, each component of E has logarithmic derivative less
than -1/4 for L>=130, so B decreases strictly there, while E_rho increases.
For 1<=L<=130, B is at least `27*(2e27)^2`, far above every candidate pair
amplitude on that interval. Integer m>=3 is recovered as
`floor(exp(L_cross))+1`; the resulting change of log(m) is less than
`exp(-L_cross)`. The JSON gives the crossing and this correction upper bound,
not an impossibly large explicit integer. Values are numerical, not enclosures.

The tail estimate used is

    tail(T0)<=8*(T0+1)^10*exp(-T0^2/2), T0=60 or 900.

The bin estimate uses `N_world(T)<=T^2` for all integer T>=T0. In
[k,k+1), bound the pair weights by `4*(k+1)^8*exp(-k^2/2)`, the bin count by
`(k+1)^2`, and sum the resulting rapidly decreasing geometric majorant.
It charges every zero in each bin and requires no RH assumption.

For DH the following elementary count supplies the missing tail rather than
extrapolating census completeness. Put c=pi/5 and
`theta(x)=sum_{n>=1} n*a_n*exp(-c*n^2*x)`. The exact periodic coefficients
satisfy |a_n|<=1 and the conductor-5 odd self-dual completion gives

    Lambda(s)=integral_1^infinity theta(x)
              *[x^((s-1)/2)+x^(-s/2)] dx.

A nonzero constant factor relative to the census completion is irrelevant to
Jensen's formula. The identity follows from the theta transformation by
Poisson summation for the specified period-5 coefficient vector. In detail,
with `tau=(sqrt(10-2*sqrt(5))-2)/(sqrt(5)-1)`, the exact radical identities
for sin(2*pi/5) and sin(4*pi/5) verify

    (2/sqrt(5))*[[sin(2*pi/5),sin(4*pi/5)],
                 [sin(4*pi/5),-sin(2*pi/5)]] * (1,tau) = (1,tau).

The odd period-5 vector is `(0,1,tau,-tau,-1)`, with 0<tau<1. This
normalized sine-transform eigenvalue +1 is exactly the self-dual odd
conductor-5 theta transformation; no numerical functional-equation test is
being used as its proof. Since
`sum_{n>=2} n*exp(-c*(n^2-1))<1/2`
(the first term is `2*exp(-3*c)` and each successive ratio is at most
`(3/2)*exp(-5*c)`), for x>=1 we have
`exp(-cx)/2 <= theta(x) <= 3*exp(-cx)/2`. In particular
`Lambda(1/2)>exp(-10)`, already by integration over [1,2]. On the disk
centered at 1/2 of radius 2R, the half-line integral gives

    max |Lambda(s)| <= 4*c^(-R-2)*Gamma(R+2).

There are no zeros with Re(s)>=2 because
`|D(s)-1|<=zeta(2)-1<1`; reflection confines completed nontrivial zeros to
`-1<Re(s)<2`. Thus radius `R=sqrt(T^2+9/4)` covers every such zero with
|Im(s)|<=T. Jensen bounds their number by

    [log(4)+(R+2)*log(1/c)+log(Gamma(R+2))+10]/log(2).

For T>=900, elementary Stirling bounds put this below
`4*T*log(T+3)<T^2`; the ratio log(T+3)/T decreases there. This bounds the
positive-height on-line count in particular. It is deliberately far looser
than the true zero count. Zeta uses Task A's analogous count bound.

The input DH census remains `NUMERICAL_NOT_CERTIFIED` with numerical
count-match completeness, not an interval-certified enumeration. The tail
argument covers unlisted heights above 900, while the sub-900 enumeration
is inherited numerical evidence. The table is therefore labelled as DIAG
with census completeness uncertified. All 65 displayed digits coincide
with census-only thresholds; the tiny upper tail is included but below
mpmath's addition resolution at dps80. These are regime estimates, not
certified intervals for integer thresholds.

Reproduction: `python scripts/task_c.py` from any directory; default dps=80.
`--bound unavailable` emits online-only necessary lower benchmarks with null
m_star, preserving the distinction if the Task B estimate is rejected.
