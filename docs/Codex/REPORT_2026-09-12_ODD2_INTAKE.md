# ODD2 intake — exact integrand obstruction, uniform sign open

Status: ACCEPTED_SCOPED_PAPER. Parent and sole independent checker complete.
Request: REQ-2026-09-12-ODD2.
Boundary: GOAL058_ACTUAL_THETA_UNIFORM_ODD_TWO_NODE_MINOR.
Source base: 7653a3503d20be4dba91a333ff96e5eea30c738c.
This is an isolated PAPER result; no Lean certification or canonical admission.

## Receipt

The same owner-directed mathematical chat
https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13-rh-marz-2026/c/6aa52001-4094-83eb-9520-01a09f54eff2
completed naturally. Its ODD2 response shows `23m 34s nachgedacht`, a complete
Markdown download and no Stop control. Completion was first observed at the
scheduled check near 2026-09-12T11:00Z, not continuously timed.
The actual completion timestamp is not inferred from the reasoning duration.

The UI download was read completely, all 772 lines, and copied unchanged to
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2_2026-09-12.md`.
It has 46046 bytes, 772 LF, final LF, and SHA256
`1ef47a209f86e1a99c1e83ca207637aacc5b33c73170e2ef5d244231fbacaaba`.
Request, boundary and six provenance fields agree with the dispatched request.
The producer bytes are immutable; this intake records acceptance separately.

## Parent decisive derivation

1. Write `a=pi exp(2x)` and
   `f=(4 pi^2/A)exp(9x/2-a)H(a)`,
   `H=1-3/(2a)+sum_{n>=2}(n^4-3n^2/(2a))exp(-(n^2-1)a)`.
   This factorization retains the full theta series. For a>=100, differentiating
   each tail term zero, one or two times is bounded by
   `2 n^8 exp(-(n^2-1)a)`. Uniform summability justifies those derivatives.
   From `log n<=n^2/4` and `n^2-1>=3(n-1)`, the total is at most
   `4 exp(-3a/2)<=20480/(81a^6)<=a^-4`.
   The constant 20480/81 follows exactly from the sixth exponential-series term.
   Thus `H>=1/2`, `|H'|<=2/a^2`, `|H''|<=4/a^3`.
   With `d/dx=2a d/da`,
   `p=(log f)'=9/2-2a+delta`, `p'=-4a+epsilon`, where
   `|delta|<=8/a` and `|epsilon|<=48/a+64/a^2<1`.
   The normalizer A cancels in these derivatives.

2. In the exact OD1 paired-integral formula, put
   `m=(x+y)/2`, `d=|x-y|/2` and
   `J_u=f(sqrt(u+m^2)-d)f(sqrt(u+m^2)+d)
        -f(sqrt(u+d^2)-m)f(sqrt(u+d^2)+m)`.
   The substitutions t=m+v and u=t^2-m^2, with the analogous reflected
   substitution, give `K_-(x,y)=integral_0^infinity J_u(x,y)du`.
   When the reflected lower endpoint is negative, evenness of the product
   and oddness of its factor 2t replace it by its absolute value.
   At u=0 both products equal f(x)f(y). For distinct x,y their first
   derivatives divided by f(x)f(y) are respectively
   `(p(x)+p(y))/(x+y)` and `(p(x)-p(y))/(x-y)`.
   Therefore `S=2(x p(y)-y p(x))/(x^2-y^2)`.
   On the diagonal the even product in sqrt(u) has coefficient
   `f f''-(f')^2`, while the other product has coefficient `f f'/x`.
   Thus `S(x,x)=p(x)/x-p'(x)` without a singular derivative at u=0.

3. For x1=10,x2=11 set `Cij=exp(-xi-xj)S(xi,xj)/(4pi)`.
   Since ai>=100 and |delta|,|epsilon|<=1,
   `Cii>=1-1/20-1/4000-1/400=3789/4000>9/10`.
   For the upper bound, the correction to 1 is at most
   `[-2ai/xi+11/(2xi)+1]/(4ai)<0` for xi=10,11; hence Cii<=1.
   Direct substitution gives the mixed leading term
   `(10e-11/e)/21`, with error below `2/(4pi exp(21))<1/1000`.
   The elementary bounds e>8/3 and 1/e<3/8 give
   `C12>541/504-1/1000>21/20`, with exact difference 353/15750.
   Consequently det C<=-41/400 and `(1,-1) C (1,-1)^T<=-1/10`.

4. Define `Bij(u)=exp(-xi-xj)J_u(xi,xj)/(4pi f(xi)f(xj))`.
   The diagonal even composition is C-infinity in u>=0; the mixed square-root
   arguments are strictly positive at zero. Thus B is C2 on [0,1].
   `M=max(1,max_ij max_[0,1] |Bij''|)` is finite and source-defined.
   For `u*=1/(100M)>0`, Taylor's integral remainder gives
   `|Bij(u)/u-Cij|<=1/200` for 0<u<=u*.
   Hence the diagonal of B/u lies in (179/200,201/200] and its off-diagonal
   is >=209/200. This proves det(B/u)<=-41/500 and its fixed (1,-1) value
   <=-2/25. Undoing the positive diagonal congruence gives exactly
   `det J_u<=-(41/500)(4pi u)^2 exp(42)f(10)^2f(11)^2<0`.
   For `w=(exp(-10)/f(10),-exp(-11)/f(11))`,
   `w*J_u w<=-8pi u/25` and its integral to u* is <=-4pi u*^2/25.
   An analytically specified u* suffices for this existential PAPER theorem;
   no rational-u interval computation is claimed.

5. Subtracting the two scaled Volterra equations after multiplication by the
   opposite profiles yields precisely response (33):
   `integral ka(ga(s)gb(t)-gb(s)ga(t))ds
    =ga(t)integral(kb-ka)gb(s)ds`.
   For a>b the RHS is nonnegative, as k is decreasing. Local integrability
   of k and boundedness of the profiles justify these integrals. The identity
   does not supply the integrated ODD2 determinant bound.

6. With inherited OD1 positivity, pointwise PSD2 of J_u would imply ODD2
   by pointwise comparison followed by integral Cauchy-Schwarz. It is a
   sufficient condition, not a necessary one. The exact counterexample
   therefore excludes that certificate and the analogous small-initial-interval
   certificates. The contribution after u* is still unbounded in sign.
   Negative initial contribution is not a negative full K, V or Q value.
   The identities for integrated log curvature and the double integral of the
   determinant are correct, but their right-hand sides are not proved positive.

## Independent acceptance and limits

The sole read-only checker `/root/sibling5_check` returned ACCEPT for the exact
response SHA above after checking sections 3–7. It rederived the full-series
derivative bounds, S and the rational margin, C2/Taylor interval, congruence,
fixed vector and Volterra balance. It explicitly inherited the source law,
OD1 representation and its entrywise positivity. Parent directly checked the
changes of variables and the new decisive calculations above. OC1/OC2/DN22
were not rerun. No external new theorem was needed by this result.

Accepted: POINTWISE_OD1_INTEGRAND_PSD2_REFUTED, on the exact source.
Unresolved: UNIFORM_ODD2_UNPROVED_NOT_REFUTED.
The owner no-delta count changes from 0 to 1 for
`SL20_DN20_FULL_COMPLEX_MIXED_SIGN / ODD_TWO_POSITIVE_NODES`.
The new intermediate obstruction does not reset the counter or count as a
positive sign-family theorem. Delivery and review are not additional cycles.

While ODD2 was running, the separate parent/sole-checker audit
`REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` was accepted and published at
7c8528ea477bb69694cc0d9c407ecfc485a8d510. It directly checked
`all finite V PSD iff Q>=0 on every complex C_c-infinity test`, with the named
published Weil criterion. This updates the inherited-transfer status in the
producer's older context. It does not provide V positivity, ODD2, or a counter
reset. The original ODD2 response remains unchanged.

Next exact candidate: the mixed logarithmic curvature of the fully integrated
K_-, with all integral compensation retained. Its nonnegativity is sufficient
for ODD2, not a consequence of the refuted pointwise PT2 certificate. A mere
formula for that curvature will count as no-delta.

PX_RH_CLAIM: NOT_MADE.
