# PICKVAR intake: an eventual full-source variance comparison

Status: ACCEPTED_LIMITED_PAPER; independent response and intake review complete.
Producer commit: f36545c687d045851e8970cb13d7d4e0fd37217b.
Response: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_PICKVAR_2026-09-17.md.
Response SHA256: 3f7a04a92554c36da91c0df87b3ad9345baf9e5b13c029f03df8c1e3c18c5f7a.
Request: REQ-2026-09-17-PICKVAR, request commit
5acb582bf195140b785e35da1d511a7195135709, exact TXT SHA256
e83b6701f8d5337556525ffb03f2919feec73186c234259a9fa0398995697958.
Isolated analytic research; canonical production remains HOLD.

## Exact result and remaining scope

The same full source q=Phi/xi(1/2), rho(s)=q(sqrt(s)), and two normalized
laws proportional to s^(u-1/2)rho(s) and s^(u-1/2)(-rho'(s)) are retained.
Let Delta(u)=Var_D,u(log s)-Var_N,u(log s). No physical V normalization,
cutoff or finite-complex-family quantifier is changed.

Write c=9/4 and let a(nu)>0 be the unique solution of

    nu=a(pi exp(a)-c).

Producer PV19 fixes finite C,K from Gaussian integrals and an absolutely
convergent full-theta constant C_H; no sign premise enters their definition.
Set, exactly as PV25,

    a*=100+2log(1+C+K+C_H),
    nu*=a*(pi exp(a*)-c), U*=(nu*+1)/2.

The independently accepted claim is, for every real u>=U*, with a=a(2u+1),

    (1-3/a)/u^2 <= Delta(u) <= (1-1/a)/u^2 < 1/u^2,
    Delta(u) >= 1/(2u^2) > 0,
    lim_(u->infinity) a(2u+1)(1-u^2 Delta(u))=2,
    a(2u+1)~log u.

This is a continuum of arbitrarily large parameters, not a finite test.
U* is an explicit finite analytic expression, not a numerical cutoff or a
claim that the remaining region is computationally small. Neither side of
VAR is settled throughout 0<u<U*. No actual-source VAR violation is supplied.
Even global VAR would only be a necessary condition for the sufficient
Pick entrance, not a proof of Pick, V or RH.

## Mechanism whose errors are audited

For u>1/2, and only in this raw integral domain, integration by parts gives

    N(u)=(u-1/2)D(u-1),
    Delta(u)=1/(u-1/2)^2 + integral_(u-1)^u (log D)'''(v)dv.

Thus the two variances are not subtracted after separate estimates. The
signed third central log moment of one full normalized law controls the
comparison. At u=1/2, N(1/2)=rho(0); the displayed factor is not a license
to discard that endpoint or use a divergent D integral below it.

The exact theta factorization is

    q(x)=(4pi^2/Z)exp(9x/2-pi exp(2x)) Hcal(exp(2x)),
    Hcal(t)=sum_(k>=1)(k^4-3k^2/(2pi t))exp[-pi(k^2-1)t].

Every mode is retained. PV5 bounds |Hcal(t)-1| by C_H/t on all t>=1,
and Hcal is bounded above and away from zero. This permits a saddle
estimate of the complete distribution in xi=log(2x). PV14--PV20 pay
both infinite xi tails and the complete errors of moments zero through
three. PV21 keeps the normalization, and central subtraction in PV22
changes the raw coefficient -5beta/2 to -beta. PV23 then bounds the signed
third moment directly. No derivative of an uncontrolled O remainder is used.

PV24--PV29 retain the shift correction

    B0=a[u^2/(u-1/2)^2-1]

and give a uniform squeeze for a(1-u^2 Delta) between 1 and 3. The same
controlled integral bounds give its limit 2. These are the critical proof
steps; a leading saddle asymptotic alone would not establish the sign.

## What the source did, and the stopping condition

Full reciprocity supplies evenness and the exact endpoint cancellation.
The exact double-exponential theta tail and the gap k^2-1>=3 pay the
large-parameter moment error. Additive PF-infinity is not consumed by this
proof, and no new property of primes is proved or used. The result therefore
does not establish a global positivity mechanism from PF plus reciprocity.

Before this response, VAR was unpaid for all positive u. The accepted result
removes only the eventual positive-parameter region. The first unresolved
implication remains the two simultaneous signs of the coupled full-source
comparison on 0<u<U*. This is progress for a necessary filter, with no
original-V sign delta and no source-sign counter reset.

No automatic request for the next derivative, no numerical bisection, and
no relabelled generic Pick task follows. Reopening requires a source-derived
comparison or factorization of the same coupled expression. A mere new
representation or an existence theorem whose hypothesis is Pick is not such
an input. The proposed moment numerator and quantile map in the response
are identities/candidates only; neither has a proved sign or contraction.

## Final-consumer scope recheck

The complete existing REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md was read,
SHA256 1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.
Its accepted Theorem T proves both directions between full Weil Q on all
complex compact smooth tests and V on every real finite complex family.
With the named published Weil criterion, RH reaches original full V.
Consequently the already accepted global-Pick-to-RH bridge also reaches V;
no extra source-sign premise is added afterwards. This is a dependency
recheck, not a new proof or a fresh audit of all historical primary theorems.
The premise of actual global Pick remains OPEN.

FULL_POSITIVE_AXIS_VAR: OPEN.
ACTUAL_PICK: OPEN. ORIGINAL_FULL_V: OPEN. RH: OPEN.
ORIGINAL_NEGATIVE_V_WITNESS: NONE. CANONICAL_ADMISSION: false.

## Independent acceptance and delivery

Verdict: `ACCEPT_FULL_SOURCE_EVENTUAL_PICKVAR_AND_ASYMPTOTIC_ONLY`.
Complete review SHA256: `38a4ed07ebba5f436a5cd293a9d1be663662ac2c024e8933f2f5ad0d8abfd2c2`.
Complete parent check SHA256: `2e685dff3b661111ed70ad53011855e5c58839d6974bf83866e47f70df0e0e2f`.
The paired certificate embeds both checks and binds the complete original
response bytes. The reviewer also checked this intake candidate without
strengthening its claims. Parent read the full independent review before
publishing. No proof correction was required.

Request sent exactly once in living chat 6aa52001-4094-83eb-9520-01a09f54eff2,
user turn bba91ba8-d85a-43ed-9ae4-7e28099bee73; completed response
99886c38-785f-49b4-b622-441c0757a824 matched the remote producer commit.
Native status idle, error null. The response remains unchanged.

CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET. This is an accepted result
for an eventual necessary filter only; the full analytic RH/V goal remains
active and incomplete. No source-sign counter was reset.
