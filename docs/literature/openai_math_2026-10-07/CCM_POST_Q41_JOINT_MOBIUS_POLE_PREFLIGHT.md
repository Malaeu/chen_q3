# Post-Q41: joint short-Mobius pole cancellation preflight

2026-10-26. Bounded independent q32_annulus_audit PASS for fixed U,K. Original full-P goal
unchanged. This checks the full alternating channels before any norm.
It does not supply a favorable arithmetic inequality or source no-go.

## Exact joint transform and the cutoff

Fix integers U,K for this algebraic calculation. Put
 M_U(s)=sum_{d<=U}mu(d)d^{-s}, Y(s)=1-zeta(s)M_U(s).
On Re(s)>1 the absolutely convergent Dirichlet series of the full Q41
alternating expansion is
 B_UK(s)=sum_{j=1}^K (-1)^{j-1}binom(K,j)M_U(s)^j zeta(s)^{j-1}(-zeta'(s))
        =(-zeta'(s)/zeta(s))[1-Y(s)^K].
The missing coefficient series is
 R_UK(s)=(-zeta'(s)/zeta(s))Y(s)^K,
so B_UK+R_UK=-zeta'/zeta exactly. All actual mu and prime powers remain.
This is Q41's coefficient identity under an absolutely convergent transform,
not a new infinite-series approximation to the finite physical source.

The remainder coefficients Lambda*y_U^{*K} have support n>=(U+1)^K.
For U=floor(m^epsilon),K=ceil(1/epsilon), they vanish through m. Thus
sum_{n<=m}b_UK(n)h(n)=sum_{n<=m}Lambda(n)h(n) exactly on original P.
No terms with n>m are inserted into that physical equality. Both times,
all mixed entries and original hyperbolic cutoffs remain unchanged.

## Does binomial recombination remove growing moments automatically?

Let t=s-1 and a=M_U(1). For FIXED U,K with a!=0,
zeta(1+t)=1/t+O(1), -zeta'/zeta(1+t)=1/t+O(1).
Therefore
 B_UK(1+t)=(-1)^{K+1}a^K t^{-(K+1)}+O_{U,K}(t^{-K}),
 R_UK(1+t)=(-1)^K a^K t^{-(K+1)}+O_{U,K}(t^{-K}).
The full alternating short expansion has NOT cancelled the highest pole.
The complete coefficient series cancels it only after R_UK is included.
Example U=2,K=3: a=1/2, the two fourth-order coefficients are +1/8,-1/8.
For m<27 the latter remainder has zero physical support through m. This
finite algebra control is not a production epsilon schedule.

No uniform asymptotic in moving U is inferred from fixed-U Laurent notation.
No lower bound for |M_U(1)| on the production schedule is assumed. Exact
rational controls U=1..64,K=1..8 verified the leading polynomial coefficient
(512 cases); they do not prove a global nonvanishing or source-size claim.

## Why a physically absent tail cannot be dropped from a contour argument

The finite source sum_{n<=m}Lambda(n)n^{-s} is entire in s. Artificial poles
belong to the infinite channel representations, not this finite polynomial.
One may use B_UK inside a legitimate inversion formula, but every truncation
edge and contour term must then be carried. One may alternatively recombine
B_UK+R_UK globally before inversion; that returns the old -zeta'/zeta source.
The fact that R_UK's causal action vanishes before log m does NOT authorize
throwing away its contour residues separately. Those residues and the other
inversion terms must cancel in that zero causal action.

This is the specific failure of automatic finite-rank moment cancellation.
It is NOT a theorem that joint finite-cutoff cancellation is impossible.
The unknown useful inequality would have to control the complete finite
signed return, including the terms enforcing that cutoff. No such inequality
is obtained by the binomial identity or its leading Laurent coefficient.

## Full budget and decision

The actual finite matrix remains A exactly: new substitution error zero.
Keep A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
T_gtR<=(s_keep+b_div)P, PK_mP>=-(s_keep+50L+8)P.
If using Q32 N_star instead, its prior r_star=O_epsilon(m^{2epsilon}) is
charged once; no new channelwise r_star or pole-price is introduced here.
No exponent or coefficient margin gained. This is the second own bounded
preflight after Q41; duplicate screens are not additional failed attempts.
No Q42 sent, no new external theorem/Lean/Arb/spectrum run. Goal OPEN.

Saved finite controls: q41_postflight/joint_pole_controls.json (512 exact
rational cases, SHA256 acfd24390a9a16e660a57cbe281ab78ffc194b7bc81d5b0f8dba41e696847e0b).
