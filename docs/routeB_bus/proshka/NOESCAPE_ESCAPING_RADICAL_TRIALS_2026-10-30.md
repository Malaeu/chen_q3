# Escaping near-null trials inside the literal CCM family

Status: BOUNDED PAPER OWN, independently reviewed without material findings. This concerns TRIAL
vectors, not exact bottoms. T and RH remain OPEN. No numerical evidence is used.

## Claim

There is a sequence of unit even vectors v_m in the ORIGINAL carriers
(m=N,L=logm), for all sufficiently large integers m, such that

    v_m weakly ->0,  ||A_m v_m|| ->0,  k[v_m] ->0.           (R1)

Every fixed finite theta-jet projection consequently tends to zero. The
claim is unconditional relative to the inherited literal form, radical
identity and CONFINE Fourier-return estimates. It makes no claim that any
v_m is an exact bottom.

## Fixed translates and their exact source return

Put r_a=(h(.−a)+h(.+a))/2 and s_a=r_a/||r_a||_2 for a>=1. They are even
smooth global radical tests by CONFINE(1.6), with EVERY prime power and both
poles retained. Since h is real positive,

    ||r_a||²=(||h||²+<h(.−a),h(.+a)>)/2 >=||h||²/2>0.

The translated overlap tends to zero as a->infinity. Translates of a fixed
L2 function tend weakly to zero (first test against compactly supported
functions and use their density), so s_a weakly ->0.

For each FIXED a, use the exact cutoff and Fourier projection of CONFINE§3:

    z_{m,a}=chi(x/b)s_a,  u_{m,a}=P_m z_{m,a},  b=logm/2.

Here chi=1 on[-1/2,1/2], supported inside(-3/4,3/4), even smooth, and P_m
retains exactly |n|<=m. No larger Fourier cutoff is introduced.

CONFINE(3.2)-(3.8) extend from its stated fixed derivatives to this fixed
translate without changing any estimate: every derivative of s_a has all
exponentially weighted norms and double-exponential spatial tails; constants
may depend on a. The Fourier tail and endpoint jumps obey(3.2),(3.3).
The mixed form bound(3.5) retains arch, primes<=m, and both pole norms. The
exterior bound(3.6),(3.7) retains the INFINITE prime sum, including n>m,
with finite S_Lambda=sum log(n)/n^(3/2). Radicality gives(3.8).

The only changed decay factor in the exterior tail is its constant shift a:
for x>=b/2, sufficiently large m, the slowest theta tail is bounded by a
polynomial in exp(x+a) times exp[-c_a exp(2x)], with c_a>0 fixed.
This still beats every power of m, since exp(2x)>=sqrt(m).
Therefore for each fixed a,

    ||u_{m,a}-s_a|| + ||A_m u_{m,a}|| ->0.                 (R2)

This is a form/source-residual return, not an inference from L2 density.
Its constants are NOT asserted uniform as a grows.

## Diagonal selection on the original schedule

For integer j>=2, set a=j. By(R2), choose increasing integers M_j>=j such
that for EVERY m>=M_j both errors in(R2) are <=j^(-2).
For m>=M_2 let j(m)=max{j:M_j<=m}, and set

    v_m=u_{m,j(m)}/||u_{m,j(m)}||.

The denominator is >=1-j(m)^(-2)>0. These are actual unit even vectors in
the carrier at that SAME m. Elementary normalization estimates give

    ||v_m-s_{j(m)}|| <=2j(m)^(-2),
    ||A_m v_m|| <= j(m)^(-2)/(1-j(m)^(-2)).

As j(m)->infinity, weak convergence and residual convergence follow. Finally
|k[v_m]|=|<v_m,A_m v_m>|<=||A_m v_m|| proves(R1).
No exchange of two limits or uniform translate bound has been assumed.

## What this rules out, and what it does not

There cannot be a uniform positive lower bound k[v_m]>=c>0 for ALL weakly
escaping unit trial sequences in the literal carriers. This unconditional
statement is about energy itself, not the gap above an unknown bottom. Nor can small raw residual plus
weak jet escape alone rule those sequences out. This is now a source-specific
obstruction, not only an abstract diagonal-matrix example.

If RH and the inherited even Weil positivity interface hold, then lambda_m>=0
and lambda_m<=k[v_m]->0. Consequently

    0<=k[v_m]-lambda_m<=k[v_m]->0.

Thus under that CONDITIONAL hypothesis these escaping states are additive
approximate bottoms. They need not be exact bottoms, and no relative error
on the vanishing spectral selection scale is obtained.

This sharpens the variational task: the required strict improvement must use
EXACT bottom selection or a quantitatively smaller comparison scale. A bound
valid for every state of energy o(1), every raw near-null vector, or every
additive approximate minimizer would be too strong. It does not refute T,
which concerns actual bottom vectors, and it does not supply a competitor
strictly below an actual bottom.

No new message was sent to the currently thinking Proshka. This result is
retained for comparison with the pending VARIATIONAL answer.

Independent researcher checked the same source extension and diagonal
selection; separate read-only reviewer accepted the full claim and boundaries.
Reviewed pre-status SHA256:
b2ef91179230f30f0f0913f211b750f397413077d7c2e5fe47cdd6279175a3e5.
