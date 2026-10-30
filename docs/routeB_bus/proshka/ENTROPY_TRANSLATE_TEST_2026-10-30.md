# Can a weaker global LSI survive? Translated-radical test

Status: bounded independent PAPER check of the leading obstruction. Inherited inputs:
CONFINE (1.2), (1.5)-(1.6) and MARKOV (6.4)-(6.8). No RH premise.
Do not send a new message while ENTROPY is running.

## Proposed conclusion

There is no finite C such that Ent_mu(F²)<=C E_h(F) for every real even
smooth compactly supported F. This is stronger than the sharp-constant cubic
obstruction, but still excludes only this global logarithmic Sobolev supplier.
It does not exclude a localized or bottom-specific entropy inequality, anchored KL on
the particular bottoms, or the Poincare inequality. It does not prove RH.

## An exact family at energy quotient8

Set a_*=(log2)/2. For 0<a<a_* define

    h_a(x)=(h(x-a)+h(x+a))/2, q_a=h_a/h,
    r=exp(-2a), delta=2r-1>0.

Both h and h_a are positive even smooth functions; h_a is a global radical
test by CONFINE (1.6). The measure is dmu=cosh(x/2)h(x)dx/2.
Translation and parity give E_mu q_a=cosh(a/2). The compact cutoffs justified below give the limiting energy

    E_a:=lim_R E_h(chi_R q_a)=8(M(a)-cosh(a/2)^2), M(a)=E_mu q_a².

Thus the energy/second-moment ratio tends to8 when M(a) diverges.

## Uniform theta asymptotics and entropy cost

Write t=exp(2x) and A=16pi². As x->+infinity,

    h(x)=A exp(9x/2)exp(-pi t)(1+O(t^-1)),
    h_a(x)=(A/2)exp(9(x-a)/2)exp(-pi r t)(1+O(t^-1)).

The latter estimate is uniform for a in [a_*/2,a_*]. The translated-away
summand is exponentially smaller there, and the higher theta summands are
uniformly exponentially smaller than n=1. Consequently

    q_a²=(1/4)exp(-9a)exp(2pi(1-r)t)(1+O(t^-1)),
    log(q_a²)=2pi(1-r)t-9a-log4+O(t^-1).

After combining the two equal half-lines, the measure q_a²dmu on large t is

    pi² exp(-9a) t^(3/2)exp(-pi delta t)(1+O(t^-1/2)) dt.

The t^-1/2 error includes the second cosh term. On any fixed compact x
interval, the integrals remain uniformly bounded as a approaches a_*.
Integrating this asymptotic with gamma integrals therefore gives

    M(a) ~ (3/4)exp(-9a) delta^(-5/2),
    [int t q_a²dmu]/M(a) ~ 5/(2pi delta),
    Ent_mu(q_a²)/M(a) = [5(1-r)/delta](1+o(1))-log M(a)+O(1).

Here the auxiliary t in the middle integral is exp(2|x|) on the full line.
In particular delta log M(a)->0 and

    delta Ent_mu(q_a²)/E_a -> 5/16.

The ratio Ent/E diverges. Gamma integral use is elementary: for k>-1,
int_0^infinity t^k exp(-pi delta t)dt=Gamma(k+1)/(pi delta)^(k+1).
Uniform O(t^-1/2) errors are smaller by O(sqrt(delta)); any fixed lower
cutoff changes these asymptotics by a bounded term.

## Short compact-test passage: no noncompact energy realization needed

Fix a<a_* first. The displayed theta asymptotics imply q_a in L2(mu)
and q_a² log(q_a²) in L1(mu). L3(mu) can fail and is not used.
Choose standard scaled even smooth cutoffs chi_R(x)=chi(x/R), equal1 on
[-R,R], zero outside[-2R,2R], bounded between0 and1. Set F_R=chi_R q_a.
These are actual even smooth compact tests, and hF_R=chi_R h_a.

Apply the already proved compact identity MARKOV (6.8) directly:

    E_h(F_R)=8 Var_mu(F_R)+k[chi_R h_a].

No term has been omitted: the odd tau moment vanishes by parity, while
all prime powers and both pole terms remain inside the exact identity.
Because h_a belongs to S_exp, the standard scaled cutoffs converge in
CONFINE's exponentially weighted derivative topology. Its source-form
continuity gives k[chi_R h_a]->k[h_a]=0, using radicality (1.6).
L2(mu) convergence gives Var_mu(F_R)->M(a)-cosh²(a/2). Therefore

    lim_R E_h(F_R)=8(M(a)-cosh²(a/2)).

This is a limit of energies of compact tests. We do not need to define a
self-adjoint global signed operator or independently identify E_h(q_a).
The limit is positive for a>0 since q_a is nonconstant.

For entropy, write (chi_R q_a)²log((chi_R q_a)²) as the sum of
chi_R² q_a² log(q_a²) and q_a² chi_R² log(chi_R²).
The first is dominated by q_a²|log q_a²|. The second is dominated by
q_a²/e, using |t log t|<=1/e for0<=t<=1, and tends pointwise to0.
Together with L2 convergence for its normalization term this gives
Ent_mu(F_R²)->Ent_mu(q_a²).

Thus a compact-test LSI with any fixed finite C would imply

    Ent_mu(q_a²)<=8C(M(a)-cosh²(a/2))

for every a<a_*. But the leading asymptotics prove

    lim_{a->a_*} delta *
       [lim_{R->infinity} Ent_mu(F_R²)/E_h(F_R)] = 5/16.

The ratio diverges. Choose a close enough to a_* for a strict violation,
then R large enough to preserve it. This is a compact even counterexample
family for every proposed finite global LSI constant, without a finite-cell
or cofinal RH assertion. The same ratio also excludes any global defective
bound Ent_mu(F²)<=C E_h(F)+D||F||_mu² with finite fixed C,D.

## Independent check and limits

The read-only lsi_translate_test researcher checked the theta leading term,
probability normalization, entropy passage and compact-identity energy limit.
The leading asymptotic constant5/16 agrees. A proposed sharper bounded
subleading remainder was NOT used: the t^-1/2 density correction need only
produce relative O(sqrt(delta)), which is enough for the leading limit.
This check relies on the exact inherited MARKOV/CONFINE source identities;
it is not a fresh full audit of those sources or Lean verification.

Conclusion: global LSI with any finite constant is KILLED(shape), even on
smooth compact tests. This is the same entropy branch, not a new message to
Proshka. Localized or source-bottom-specific entropy estimates remain open.
The RH goal is unchanged.

Interpretation: h_a itself converges in physical L2 to the fixed finite
translate combination h_{a_*}. The divergent entropy is caused by division
by h and the mu-weighted q_a normalization, not by physical escape of h_a.
These q_a are not identified with the literal CCM bottoms f_m. This is why
the global entropy obstruction does not refute geometric NOESCAPE.

## Non-certifying numerical sanity check

Root evaluated the actual theta quotient using six theta terms and stable
log-sum evaluation, mpmath dps35, positive half-line x in[0,5] split into
quarter intervals. No quadrature/tail enclosure was claimed or spent.

| delta | M(a) | Ent/[8Var] | delta Ent/[8Var] |
|---|---:|---:|---:|
|0.1|17.0550960386|2.2279815251|0.2227981525|
|0.03|272.1124469548|8.8942788616|0.2668283658|
|0.01|3807.3458643543|29.0232581651|0.2902325817|

The proved leading target is5/16=0.3125, not an asserted finite-delta equality.
Independent follow-up confirmed that the sequential cutoff limit needs no
new assumption and also excludes finite global C,D defective bounds. The
introductory wording was narrowed to localized/bottom-specific alternatives.
