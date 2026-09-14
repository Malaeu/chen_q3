# Exact test of the scalar Bessel lift

STATUS: INDEPENDENTLY_REVIEWED_ANALYTIC_OBSTRUCTION_FOR_NAMED_LIFT.
SOURCE: REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md at
65c4a563ce4319a595a17e7c264dbbd77f1672e1, SHA256
7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET.

The first finite gamma member has a positive scalar Bessel energy. Does the
same natural radial extension give a scalar spectral equation for the other
members? The exact answer below is no, even allowing any fixed power
normalization. This excludes that particular lift, not real zeros of M_N,
not a different spectral construction, and not the cofinal criterion.
The live GAMMARECIP request is not interrupted or duplicated.

## S1. The complete differential correction

Fix N>=1 and real kappa. Put, for t>0 and s,y real,

    A(t)=r_N(t)/t^kappa,
    Q(t)=t A'(t)/A(t),
    H(s,y)=sqrt(A(exp(s+y)) A(exp(s-y))),
    Psi(s,k)=integral_R H(s,y) exp(-iky)dy.

Only positive real square roots are used. The extension parameter s is real;
the spectral parameter k may be complex. At s=0,

    H(0,y)=G_N(y/2),
    Psi(0,k)=2 Z_N M_N(2k).                              (S1)

In particular the boundary function is independent of kappa.
For u=exp(s+y), v=exp(s-y), direct logarithmic differentiation gives

    (partial_s^2-partial_y^2)H=Q(u)Q(v)H.                (S2)

Indeed log H is the sum of a function of s+y and one of s-y, so its wave
operator vanishes, while (partial_s log H)^2-(partial_y log H)^2=Q(u)Q(v).
For fixed N, the finite exponential-convolution endpoint expansions used in
G6, with their derivatives, show that H and its required derivatives decay
as an exponential of -c exp(|y|), times at most exp(C|y|), locally uniformly
in s. Differentiating the integral and integrating twice in y is therefore
justified for every complex k; both y boundary terms vanish. Hence

    -Psi_ss+pi^2 exp(2s)Psi=k^2 Psi-J(s,k),              (S3)
    J(s,k)=integral_R [Q(u)Q(v)-pi^2 exp(2s)]
                         H(s,y)exp(-iky)dy.

For N=1, kappa=1, Q(t)=-pi t, J=0 and
Psi(s,k)=2pi^2 K_(ik)(pi exp(s)). This is precisely the previously proved
scalar positive-energy case. No assertion about the sign or reality of a
complex-frequency integral of J is made for other N.

## S2. No scalar potential for this natural lift when N>=2

Claim: for fixed N>=2 there are no real kappa and function P(s), s>=0,
such that the exact family Psi just defined obeys

    -Psi_ss(s,k)+P(s)Psi(s,k)=k^2 Psi(s,k)               (S4)

for every real k and every s>=0. Even allowing complex P would not help.
This is a statement about this fixed integral family and this differential
operator, not about all possible spectral representations of M_N.

Let m=2N-1 and lambda_n=pi n^2. Finite gamma convolution has, with controlled
first derivatives,

    r_N(t)=c_N t^m(1-lambda_bar t+O(t^2)) at t->0+,
    r_N(t)=d_N(t-mu_N+o(1))exp(-pi t) at t->infinity,
    lambda_bar=(1/N)sum_(n=1)^N lambda_n>pi.

The first expansion follows by integrating the product of the N shape-2
Densities on the simplex: the normalized coordinates have the Dirichlet
(2,...,2) law, whose coordinate means are 1/N. The second follows from
r_N=q_pi*law(S_N): mu_N=E[S_N exp(pi S_N)]/E[exp(pi S_N)], finite since all
rates of S_N exceed pi. The exponentially small omitted tails can be
differentiated because each finite convolution is an exponential polynomial.
Consequently,

    Q(t)=m-kappa-lambda_bar t+O(t^2) at t->0+,
    Q(t)=-pi t+1-kappa+O(1/t) at t->infinity.            (S5)

Equation (S4) and (S2), by injectivity of the Fourier transform on L1(R),
would force P(s)=Q(a exp(y))Q(a exp(-y)) for every y, where a=exp(s)>=1;
continuity and strict positivity of H remove the almost-everywhere qualifier.
At y=0 this equals Q(a)^2, a finite value.

If kappa!=m, then as y->infinity the same expression has leading term
-pi a exp(y)(m-kappa), so it is unbounded. This is impossible.
If kappa=m, then its limit as y->infinity is pi lambda_bar a^2. Thus (S4)
would require Q(a)^2=pi lambda_bar a^2 for every a>=1. But (S5) gives
Q(a)^2/a^2->pi^2 as a->infinity, whereas pi lambda_bar>pi^2.
This is again impossible. The claim is proved analytically.

A prefactor depending on s beyond the stated power normalization, a first
order differential term, a matrix/operator valued energy, or a different
extension is not excluded by this proof. Such a proposal must be constructed
and its exact boundary function verified; no positivity is supplied by its
name. In particular S2 does not prove that M_2 has a nonreal zero.

## S3. Exact semantic sibling in phase-space analysis

Let p_N(x)=2exp(2x)r_N(exp(2x)) and phi_N=sqrt(p_N). Then ||phi_N||_2=1.
Using the Wigner convention

    W(phi,phi)(q,p)=integral_R phi(q+t/2)
                              conjugate(phi(q-t/2))exp(-2pi i p t)dt,

substitution t=2x at q=0 gives the exact real-frequency identity

    W(phi_N,phi_N)(0,p)=4 Z_N M_N(4pi p).               (S6)

The right side also supplies the entire continuation in p of this slice.
Thus the reciprocal geometric operation is a central Wigner slice of the
log-density amplitude. Additive convolution of r_N is not convolution of
phi_N, and no total positivity of phi_N has been established here.

The primary paper by Groechenig, Jaming and Malinnikova, *Zeros of the Wigner
distribution and the short-time Fourier transform*, DOI
https://doi.org/10.1007/s13163-019-00335-w, equation (1), Examples 3 and 5,
and the outlook before section 4, was read for this mapping. It studies
nonvanishing on real phase space. Its explicit convolution examples do not
supply complex real-zero preservation for (S6). Example 5 uses log-gamma
amplitudes but computes the ambiguity function, not our central self-Wigner
slice. This is a scope-checked related source, NOT an admitted preserver.
Quote, outlook before section 4: "the role of totally positive functions in
the classification of zero-free ambiguity functions remains unclear."
No complete-paper audit or new theorem from that paper is claimed.

## S4. Return point

The actual extension has a nonconstant multiplication term Q(u)Q(v). After
Fourier transformation this becomes the full correction J, not a scalar
potential. The all-N/cofinal real-zero property remains the active problem.
The Wigner description gives an exact alternative description of the object,
but the read source has different zero-domain and input hypotheses.
No numerical tests, new negative theta witness, IC/ODD2 closure, canonical
admission or RH claim result from this note. The coauthor's general
preservation request remains active; S2 excludes only a narrower proof attempt.
