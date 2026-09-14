# Bessel sibling: the full theta source is outside the multiplier closure

STATUS: ACCEPTED_PAPER_EXCLUDE_SPECIFIED_BESSEL_MULTIPLIER_POINTWISE_CLOSURE.
SCOPE: one specified Bessel-base multiplier class, including real pointwise limits.
ACTUAL_V_SIGN: OPEN. IC: OPEN. ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. INCOMPLETE_NO_CONSUMABLE_TARGET: canonical edge unbound.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The Bessel spectral model and its specified positive multipliers cannot reproduce or pointwise approximate the complete source: their normalized limits extend holomorphically, whereas Phi has a flat theta cusp obstructing continuation.

## 1. Sources and the actual spectral sibling

Input brief: docs/Codex/BRIEF_2026-09-13_BESSEL_SOURCE_MATCHING.md,
SHA256 c2dce3c5b170931cd9663b70eef63fc82cdc926efdfb368bf9c0808b72ae6974.
Its complete theta source and accepted dependencies are pinned to commit
b5328d02fbf988a54ad5996f4fb826a65b50a5a3. We retain f=Phi/A and A=||Phi||_2,
distinct from Z=integral Phi. Normalization by Phi(0) below is only a test of
source matching, not replacement of either project normalization.

Two primary sources were fetched and their relevant formula pages inspected:

- Lagarias, *The Schrodinger Operator with Morse Potential on the Right Half
  Line*, arXiv:0712.3238v6 (2009), Theorem2.1, printed p8; Theorem4.1,
  pp16-17; equation(4.7), p18. [PDF](https://arxiv.org/pdf/0712.3238v6).
  327335 bytes, SHA256
  307d253d70abc7d8ef3d24355e9ab7708010bda18c7b9060a4913033c6e224be.
  Located quote, Theorem2.1: "pure discrete simple real spectrum".
  For k=0, translate u=r+log(2b): its Dirichlet operator becomes
  -d^2/dr^2+b^2 exp(2r) on r>=0. The decaying solution is proportional
  to K_(it/2)(b exp(r)), with eigenvalue t^2/4. Hence the zeros of
  K_(it/2)(b), b>0, are real in t. This is an exact model, not xi.
- Cardon, *Convolution Operators and Zeros of Entire Functions*, author PDF,
  Theorem2 and its proof pp1-2, displayed(1) p2; Theorem3 p3.
  [PDF](https://mathdept.byu.edu/cardon/papers/convolutions_and_zeros.pdf).
  207596 bytes, SHA256
  0b563044ef851f1fb73d39f0ce4fc67979258d47ff841367a8ebfde7c96c639a.
  Located quote, Theorem2: "has at least one real zero, and has only real zeros."
  For real entire G of genus0 or1 with those zero hypotheses, imaginary
  shifted sums preserve real zeros. The Bessel integral gives, in our x-scale,
  integral_R exp(-b cosh(2x)) exp(itx) dx=K_(it/2)(b).
  Multiplication by cosh(a x) takes the mean of shifts t+ia and t-ia.
  These are verified conditional mechanisms; the actual theta multiplier
  has not been supplied by either paper. The full papers were not audited.

The parent independently read the located formulae and mappings; only these
statements are imported. The obstruction proved below is our derivation, not
attributed to either paper. No bibliographical priority is claimed.

The familiar model Phi_*(x)=8pi^2 cosh(9x/2) exp(-2pi cosh(2x)) matches the
leading heat amplitude of Phi but not the source itself. Put r=exp(-2x).
The full-source bound in SOURCEENERGY gives

    Phi(x)/(4pi^2 exp(9x/2-pi/r)) = 1-3r/(2pi)+O(exp(-3pi/r)),
    Phi_*(x)/(4pi^2 exp(9x/2-pi/r)) = (1+r^(9/2))exp(-pi r)
                                                   =1-pi r+O(r^2).

The first unequal coefficient is pi-3/(2pi)>0. All n>=2 theta terms are
included in the displayed full-source remainder. This comparison alone
rejects only Phi_*, not an improved family. The next theorem addresses a family.

## 2. A boundary fact about the complete source

**Lemma.** Phi is holomorphic in S={z: |Im z|<pi/4}, but has no holomorphic
continuation to a neighborhood of z0=i*pi/4 agreeing with Phi in S.

Let Theta(u)=sum_(n in Z) exp(-pi n^2 u), Re u>0. Normal convergence and
its differentiated versions on compact subsets give, for u=exp(2z),

    Phi(z)=exp(z/2)[2u^2 Theta''(u)+3u Theta'(u)].                 (B1)

On the curve u=s+i, s>0, exp(-pi i n^2)=(-1)^n. The already accepted real
Poisson identity Theta(v)=v^(-1/2)Theta(1/v), applied at v=s and4s, gives

    Theta(s+i)=2Theta(4s)-Theta(s)
              =s^(-1/2)[Theta(1/(4s))-Theta(1/s)]
              =s^(-1/2) sum_(m in Z) exp(-pi(m+1/2)^2/s).       (B2)

This uses every term. Differentiating j times, j=0,1,2, along the real
s-parameter is valid on each compact subinterval of s>0. For 0<s<=1,
each derivative is a sum of terms bounded in absolute value by
C_j s^(-1/2-2j) times a polynomial of degree at most2j in |m+1/2|
times exp(-pi(m+1/2)^2/s). Factor out exp(-pi/(4s)); the remaining
polynomial-weighted sum is bounded by its convergent value at s=1.
Consequently

    |Theta^(j)(s+i)| <= C'_j s^(-1/2-2j) exp(-pi/(4s)).         (B3)

Define z(s)=Log(s+i)/2 with the principal logarithm. It belongs to S,
approaches z0, and |z(s)-z0|/s ->1/2. All coefficients in (B1) stay bounded
on this curve for 0<s<=1. Thus

    |Phi(z(s))| <= C s^(-9/2) exp(-pi/(4s))=O(s^N)             (B4)

for every positive integer N. If a holomorphic continuation existed, its
Taylor series at z0 either would have a first nonzero coefficient, violating
(B4), or would vanish identically nearby. In the latter case the identity
theorem on the connected strip S would give Phi=0, contrary to Phi(0)>0.
This proves the lemma. It asserts a singular boundary point, not a classification
of the whole boundary as a natural boundary.

This is a statement about the source variable z. It is fully compatible with
the Fourier/Mellin transform xi being entire in its own spectral variable.

## 3. Exact named class and its closure obstruction

Define a normalized entire multiplier by

    L(z)=exp(beta z^2) product_j (1+alpha_j z^2),
    beta>=0, alpha_j>=0, sum_j alpha_j<infinity.                (B5)

The product may be finite or empty. These conditions imply locally uniform
convergence on the whole complex plane and L(0)=1, L(x)>=1 for real x.
This explicitly defined class contains cosh(a z), via its product over zeros,
and positive Gaussian factors. It is the usual even imaginary-axis
Laguerre-Polya multiplier form with value1 at zero. We do not assume that an
arbitrary positive function, positive sum of multipliers, or other spectral
model belongs to this class.

**Theorem.** There is no sequence

    k_N(x)=C_N exp(-b_N cosh(2x)) L_N(x), C_N>0, b_N>0,        (B6)

with each L_N satisfying (B5), such that k_N(x)->Phi(x) at EVERY real x.
In particular there is no exact representation of Phi in (B6). This conclusion
allows every parameter and every number of factors to vary with N.

**Proof.** Suppose such convergence holds. Since Phi(0)>0, the normalized
functions h_N(x)=k_N(x)/k_N(0) converge to h(x)=Phi(x)/Phi(0)>0. They obey

    h_N(x)=exp(-b_N(cosh(2x)-1))L_N(x).                       (B7)

For every alpha>=0,

    log(1+4alpha)-4log(1+alpha)<=0,

because (1+alpha)^4>=1+4alpha. Gaussian terms cancel in
log L_N(2)-4log L_N(1); convergent sums of the displayed inequalities give
that this difference is nonpositive. Set D=cosh(4)-4cosh(2)+3
=2(cosh(2)-1)^2>0. Then

    log h_N(2)-4log h_N(1)<=-b_N D.                          (B8)

The left side converges to a finite real number. Hence b_N is bounded above.
Pass to a subsequence with b_N->b_*>=0. Equation(B7) at x=1 now bounds
L_N(1) above by some constant K>=1.

For |z|<=R, set q=max(1,R^2). The inequality
1+alpha R^2 <=(1+alpha)^q (Bernoulli for R>=1, monotonicity for R<=1)
and beta R^2<=q beta imply

    |L_N(z)| <= L_N(1)^q <= K^q.                             (B9)

These bounds include the entire infinite product. Montel's theorem supplies
a further subsequence converging locally uniformly on C to an entire L_*,
with L_*(0)=1. Pointwise real convergence in(B7) identifies, at every real x,

    L_*(x)=h(x)exp(b_*(cosh(2x)-1)).                          (B10)

Thus Phi(0)exp(-b_*(cosh(2z)-1))L_*(z) is an entire extension of Phi from
the real line. The identity theorem identifies it with Phi on S, contradicting
the boundary lemma. No such sequence exists.

Neither the proof nor its hypothesis uses xi zeros. It excludes pointwise
real source matching, which is a weaker requirement than many usual kernel
approximation schemes. It does NOT exclude convergence of Fourier transforms
alone when source kernels lack pointwise convergence; nor does it exclude
varying cosh scales, signed combinations, nonmultiplicative constructions,
all Morse potentials, or general positive Hamiltonians.

## 4. Controls, evidence and stopping boundary

The accepted negative controls g_a=exp(a x^2)f, a<0, have the same obstruction
to holomorphic continuation: multiplication by a nonvanishing entire function
cannot remove it. They too are excluded from this source-matching class.
This is therefore a failure of the proposed supplier for both source and
controls, not a new source discriminator proving positivity of V.

Three new registered shelf queries returned exit2 and INCOMPLETE due to
semantic-index freshness, not mathematical absence. Their retained combined
stdout/stderr SHA256 values are:

    spectral: ec4593badd8e23f01ebf98c6db54ad7497024423b5859385eca9a63e732c303a
    special:  3150155953b23457d9ab0566eb33b9b972d35a49e1229e0bb8f452597c330d60
    physics:  1810261125da8f47a836687ce4b3213d76ffa1c651699ecfb6801488708ae8d9

Prior Lee-Yang/Villain and de Branges reports were reconciled; they supplied
no exact Bessel multiplier for Phi. Two primary sources were then read within
the brief's bound. Local source PDFs, rendered pages and the selection record
remain in the parent artifact directory; they are not redistributed here.
No theta evaluation, numerical zero search, quadrature, rank sweep or Lean
run was used. Sole independent checker sibling5_check accepted the full analytic
proof. Exact reviewed hashes and the retained receipt are recorded in the owned
PROSHKA_QUEUE.md; this is PAPER acceptance, not canonical admission.

This accepted result completes ONE further attempt without an actual source-sign
supplier: history8->9, latest owner resumption2->3, applied on this intake.
Search, manuscript, review and delivery are parts of that one attempt.
The owner's three-repeat brainstorm boundary then applies before another
proof construction. No new substantive Pro proof request is commissioned by
this report. Full V, IC/ODD2 and RH remain open; no negative V witness is given.
