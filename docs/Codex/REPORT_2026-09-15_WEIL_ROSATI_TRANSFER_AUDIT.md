# Exact audit: source inversion is not a positive Rosati pairing

Date: 2026-09-15. Status: PAPER candidate, bounded transfer audit.
Verdict: DIRECT_SOURCE_INVERSION_ROSATI_TRANSFER_REJECTED.
This excludes the explicit identifications below. It does not exclude another
source-built algebra, disprove RH, or give a negative row of V.

## Source and target pins

Source base: `dac86ef60da246f5abf61c93b724a15fb6950537` on
`codex_mac/gamma-reciprocity-20260914` in Malaeu/chen_q3.
Read source reports: `docs/Codex/REPORT_2026-09-15_RH_ROUTE_AUDIT.md`,
`REPORT_2026-09-12_THETA_TN_INFINITY_INTAKE.md`, and
`REPORT_2026-09-14_EXACT_RECIPROCAL_PAIRING.md` in the same directory.
The two proved inputs are used in their actual domains:

* A: the additive translation kernel r(u-v), with r extended by zero to
  negative arguments, is totally nonnegative of every order.
* B: r(1/t)=t^(5/2)r(t), t>0.

Here r is the full positive source density, not a finite approximation.
Its established tails give all exponential moments in X=(log t)/2.
The exact source correspondence is r(t)=t^(-5/4)Phi((log t)/2).
Set Z=integral_R Phi(x)dx and m=M_r(5/4)=2Z. Then

    dnu(t)=t^(1/4)r(t)dt/m,
    X(t)=(log t)/2,
    law_nu(X)=rho(x)dx=Phi(x)dx/Z,
    phi(z)=E_nu exp(-izX)=F(z)/F(0).

This audit tests whether A and B directly supply Weil's positive involution.
It makes no production consumer admission: INCOMPLETE_NO_CONSUMABLE_TARGET.
V remains parked; no goal, phase, or counter is reset.

## 1. What the finite-field theorem actually uses

Primary source: J. S. Milne, *The Riemann Hypothesis over Finite Fields*,
https://www.jmilne.org/math/xnotes/pRH.pdf, printed pp. 21-23,
Theorem 1.27, Corollary 1.29, Theorem 1.30 and summary 1.31.
The reviewed theorem acts on the endomorphism algebra of an abelian variety:
a polarization supplies a Rosati involution with positive trace pairing.
For Frobenius pi, the identity pi^dagger pi=q then forces all its complex
conjugates to have absolute value sqrt(q). The curve zeta numerator encodes
these eigenvalues. Both positivity and that spectral identification matter.
This is not a claim about an arbitrarily chosen positive Hilbert norm on a
Tate module. A bare reciprocal symmetry does not satisfy these hypotheses.

Two short verified source phrases: Theorem 1.27 says the pairing
"is positive definite." Corollary 1.29 identifies the involution
"as complex conjugation on the complex factors."
The web extraction actually read is archived ephemerally as
`langlands-route-check-20260915/milne-rosati-web-extract.txt`, 19056 bytes,
SHA256 `7c9d378a81a420d496b6e1cd84401836da04efab566360980d1d30c7dce51a33`.
This hashes the extraction, not original PDF bytes; only the cited portion
was checked for this audit.

## 2. Exact source inversion: an isometry with a negative reflected form

By B, inversion preserves nu, since its transformed density is

    t^(-1/4) r(1/t) t^(-2) / m = t^(1/4)r(t)/m.

On H=L2(nu), use the inner product conjugate-linear in the first argument.
Define Jg(t)=g(1/t). Thus J*=J, J^2=I and ||Jg||=||g||.
All of these properties are proved, but they do not make

    B_J(g,h)=<g,Jh>

positive. Write g=g_+ + g_- with Jg_+=g_+, Jg_-=-g_-. Orthogonality gives

    B_J(g,g)=||g_+||^2-||g_-||^2.

For the actual source, X belongs to H, JX=-X and
mu2=E_nu X^2>0. Consequently

    B_J(X,X)=-mu2<0.

This is an exact counterexample to positivity of B_J, not of V.
Multiplication by a positive constant cannot fix this sign. Restriction to
the even subspace makes J the identity, but no target-preserving spectral
identification on that restriction has been supplied.

The operator-algebra version fails just as explicitly. On finite-rank
operators try A^dagger=J A* J. This is an involution reversing products.
Put u=1, v=X/sqrt(mu2). These are orthonormal and Ju=u, Jv=-v.
For A(w)=u<v,w>, A*(w)=v<u,w>, so A^dagger=-A* and

    Tr(A A^dagger)=-1.

No unbounded operator or trace-domain assumption is involved. Thus this
particular source-induced involution is not a positive Rosati involution.

## 3. Total nonnegativity does not make the translation table Hermitian

The continuous extension has r(0)=0: inversion B and the full large-t tail
give this limit. For d>0 and ordered nodes 0,d, the table is

    K = [[0,0],[r(d),0]].

Its ordered minors are nonnegative, consistently with A. Its Hermitian part
S=(K+K*)/2 instead has off-diagonal entries r(d)/2 and zero diagonal. For
c=(1,-1), c*Sc=-r(d)<0. The raw TN table cannot be identified with a positive
Hermitian form. This is not a refutation of A and again is not a V-row.

## 4. A positive Hilbert realization already exists, with a different role

Multiplication M_X by the real function X is self-adjoint on its maximal
natural domain. For real u, U(u)g=exp(-iuX)g is unitary and

    phi(u)=<1,U(u)1>.

The scalar coefficient extends to an entire function by exponential moment
bounds. We do not assert that exp(-iz M_X) is a bounded operator for every
complex z. More importantly, phi is a matrix coefficient, not a spectral
determinant whose zeros are the spectral values of M_X. Self-adjointness
alone cannot impose real zeros on this coefficient.

An exact control shows the difference. The positive even density proportional
to g0(x)=exp(-x^2)-(1/4)exp(-2x^2) has the same elementary unitary realization.
Its unnormalized entire Fourier transform is

    G0(z)=sqrt(pi)[exp(-z^2/4)-(1/(4sqrt(2)))exp(-z^2/8)].

Its zeros satisfy

    z^2=8 log(4sqrt(2))-16 pi i k,  k in Z.

For k nonzero these zeros are off the real axis. This control is not asserted
to have additive TN infinity; it does not refute A+B jointly. It refutes the
inference from a positive density, reflection symmetry and an ordinary
unitary coefficient representation to a real-zero theorem.

## 5. Result and route decision

The attempted direct transfer fails at named, testable identifications:
inversion is not a positive reflected pairing; the TN table is not a positive
Hermitian table; a unitary matrix coefficient is not a spectral determinant.
These are structural failures with exact examples, not estimates of another
uncomputed tail. Other source-built constructions remain untested.

For a new Weil-style candidate, require in the same construction (i) a proved
positive duality on its actual algebra and (ii) an exact correspondence to
zeros of the full F. These are obligations for a proposed candidate, not new
axioms claimed sufficient by themselves. A name from Langlands or the
existence of an unrelated positive norm cannot replace either verification.

AUTOPSY: dropped=COUPLING; note=The source involution is isometric but its reflected pairing and induced trace pairing are negative on explicit source-built test objects; no positive-duality transfer was obtained.

One bounded audit is complete. No RH theorem, negative V witness, full
source-sign inequality, or claim that all uses of A+B fail is made here.
