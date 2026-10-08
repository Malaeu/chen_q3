# Own phase-mixing sign check while Q4 is pending

2026-10-08. This is a finite-dimensional derived identity, not an accepted
interpretation of Pro's interim reasoning. No additional message sent.

Let H be real symmetric or Hermitian, p>1, G=H_-^(p-1), and let Phi be an
average of conjugations H -> U H U*, where every U is diagonal unitary.
For F(H)=Tr H_-^p, convexity and unitary invariance give F(Phi H)<=F(H).
The supporting inequality at H, with F'(H)[E]=-p Tr(GE), gives

    Tr[G(Phi H-H)] >= (F(H)-F(Phi H))/p >=0.                  (1)

Phi preserves every diagonal entry. Thus the same inequality holds with
G replaced in its trace by G+D, D=diag((-H_jj)_+^(p-1)); the D contribution
to Phi H-H is exactly zero. This cancellation concerns this diagonal-preserving
increment only, not an arbitrary physical CCM increment.

For a Hermitian diagonal A, Gaussian diagonal-phase averaging has infinitesimal
direction -[A,[A,H]] (with variance normalization chosen accordingly).
The exact spectral-basis identity is

    Tr(G [A,[A,H]])
       = sum_(i,j) (g(lambda_i)-g(lambda_j))(lambda_i-lambda_j)
                     |A_ij|² <=0,                           (2)
    g(lambda)=(-lambda)_+^(p-1).

Here A_ij are entries in an eigenbasis of H, not in the original mode basis.
Monotonic decrease of g proves the sign, including repeated eigenvalues.
Because A is diagonal in the original mode basis, the double commutator has
zero original diagonal; the D trace remains zero.

For the actual affine path H_t=padK_m+t deltaK, suppose one decomposes

    deltaK = -alpha_t[A_t,[A_t,H_t]] + R_t, alpha_t>=0,          (3)

where A_t is diagonal in the original mode basis. Then pointwise

    -p Tr[(G_t+D_t)deltaK] <= -p Tr[(G_t+D_t)R_t].             (4)

This is a useful conditional sign, not a source estimate: (3) always defines
R_t, but only an independent upper bound on the right side of(4) could pay
the moment consumer. All physical diagonal motion lies in R_t. The old/new
interface and every prime-power term must also return to R_t unless a literal
source identity assigns them to the double-commutator term.

Sign caution: for H=B-C, (2) yields
Tr(G [A,[A,C]]) >= Tr(G [A,[A,B]]). It gives a LOWER bound for this
C-expression, not the desired upper bound for arbitrary deltaC. A negative
coefficient and a proved source matching are essential to use it in(4).

No construction or quantitative estimate of the actual source residual R_t
is supplied here. Finite dephasing contraction must not be relabelled as
contraction of the original N=m schedule. SP/RH OPEN.

Independent ccm_window_transport audit PASS for signs, factor, repeated
eigenvalues, companion cancellation and source-return scope. No actual
source residual bound established. This note is not in already-sent Q4.
