# Curved compression geometry: exact metric and turning identities

Status: PAPER_PROPOSAL, not an independently audited source-sign result. The
selected Ferrers/CCM family, `m=J_P+j+2`, `N=6m-1`, original carrier and
physical boundaries remain unchanged. No result below replaces the complete
Weil compression or proves a ground-state gap.

## 1. The metric already present in the source plane

For the actual columns `B_m=(b_m,e_m)` on the rank-two tail, write

\[
R_m=B_m^*B_m>0,\qquad A_m=B_m^*K_jB_m,\qquad
t_m^{\rm sel}=R_m^{-1}B_m^*x_m.
\]

The physical norm of a coefficient vector `t` is `t* R_m t`. Thus the
unit sphere of the source plane is the ellipse `t* R_m t=1` in the
original coefficient coordinates. For `t != 0`, the exact signed Rayleigh
quotient of the unchanged `K_j` is

\[
\mathcal E_m(t)=\frac{t^*A_mt}{t^*R_mt}.
\tag{C1}
\]

This is an interpretation of the same finite form, not a replacement for
its original Euclidean-unit rank-one certificate. In particular,
`kappa_R=||R_m||_2 ||R_m^{-1}||_2` measures coordinate anisotropy at one
index; it is not a curvature tensor or a signed estimate.

Let real `t,u` obey `t^T R_m t=u^T R_m u=1` and `t^T R_m u=0`. On the
unit ellipse set `t(theta)=t cos(theta)+u sin(theta)`. Direct expansion
of (C1) gives

\[
\begin{aligned}
\mathcal E_m(t(\theta))={}&(t^TA_mt)\cos^2\theta
 +(u^TA_mu)\sin^2\theta
 +2(t^TA_mu)\sin\theta\cos\theta,\\
\mathcal E'_m(0)={}&2t^TA_mu,\\
\mathcal E''_m(0)={}&2\bigl(u^TA_mu-t^TA_mt\bigr).
\end{aligned}
\tag{C2}
\]

The subtraction of the reference quotient in the second derivative is
the precise normalization-curvature term. The unnormalized quadratic
numerator along a straight coefficient path `t+theta u` would omit it.
Positive curvature of
the unit ellipse is **not** positivity of this Hessian: the complete
source form still determines both entries in (C2). For the actual
selected direction, even `t_m^{sel} != 0` remains an activity obligation.

Equivalently, `H_m=R_m^{-1/2}A_mR_m^{-1/2}` is the same form in physical
orthonormal coordinates. If its eigenvalues satisfy `lambda_+>0>lambda_-`
and the normalized actual direction makes angle `theta_m` with its
positive eigenvector, then exactly

\[
\mathcal E_m(t_m^{sel})>0
\quad\Longleftrightarrow\quad
\lambda_+\cos^2\theta_m>|\lambda_-|\sin^2\theta_m.
\tag{C3}
\]

For `cos(theta_m) != 0`, this is equivalently
`tan^2(theta_m) < lambda_+/|lambda_-|`; the displayed version also
covers a direction exactly on the negative eigenaxis.

The eigenvalue signs, the angle of the **actual** selected vector and
the margin in (C3) are not established. Whitened coordinates do not
change signs of quadratic values, but the old strict rank-one package
in the original coefficient units cannot be declared proved by
whitening.

## 2. Bending of the source plane as the selected index changes

Embed the windowed Fourier projections in the common real Hilbert space
`L^2(R)`. Let `F=(G,G'')`, let `T_m` be the actual orthogonal projection
used for the selected Fourier carrier, and set

\[
R_\infty=F^*F,\quad
\mathsf E_m=((I-T_m)F)^*((I-T_m)F),\quad
R_m=R_\infty-\mathsf E_m.
\tag{C4}
\]

The last identity and `lambda_min(R_infty)>0`, together with
`||E_m|| -> 0`, are supplied at PAPER level by the spectral-spread
verdict. Let `S_infty=ran(F)` and `S_m=ran(T_m F)`, both two-dimensional
on the admitted tail. Their largest principal angle satisfies

\[
\sin\Theta(S_m,S_\infty)
 \le \sqrt{\frac{\|\mathsf E_m\|_2}
                       {\lambda_{\min}(R_\infty)}}.
\tag{C5}
\]

Indeed, for any unit `Fc` in `S_infty`, `||c|| <=
1/sqrt(lambda_min(R_infty))`; its distance to `S_m` is at most
`||(I-T_m)Fc||`. Taking the supremum proves (C5). This is an
**extrinsic turning bound** for the source plane. The one-parameter
index path has no intrinsic Riemann curvature tensor to insert as a new
positive scalar. Formula (C5) is not yet independently audited and is
only an `L^2` statement. The spectral-spread verdict explicitly leaves
transfer to the indefinite Weil form open.

## 3. Exact next discriminator and limit

One source-locked geometric test is to estimate the actual angle
`theta_m` in (C3), the two generalized eigenvalues of `(A_m,R_m)`, and
their changes on the selected tail, retaining the complete diagonal,
archimedean subtraction, Q5/Q6 physical edges, every prime power and
the full selected `x_m`. A proved eventual strict margin in (C3) would
give a signed Rayleigh statement on this plane; it would still need the
separate `P_m`-sector/ground-state consumer bridge. If the actual
direction leaves the positive cone on an unbounded selected set, this
would falsify that proposed signed plane statement with exact scope.

Curvature or turning alone does not decide sign: with `R=I` and
`A=diag(1,-1)`, the same unit circle contains directions with positive
and negative quotient. Thus (C2) and (C5) are geometric suppliers,
not a positive source margin, first `tau_j` sign, Schur floor or RH
claim. Do not interrupt the outstanding log-symbol-transfer request
or count this note as a new Proshka verdict.
