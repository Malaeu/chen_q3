# Boundary Pick dictionary for answer3 matrix (2026-10-06)

## Exact project object

On one original cell (m), answer3 defines, for (-m\le j,k\le m),
\[
q_j=a(\omega_j)-d_j+r,\qquad
T_{jk}=\begin{cases}(h_j-h_k)/(\pi(j-k)),&j\ne k,\\0,&j=k,\end{cases}
\]
with (h_j=\operatorname{Im}\Phi_m(\omega_j;m)). Its open consumer is
\(S_m(r)-T_m\succeq0\), with (S_m(r)=\operatorname{diag}(q_j)), for every
\(\eta>0) on one unbounded original subfamily at (r=C_\eta m^\eta).
See `PROSHKA_JOINT_HILBERT_INLINE_2026-10-06.md` (21)–(22). The full-carrier
bound and the constant-20 archimedean budget are proved there; (21) is open.

## One primary worked source and exact map

Vladimir Bolotnikov and Alexander Kheifets, “Boundary Nevanlinna–Pick
interpolation problems for generalized Schur functions,” *Operator Theory:
Advances and Applications* 165 (2006), 67–119. Author-hosted PDF:
<https://www.math.wm.edu/~vladi/ot165.pdf>. The fetched file here is
`bolotnikov_kheifets_boundary_np.pdf`, SHA-256
`388da69d4674db9dd75c1cfab6a240f74454fcb00f0ee2a29f395ea6dce4cdae`.

Section 1, pp. 2–3, (1.5)–(1.7), proves the boundary Schur criterion: for
pairwise distinct (t_j\in\mathbb T), unimodular targets (w_j), and
nonnegative caps \(\gamma_j\), a Schur function (w) with boundary values
(w(t_j)=w_j) and angular derivatives (d_w(t_j)\le\gamma_j) exists iff its
Pick matrix (P_{jk}=(1-w_j\overline{w_k})/(1-t_j\overline{t_k})) off diagonal,
(P_{jj}=\gamma_j), is positive semidefinite.

Here is the exact Cayley map back to the project matrix. Let
\[
u_j=-h_j/\pi,\quad t_j=(j-i)/(j+i),\quad w_j=(u_j-i)/(u_j+i),\quad
c_j=(j+i)/(u_j+i),\quad \gamma_j=|c_j|^2q_j
=\frac{1+j^2}{1+u_j^2}q_j.
\]
For (q_j\ge0), the upper-half-plane kernel with real boundary data (u_j),
\[
K_{jk}=\begin{cases}(u_j-u_k)/(j-k),&j\ne k,\\q_j,&j=k,\end{cases}
\]
is exactly (S_m(r)-T_m). The two Cayley transforms give
(P=\operatorname{diag}(c_j)K\operatorname{diag}(c_j)^*\); hence (P\succeq0)
iff (S_m(r)-T_m\succeq0). The theorem therefore gives an exact equivalent
analytic phrasing: a disk Schur interpolant at those (m)-dependent boundary
values with those (m)-dependent derivative caps exists.

This is **not an independent supplier**. The interpolation theorem constructs
an interpolant from the very PSD condition being sought; it does not prove the
arithmetic matrix PSD or construct an interpolant from an independent positive
prime/pole representation. The current (h_j=\operatorname{Im}\Phi_m(\omega_j;m))
is cell-dependent, so no single global Pick property follows from the finite
interpolation statement. A noncircular route would need an explicit arithmetic
Herglotz representation or a direct construction of the interpolant plus the
caps; none was found in this bounded check.

## Negative control and status

Take (h_j=j) and constant (q_j=q\ge0). Then (T_{jk}=1/\pi) off
diagonal and (S-T=(q+1/\pi)I-(1/\pi)\mathbf1\mathbf1^*\). Its constant-vector
eigenvalue is (q-(N-1)/\pi), (N=2m+1); it is negative when (q=o(m)).
Thus pointwise nonnegative diagonal slack, including (q=Cm^\eta) for
(0<\eta<1), does not dominate a generic divided-difference matrix.

- **PROVED:** exact algebraic Cayley/Pick reformulation of the finite matrix;
  the negative-control eigenvalue calculation.
- **OPEN:** the actual arithmetic (S_m(C_\eta m^\eta)-T_m\succeq0) on an
  unbounded original subfamily, or any independent Herglotz construction
  implying it.
- **INAPPLICABLE as a supplier:** boundary Pick positivity itself; it is
  equivalent to the target matrix condition.
- **No claim:** global Pick/operator-monotone properties of this cell-dependent
  arithmetic (h_j), RH, or any theorem closure.
