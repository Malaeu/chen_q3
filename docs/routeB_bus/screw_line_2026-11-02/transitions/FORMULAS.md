# Atom transitions and formal inverse-kernel slopes

DIAGNOSTIC_NEVER_A_PROOF. Route B remains CHALLENGER / NOT_RH.

Three different objects are kept separate:

1. The arithmetic atomic weight `w_n=b(n)/sqrt(n)`. For zeta this is
   `Lambda(n)/sqrt(n)` and has prime-power support. The separate primary-source
   audit confirms Suzuki's `g=-q_source[1_[0,t]]/2`: the arithmetic hinge is
   `+w_n (t-log n)_+`, so `jump g_prime=+w_n`. A jump in its derivative is
   not a jump in the continuous screw function itself. See
   `source_audit/SOURCE_AUDIT.md`, Suzuki arXiv:2206.03682v4 (1.1),(1.8)
   and arXiv:2209.04658v3 (1.1). There is no missing factor2 or2pi.
2. The fixed-N local source derivative at `L=log(n)`, with
   `L_tau=L exp(tau)` and the SAME active zero set on both sides.
3. The discrete differences of saved kernels as integer `m` changes on
   `N=m,L=log(m)`. These also change the carrier and sometimes its active head.

From the pinned finite-source Rellich endpoint calculation,

    dot A_plus - dot A_minus = -2 w_n L d_b d_b^*.

Here dot is `d/dtau=L d/dL`, and `d_b=(1,sqrt(2),...,sqrt(2))/sqrt(L)` is
the physical endpoint row. The matrix A is continuous at the birth atom;
this is a jump of its first derivative. The corresponding coefficient for
`d/dL` is `-2 w_n`, without the extra L.

For the formal inverse kernel at one fixed point z, define

    t_z=U^* e_z,
    K_z=t_z^* G^(-1)t_z,
    v_z=U G^(-1)t_z,
    h_z=d_b^* v_z,
    r_proxy(z)=1/(eta K_z),  eta=Im(z)>0.

Physical cosine evaluation and Fourier evaluation are separate e_z choices.
No source transfer identifying either with an actual de Branges/Weyl kernel
is asserted by this calculation. The formula requires invertible G. The last
quantity additionally requires nonzero K_z; an indefinite G is not a Hilbert
RKHS merely because these algebraic expressions can be evaluated.

At a threshold with constant active rows/rank, the one-sided differences of
`dot U`, the evaluation row derivative, and the endpoint row derivative are
zero. Thus the ordinary inverse-derivative formula gives the local slope kicks

    jump dot K_z = 2 w_n L |h_z|^2,

    jump dot r_proxy(z)
      = -2 w_n L |h_z|^2/(eta K_z^2),  K_z != 0.

The derivative in L has these same formulas divided by L. A nonzero
endpoint-kernel coupling is needed for a STRICT sign. For zeta the local
K-slope kicks are nonnegative and the formal r-slope kicks nonpositive;
zero coupling gives a zero kick. These weak signs are finite rank-one algebra,
not an Euler-product proof or a statement about discrete m monotonicity.
DH changes both signs because its b(n) has both signs, and has additional
births away from prime powers.

For the endpoint self-kernel only, `h_b=K_b`, so the radius slope kick reduces
to `-2 w_n L/eta`. That simplification MUST NOT be used for a general z.

## Coefficient table controls

`atom_table.py` computes the log-Dirichlet coefficients before differentiation.
Writing `u=D-1`, the coefficient of n^(-s) in
`log(D)=sum_(k>=1)(-1)^(k+1)u^(star k)/k` is a rational polynomial in tau.
For n<=240, at most seven factors occur. Hence

    b_D(n)=log(n) * B_n(tau)

with exact rational coefficients. The polynomial is reduced modulo
`tau^4+2tau^3-6tau^2-2tau+1`. Exact zero is determined before the 100-dps sign
evaluation, so cancellation residuals are not misclassified as tiny atoms.
The resulting weights are independently checked against the unchanged source
recurrence. In particular b_D(3)=-tau log(3),
b_D(6)=(1+tau^2)log(6), and all coefficients at multiples of 5 vanish.

All 54 prime powers in m=20,...,240 are listed separately. The full table
also retains all 167 non-prime powers; 75 have nonzero DH coefficients.
The normalized arithmetic weights and the physical source rank-one slope
coefficients are both present, with their derivative variable labeled.

The joined kernel table uses the kernel worker's saved K_z and
h_z at z=i/2,i,2i, retaining undefined/indefinite/zero-consistent states. Its
discrete differences are observations on the nonnested diagonal schedule;
they are never substituted for the one-sided fixed-N formulas above.
