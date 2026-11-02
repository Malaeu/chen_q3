# Capacity-matrix normalization and interpretation

Read-only source/theory check, 2026-11-02. No new theorem, spectrum, or Git write.

## Exact source pins and lines

- `docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md`, fetched at
  `rh_clean`, blob `1879347b72d1aa55cf506f5387de37059f929122`:
  lines90–95 Fourier/Parseval; lines119–145 correlations and full source;
  lines147–157 unconditional zero-side formula with multiplicity;
  lines178–190 literal N=m carrier and exact matrix restriction.
- `PROSHKA_VERDICT_HARDBREAK_2026-10-31.md`, blob
  `2fefd53e6dd2d9492ddbc5a8195fac3e9d4d8feb`:
  lines93–99 theta/Fourier conventions; lines105–126 compensated full source
  and both poles; lines262–269 square versus absolute-square distinction
  off the real axis. Its `H=4ξ` normalization belongs to the theta profile;
  it is not an extra factor for an arbitrary unit carrier vector.

## Raw Fourier evaluations give 2G, with no missing 2π

Use the same real even physical basis

`φ_n(x)=d_n(−1)^n cos(2πnx/L)/√L`, `|x|≤L/2`,
`d_0=1`, `d_n=√2 (n>0)`, zero outside.

Let γ_k>0 run through the retained genuine critical-line zero ordinates,
through height400 in the requested calculation. Put

`E_kn=φ̂_n(γ_k)`, `G=E*E`, `C=EE*`,
`φ̂_n(t)=∫φ_n(x)exp(−itx)dx`.

For a carrier vector f with coefficient column a, its sampled evaluations are
`Ea`, and `a*Ga=Σ_(γ_k>0)|f̂(γ_k)|²`.
The source explicit formula is

`k(f,g)=Σ_ρ overline(f̂(bar z_ρ)) ĝ(z_ρ)`, `z_ρ=i(ρ−1/2)`.

For each critical zero, z_ρ is real. Its ±γ pair gives two identical terms
on the even carrier. Thus the **retained positive-ordinate contribution to
the full even Weil matrix A is 2G**, or equivalently the nonzero spectrum
of `2C`. If a zero has multiplicity q, repeat its row q times or weight that
row by √q. Listing distinct ordinates once assumes multiplicity1 for those
entries; specify that convention.

The factor `1/(2π)` occurs in Lebesgue-frequency Parseval, not in this discrete
zero sum. Inserting it into raw E would change the normalization: with
`E=φ̂/√(2π)` the corresponding coefficient would instead be `4π E*E`.
Neither dividing by H(0) nor replacing φ̂ by Xi-normalized samples is the
requested unit physical evaluation map.

The direct stable basis transform is

`φ̂_n(t)=d_n(−1)^n (L/2)/√L ·`
`[sinc((t−2πn/L)L/2)+sinc((t+2πn/L)L/2)]`,

where sinc(z)=sin(z)/z and sinc(0)=1. This includes modal removability.

## Poles and the unobserved remainder

The source-side matrix already includes the full archimedean constant,
all prime powers, and `+pp*−qq*`,
`p(x)=√2cosh(x/2)`, `q(x)=√2sinh(x/2)`.
On the even carrier the q functional vanishes by parity; p generally does not.
The zero-side formula incorporates that compensation. Do not add another
pole term to 2G when comparing it with the already full A.

Evaluation at finitely many verified critical zeros assumes no global RH.
It defines an unconditional positive finite Gram matrix. But

`A−2G = remaining zero-side contributions`

includes omitted critical zeros and any unexcluded off-critical zeros.
Off-critical contributions use the conjugate-reflection pairing, not an
absolute square, and can be indefinite. Therefore **A−2G need not be asserted
positive semidefinite unconditionally**. Under RH the remaining contributions
are positive and this Loewner comparison is available; that is a conditional
interpretation, not a premise of the proposed measurement.
Finite numerical discrepancy, agreement, or a small negative difference
eigenvalue must not be read as global RH evidence without the relevant tail,
root-evaluation, quadrature, and eigenpair budgets.

## C nullspace is in zero-index space

If E has p retained zero rows and d=m+1 carrier columns with rank r,

`rank G=rank C=r`, `dim ker G=d−r`, `dim ker C=p−r`.

The nonzero eigenvalues of G and C coincide, with multiplicity, and equal
the squared nonzero singular values of E. In particular C has at least p−d
forced zero eigenvalues when p>d. Their existence is finite-dimensional
algebra, not a deficiency of the arithmetic source.

- `a∈ker G` means the physical vector with coefficients a vanishes under all
  retained zero evaluations. It does not mean full Weil radicality.
- `b∈ker C` means `E*b=0`: a linear dependency among the sampled evaluation
  functionals on this carrier. It is not a physical vector hidden from E,
  nor does it say an individual listed zeta zero is absent or invisible.

Tiny eigenvalues and numerical rank require an explicit threshold and precision
stability; a floating truncation cannot distinguish exact nullity beyond the
dimension-forced part without further verification.

## Mixing and near-degenerate modes

For an orthonormal eigenbasis U of A, `E_A=EU` lists zero responses of the
actual physical energy modes. Then `G_A=U*GU`, while `C=E_A E_A*` is unchanged.
Thus a plot of C is invariant under a unitary change of carrier basis; it does
not by itself assign one energy eigenvector to one zero.

Eigenvectors within a degenerate Gram or energy cluster are not canonical.
Near degeneracy, individual coordinates and one-to-one assignments can change
substantially under perturbations smaller than the displayed energy scale.
Report cluster projectors, principal angles, aggregate overlaps, or singular
subspaces alongside any individual-mode assignments. A zero-side eigenvector
of C mixes zero-index evaluation functionals; a right singular vector of E
mixes physical carrier modes. These are different spaces.

**Verdict:** `2G` is the correct retained-zero normalization for the stated raw
Fourier evaluations; C is a useful finite capacity/mixing observable, with a
large dimension-forced nullspace when p>d. It is not an unconditional positive
remainder decomposition or a new level–zero correspondence theorem.
