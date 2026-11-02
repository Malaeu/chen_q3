# Signed source ledger for the bottom of J-perp

`DIAGNOSTIC_NEVER_A_PROOF`. Original schedule N=m, L=log(m), kappa=1.1.

`ledger.py` reads unchanged `dh_matrix.py` and saved source matrices from
`fake_worlds_2026-11-02` at `d26831357b6cb3b2b7d4a569d2031e454952b246`.
Extract its matrix archives to `matrix_cells/` first. Run with
`DH_INPUTS=/path/to/fake_worlds_2026-11-02 python ledger.py 55 DH`, and likewise
for m=80,120 and world `zeta`. Zeta ordinates come from `zeta_zeros.csv` in that
input directory, or the sibling `capacity_matrix_2026-11-02/zeros.csv`.

The physical source ledger is

    Rayleigh = H_raw + constant_c + pole - sum_(n<=m) b(n)/sqrt(n) Q_f(log n).

`H_raw` includes the infinite archimedean tail. Its kernel is
`exp(-s/2)/(1-exp(-2s))` for zeta and `exp(-3s/2)/(1-exp(-2s))` for DH.
The constants are `-gamma-log(8*pi)-pi/2` and
`log(5/pi)+psi(3/4)`, respectively. There is no DH pole. Arithmetic terms are
grouped by prime, prime square, higher prime power, and non-prime-power,
and separately by positive/negative b(n). Their stored values include the
minus sign from the operator. The birth atom n=m is retained and multiplied
by exactly zero Q(L).

The trial is the lowest eigenvector of U^T A U, where U is an orthonormal
basis of J-perp. Q separately denotes the orthonormal basis of J=ker(E).
Thus a compressed lowest vector is not confused with a full lowest vector.
The source includes both critical-line zeros and real/imaginary constraints
for each reflected positive-height off-line pair. Row equilibration is used
only for a numerically stable basis; it does not change the subspace.

Boundary and interior terms are a **second ledger**, not extra terms added
to the physical Rayleigh sum. With psi_b(x)=sum_(n<=x) b(n),

    a(s)=exp(-s/2)[psi_b(exp(s))-(exp(s)-1)],
    B=2 f(L/2) integral_0^L a(s) f(L/2-s) ds,
    I=-2 integral_0^L a(s) integral_(-L/2)^(L/2-s) f(x)f'(x+s) dx ds,
    halfQ+B+I = P - continuum,
    continuum=integral_0^L exp(s/2)Q_f(s) ds.

For zeta this is the exact source `c31645a`, equations (3.3)/(3.4) in the
delivered file (the owner's boundary/interior labels). For DH the same Abel
calculation is explicitly an analog using **all** signed b_D(n), rather than
an assertion that the zeta psi is unchanged. All s-moments are integrated
analytically as exponential-trigonometric primitives on the integer atom
intervals, without quadrature or dropping the moving boundary.

For zeta an additional cross-check records

    pole = continuum + decaying_continuum,
    decaying_continuum=integral_0^L exp(-s/2)Q_f(s) ds,
    H_plus=H_raw-4+decaying_continuum,
    Rayleigh=H_plus+4+constant_c-(halfQ+B+I).

Here H_plus uses `exp(-5s/2)/(1-exp(-2s))`, the transformed H of the
PRIME_COMPLEMENT/KERNEL source. This avoids mixing raw H and transformed H.

The JSON results report physical-ledger sum residual, Abel-ledger residual,
compressed eigen-equation residual, E Q residual, source reconstruction
difference (DH), full minimum, full quiet residual delta, and modal trial
coefficients. All series calculations are diagnostic numerical computations;
no route-state, RH assertion, or mathematical status is exported.
