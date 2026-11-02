# Arithmetic transitions: diagnostic only

The actual screw function is continuous. Its derivative has jump
`b(n)/sqrt(n)` at `t=log(n)`, by the source normalization `g=-q[chi]/2`
verified in `../source_audit/SOURCE_AUDIT.md`. These are derivative kicks,
not jumps of g or of the formal radius proxy.

For every integer 20–240, `all_atoms.csv` gives exact algebraic DH
coefficients before numerical sign evaluation. All 54 zeta prime-power
weights are positive. DH has 25 positive, 27 negative and two exactly zero
weights on these same prime powers. In addition, 75 non-prime powers have
nonzero DH coefficients. The independent coefficient recurrence agrees
within 5.32e-99.

`local_atom_slopes.csv` joins all 442 kernel cells (3094 rows, no missing
cell). At fixed N=m, fixed actual zero nodes and L_tau=L exp(tau), the
source derivative kick is `-2 L b(m)/sqrt(m) d_b d_b*`. Consequently
`jump dotK_z = 2 L b(m)/sqrt(m) |endpoint(v_z)|^2` and
`jump dotr_proxy = -jump dotK_z/(eta K_z^2)`.
Zeta therefore has the expected weak positive K kick and weak negative
formal-radius kick. DH retains the signed coefficient. The formulas apply
to invertible inverse forms, including indefinite ones; they provide no
identification with a Weyl disk radius.

`prime_power_smooth_decomposition.csv` contains all 648 point/gauge rows:
54 prime powers, both worlds, physical and Fourier evaluations, eta=.5,1,2.
It reports the smooth left derivative, arithmetic kick and right derivative
separately. `smooth_parts.csv` adds the m=20 controls, giving 660 rows in
110 cells. The smooth continuation excludes the birth integer m on both
sides of the central difference; it varies A, E and the evaluation vector
while retaining the same actual active zero set. The right derivative is
obtained by adding the exact rank-one kick. No eigensystem is recomputed.

At 1024 bits and h=1e-30, base K and endpoint-cross agree with the saved
kernel values at all 65 reported digits. The worst relative radius
chain-rule discrepancy is 9.73e-53. Repeating m=55,239 in both worlds with
h=1e-35 changes the smooth derivatives by at most 5.88e-53 relatively.
These are numerical derivative checks, without interval truncation-error
enclosures. The source's finite geometric-tail metadata uses the next
omitted term explicitly; this metadata correction does not change A.

`discrete_increments.csv` retains 2640 defined adjacent-size differences plus
12 initial m20 rows with undefined previous values (2652 rows total),
including changes in N and the active zero count. Such increments differ
from a fixed-N threshold derivative. Among the 162 zeta prime-power
observations per gauge, 26 physical and 60 Fourier increments have a sign
different from the local derivative kick. This does not contradict the
local formula: the discrete schedule is nonnested and contains additional
smooth, carrier-dimension and head changes. DH discrete observations are
also retained without replacing signed or indefinite values by magnitudes.

Reproduction: run `atom_table.py`, then `join_kernels.py` after generating
`../kernels/`; run `smooth_parts.py --input-root INPUT_ROOT --m ...
--world zeta dh --bits 1024 --h 1e-30` on all sizes in `prime_powers.csv`
and m=20. Repeat anchors 55,239 with `--h 1e-35`, then run
`summarize_smooth.py`. Set PYTHONPATH to the python-flint installation when
needed. Scripts resolve sibling paths relative to their own location.

DIAGNOSTIC_NEVER_A_PROOF. No route-state or RH export.
