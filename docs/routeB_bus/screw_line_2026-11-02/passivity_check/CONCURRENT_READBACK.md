# Independent readback of the concurrently delivered canonical packet

DIAGNOSTIC_NEVER_A_PROOF.

During this run, rh_clean acquired the canonical SCREW_LINE packet at
`05d2604ae7a1d8d96d59306d559ac6a72e070701`. Its source base is the same
`1c91c4c86ef6987782c08c84e22707d1b7324646`. This independent addendum is
placed in `passivity_check/` to preserve that packet and its raw data.

## Numeric overlap

The canonical archive's 30 parts and its exact `kernels/kernels.csv` and
`kernels/inertia.csv` members were read back and checked against its
DATA_MANIFEST. All442 inertias and ranks agree. All1768 overlapping endpoint
and Fourier kernels, and all1768 endpoint cross-kernels, agree with maximum
relative differences **4.88e-65** and **4.78e-65**, respectively. The canonical
CSV serializes about64 significant digits. Full comparisons and member
hashes are in CONCURRENT_NUMERIC_VALIDATION.json.

The algorithms are materially different: the canonical packet uses analytic
arch moments,1024-bit Arb midpoint arithmetic, raw EAE* congruence and LU;
this addendum uses220-dps quadrature,768-bit GMP arithmetic, reorthogonalized
MGS and LDL. Neither is an interval inverse certificate. The comparison
was performed after this addendum's independent scan, not used to manufacture
its values. The canonical packet also retains an interior-cosine evaluation
gauge; that additional gauge was not recomputed here.

## The geometric variables differ

The canonical geometry uses stationary increment innovations v_n. While
positive, those prediction-error variances DECREASE with the number of
previous increments. This addendum uses the projection inverse form E_n
of ONE fixed target curve point; while the kernel is positive, E_n INCREASES
as its projection space expands. These are different variables, both governed
by Schur positivity. Opposite monotonic directions are not a contradiction.

The meshes also differ. Canonical1/64 and1/128 witnesses, this addendum's
uniform240/480 nodes over log240, and its log-endpoint plus fixed-mesh test
must not be assigned one common continuum onset. Each preserves old nodes
within its own run. Source normalization agrees: g=-k[chi]/2 with the
original gamma, constant, pole and all signed arithmetic terms retained.

## Additional owner-steered passivity content

The new material is the independent whole-scan verification, the fixed-target
geometry and its resolution control, sparse-endpoint false-negative control,
the actual global completed-log-derivative test off the imaginary axis,
and the exact source-preserving passive-section proof contract. No finite-end
canonical impedance or passive factorization is claimed. The previous
canonical numerical conclusions and raw files are preserved.
