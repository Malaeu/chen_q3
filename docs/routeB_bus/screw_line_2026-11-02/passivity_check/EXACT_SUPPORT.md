# Exact DH support labels

DIAGNOSTIC_NEVER_A_PROOF. This fixes labels, not the numeric source matrix.

Write D(s)=1+A(s), with periodic coefficients
(0,1,tau,-tau,-1). The finite formal Dirichlet logarithm

    [n^-s] log D = sum_(k<=floor(log_2 n)) (-1)^(k+1)/k [n^-s] A^k
    b(n) = log(n) [n^-s] log D

is evaluated in Q[tau], reduced modulo
`t^4+2t^3-6t^2-2t+1`. Thus a zero coefficient is detected algebraically,
without a floating cutoff. `exact_atoms.py` (SymPy) generates
`DH_EXACT_COEFFICIENTS.json` through300; downstream checks load that table.
The chosen tau is specified by its radical, not an arbitrary root.

The original floating recurrence produced tiny rounding ghosts at some
exact zeros (e.g.57,87,118). Treating every nonzero decimal as an arithmetic
atom would give12 spurious non-prime-power labels on20..240. The corrected
support has75 non-prime-power nonzero coefficients on that range.

`exact_label_records.py` changes only the displayed birth labels of these
zeros and preserves the original decimals in `numeric_recurrence_birth_raw`.
The original input-stream hashes, matrix solves, inertia and inverse kernels
are unchanged. Source matrices and curve computations used the unthresholded
floating recurrence at their stated precision; its tiny residuals remain
ordinary coefficient roundoff. No operator with deleted nonzero atoms was
substituted. All1768 overlapping kernels still agree with the independent
canonical implementation within4.88e-65 relative error.

Aligned JSON/CSV atom labels use the same exact support; their numerical
Gram matrices are unchanged. Scalar source-section bookkeeping suppresses
only exact symbolic zeros. This distinction is recorded because a support
or sign claim must not classify roundoff as a new physical section.
