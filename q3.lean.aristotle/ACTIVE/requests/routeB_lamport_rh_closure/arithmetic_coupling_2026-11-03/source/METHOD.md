# Literal arithmetic coupling split

DIAGNOSTIC_NEVER_A_PROOF. Fixed physical even carrier N=m,L=logm. For each world,

A(u)=C+uB,

where C contains the complete archimedean gamma term, its analytic tail, and the ζ pole (no DH pole). B contains **all arithmetic atom terms with their original signs**, −b(n)/sqrt(n) times the shifted autocorrelation form. All terms in B scale jointly withu. The finite support leaves2≤n<m; n=m has identically zero overlap, hence zero form. This is not a change of prime coefficients inside the fixed source.

The double2 control uses Cζ and Bζ+the single ζ atom at integern=2. It doubles that atom only; atoms at4,8,and higher powers are not modified. The stored atom2 matrix is the ζ n=2 contribution, even in a DH file where it is an auxiliary reference and not added to DH B.

`split.build(m,q)` returns400bit MPFR object matrices C,B,A1,atom2. Saved npz files contain their float64 readbacks plus sorted C/B/A1 spectra and a conservative heuristic roundoff radius. Main quadrature is GL192 per panel with8panels. Independent GL256 pilots at16 and300 differ by less1.2e−115 per entry across C,B,A1. No inertia, interval membership, or eigenvalue-sign certification is performed.

For each base world, positive-b and negative-b atom lists are accumulated independently into sine/diagonal moments, then into their signed B matrices. Metadata records each group's atom count, signed coefficient-weight sum, matrix trace and max-entry magnitude; their sum reproduces B at400bit roundoff. These are classifications by coefficient sign, not claims that the resulting atom/group matrices are semidefinite. The double2 metadata lists its extra positive-b integer2 separately.

C+B is regressed against frozen source A where available. At80,120,248,300 the float matrices match exactly for both base worlds. DH16 differs from the old float64 build by8.44e−15, inside roundoff; no frozen ζ16 matrix was found, so that particular comparison is explicitly absent. The split itself uses the same original source assembly formulas. C is already indefinite at16 in both worlds; adding a small positive εI must not be assumed to make C SPD.

Every npz is paired with source/settings/check metadata in JSON. PROVENANCE.json hashes the old builder and this derivative. Completion and conservation/control checks are reported by finalize.py, not by a proof claim.
