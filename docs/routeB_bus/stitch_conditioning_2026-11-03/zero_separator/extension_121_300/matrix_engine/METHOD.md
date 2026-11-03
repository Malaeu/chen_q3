# Literal even matrix engine

DIAGNOSTIC_NEVER_A_PROOF; Route B CHALLENGER / NOT_RH. No route-state exports.

`engine.py` implements only the physical **even** cosine carrier with N=m, using the archimedean sine/diagonal moment recurrence, the exact finite coefficient recurrence, analytic archimedean tail, and the ζ pole. Its conventions match `suzuki_w_inputs/prototype.py`, `dh_inputs/dh_matrix.py`, and Q2 parity.py. Plant adds `4 Re(e(w)e(w)^T)` with w=2π/log2+i/4 (transpose, not Hermitian adjoint). No odd carrier is built.

Arithmetic uses gmpy2 MPFR/MPC at400bits. An independently computed Newton/Legendre quadrature uses192 nodes per panel and8panels. Paired192/256 source pilots at m80,120,121,300 differ by at most1.2e−115 per entry. Source regression against previously saved DH80, DH120, and ζ120 matrices differs by at most4.7e−116. These are numerical checks, not interval quadrature bounds.

For every matrix, three unpivoted symmetric LDL decompositions count negative pivots of A−gI, A, A+gI, with g=1e−70. An exact zero pivot returns unresolved rather than dividing by zero. The shifted-count range [nminus(A+gI),nminus(A−gI)] leaves all modes in the numerical guard band unresolved. The middle/raw count is a diagnostic only: it must never replace the guarded range. The range itself is numerical rather than certified because source and arithmetic error have empirical checks, not proved outward bounds. Minimum absolute pivots are saved for the Python backend. The later native MPFR backend traps zero pivots but does not report the minimum nonzero pivot; metadata explicitly records this limitation. Native counts were validated against all three Python shifts in all three worlds at m121 before restarting only missing checkpoints. Broad ranges are expected for the tiny spectrum and must not be collapsed to a definite count.

Each `matrices/{world}_m{m}.npz` contains float64 A, sorted eigenvalues (also `lambda_`), m, and `numeric_radius`. This float radius is 64 eps n max(1,spectral radius), a conservative numerical roundoff heuristic, not an interval bound. Separate JSON records contain MP source settings, LDL diagnostics/range, timings, and provenance. Downstream δ/λ_r calculations should preserve their own numerical guards and should not infer signs of tiny eigenvalues from float64 output.

`bulk.py` checkpoints each world/m and uses two worker processes, each with one BLAS thread. Pilot and regression logs are retained. No full MP eigensystem is required.
