# Independent zero-threshold count review

Read-only extraction from the frozen literal-even CCM spectra, m=16,...,120,
all three worlds. No matrix, projector or eigenproblem was changed.
`counts.csv` has 315 rows. Selection exactly follows `refine_lambda.py`:
maximum GL first, then prefer names beginning `mp_cell`; use cached MP
full eigenvalues only if no replay exists. Every selected receipt has its
own SHA256 and source provenance in the table.

Literal signs of printed MP point values are reported separately from
numerically guarded signs. The receipt's `roundoff_heuristic` is preferred.
When that field is absent from an inherited cache, the fallback gives up
20 printed significant digits and scales by max(1,max|lambda|). This is a
screening heuristic based on output precision, not a source-accuracy,
quadrature, zero-census or interval error enclosure. Thus the reported
lower/upper negative-count range is numerical, not a certified inertia
interval. The upper value includes every eigenvalue within the zero guard.

| world | literal negative count range | guarded lower range | cells with unresolved zero signs | first resolved negative |
|---|---:|---:|---:|---:|
| zeta | 0–5 | 0–0 | 81 | none |
| plant | 1–12 | 1–1 | 75 | 16 |
| DH | 0–2 | 0–2 | 28 | 51 |

In particular, a tiny printed negative ζ eigenvalue at a cache's arithmetic
floor is not evidence for a negative source direction. Float64 signs near
zero are still less useful here: they must not replace the MP/guarded
counts. The planted source has one resolved negative direction throughout
this grid, while additional printed negative signs near zero remain
unresolved. DH has genuinely negative resolved directions starting at 51.
The table also retains the literal count in (0,2), which is a different
quantity from n_-(A) at zero; small positive eigenvalues in that interval
are not negative directions.

For any proposed quiet subspace of dimension 0<r<d, with orthonormal Q,
put delta=||AQ|| and order lambda_0<=...<=lambda_(d-1). A necessary
condition for delta<lambda_r is

    lambda_r > max(-lambda_0, lambda_(r-1), 0).

Indeed, the r-th smallest singular value is at most delta. For every
threshold strictly below the positive lambda_r there are only r eigenvalues
with lambda<=that threshold; all negative directions must therefore fit
inside the absolute-value band as well. A nonpositive lambda_r, repeated
eigenvalues across r, or -lambda_0>=lambda_r excludes that rank before
building a projector. Passing this necessary test does not prove that the
specific evaluation-kernel subspace passes. The separator also does not
by itself imply n_-(A)=0: it may put negative directions inside the quiet
sector.

Degenerate cases require explicit labels. If r=0 (q>=d with full column
rank), J=0 and delta=0; delta<lambda_0 is merely positivity of the whole
finite matrix, with no nontrivial quiet-sector statement. If q=0 then r=d:
Q spans the whole carrier and lambda_r is outside the spectrum, so the
requested separator is undefined. Tall E must not be treated as a square
invertible evaluation map. Distinct zero-height events can skip a rank
because a quartet adds two real rows, so not every integer r is necessarily
realized by a cutoff.

All statements are finite numerical diagnostics. DIAGNOSTIC_NEVER_A_PROOF;
no route-state or RH export.
