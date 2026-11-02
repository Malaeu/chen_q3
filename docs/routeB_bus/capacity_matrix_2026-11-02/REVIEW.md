# Bounded final review: finite capacity matrices

Read-only mathematical-definition, numerical-interpretation and code review of
`capacity.py`, `mixing.py`, `report.py`, the generated `RESULT.md`, and the
existing summary files. No full computation rerun or Git operation was performed.
The earlier source-normalization check is in `NORMALIZATION.md`.

## Verdict

**PASS for the stated finite diagnostic scope; no material finding.**
This does not certify exact spectra, an infinite-zero tail bound, positivity of
an uncomputed remainder, RH, or a cofinal capacity/counting theorem.

## Checks

1. **Normalization.** The raw evaluation matrix uses the unit real even
   physical basis, with no H(0) normalization or Parseval divisor. The
   rational-times-sine formula and its sinc removable extension agree with
   that convention. The retained ±zero contribution is `2G=2E*E`, not G.
   The full A already includes the source pole terms; none is added again.

2. **Dimensions and nullity.** There are202 retained positive-zero rows and
   d=17/25 carrier columns. C therefore has nullity at least185/177 in
   zero-index space. These are distinct from the small positive eigenvalues
   of G on the physical carrier. The report does not confuse structural
   C-nullity with a physical near-null spectral cluster.

3. **Nonzero C modes.** For `G U_i=g_i U_i`, the construction
   `W_i=E U_i/√g_i` correctly gives unit nonzero C eigenvectors with
   eigenvalue g_i. The final files resolve every g_i positive at their stated
   working precision, so W has all d columns in these cells. The code checks
   `CW−W diag(g)`, orthogonality, and the trace identity. Transposes are
   appropriate because the evaluation matrix and bases here are real.

4. **Carrier versus zero-space components.** `V*U` measures A/G carrier-mode
   overlaps, whereas `|W_ki|²` describes the zero-index mixture. Participation,
   strongest zero weights and contiguous90%-mass windows have the stated
   meaning. They are not one-to-one assignments of Weil energies to zeta zeros.
   Near-degenerate individual directions remain basis-sensitive; no intrinsic
   single-zero identity is claimed.

5. **Prefixes.** Adding one retained positive-zero row adds a positive rank-one
   term to G. Structural nullity for q<d is separately labeled. Selected
   prefix eigenvectors are compared with the final finite-height400 basis;
   that reference is not treated as the infinite-zero limit.
   For the zero-padded left modes the saved squared overlap formula
   `|U_i*U_(q,i)|² g_(q,i)/g_i` is correct, since
   `E_q*E_q U_(q,i)=g_(q,i)U_(q,i)`.

6. **Residual matrix.** The corrected largest/second-largest indices are d−1
   and d−2. In the computed files the residual eigenvalues are positive, so
   their ratio is a valid descriptive almost-rank-one measure. The top
   residual direction is compared with normalized `b=(1,√2,…,√2)`, the
   endpoint-evaluation direction. The large-t evaluation formula also has
   leading direction b. Both facts are interpreted as finite observations,
   not as an unconditional positive infinite-zero remainder theorem.

7. **Precision.** E/G/A eigenproblems and subspace SVD use mpmath. No float64
   eigensolver was found. Float conversion is used for figures and descriptive
   weights, windows, participation and displayed summaries. Numerical
   residuals are reported as checks, not enclosure radii or interval proofs.

## Consistency with the reported outcome

The minimum same-index carrier overlaps squared, approximately0.99780045 and
0.99619376, support the scoped statement that the finite carrier eigenbases
are close. They do not make the eigenvalues identical: the bottom ratios
`2g_0/λ_0(A)` are approximately0.65976151 and0.43749768. This distinction is
retained explicitly in the report.

The B=2/4/8 cluster counts of A and2G agree in these two cells; their largest
cluster principal angles are at most about1.247degrees. In the current data
the compared cluster dimensions coincide, so the same-r slicing in the angle
code compares the actual declared clusters.

The observed second/largest residual eigenvalue ratios, approximately
`5.8384e−7` and `1.6669e−6`, and the near-unit boundary-direction overlaps
justify the phrase numerically almost rank one. The report correctly keeps
off-critical contributions unexcluded, treats positivity as uncertified, and
does not turn increasing prefixes through400 into a completed convergence
claim. No theorem status changes follow from this batch.
