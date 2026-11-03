# T3 Hermite-coordinate sanity: exact identity and bounded pilots

DIAGNOSTIC_NEVER_A_PROOF. The seven baseline gates passed before these
checks. Source400bits, GL256/8panels and frame768bits are unchanged; there is
no precision chase or altered source/constraint count.

The exact proof is in hermite_EXACT_ARGUMENT.md. Its scope is every pair
of distinct INCLUDED, equal-multiplicity events. Real/complex branches may
be changed by the invertible sum/divided-difference coordinates; mixed
one-row/two-row events are not silently blended. No new separator theorem
or favorable source sign follows from a row-coordinate change.

Numerical coverage is BOUNDED: ten prefix sectors, eight distinct nonidentity
transforms,30 theta receipts of which13 activate the transform. Repeated
identical transforms at different admitted theta values reuse their computed
comparison. The tested active cases are zeta16,80,120(q58),200,248(q128),300;
DH310(q249); plant310(q167). Additional zeta310(q163) and600(q333) cases have
no included admissible near-window T1 pair below the tested thresholds and
are identities, not nonidentity successes. Requested24,40,400 are not
numerically executed; full-grid numerical T3 coverage is NOT claimed.

Pair selection uses the frozen T1 local mean spacing2pi/log(midgamma/(2pi))
and its two fixed near-window tests. The original zeta248 optimizerq127
splits the pair127/128. Its mandated Hermite pilot uses the DISTINCT next
sectorq128, which includes both. At all theta=.5,.6,.75 this pair is active.
No excluded row is imported into the originalq127 space.

For zeta248q128, relative delta difference is approximately2.16e-16 and
physical projector operator-norm difference3.35e-15. Across the eight active
cases, the largest relative delta difference is approximately1.12e-15 and
largest projector difference5.93e-15. Lambda_r and r are reused identically
between raw/Hermite coordinates. The matrices are NOT reoptimized separately.
These are binary readback comparisons after768-bit frames, not enclosures.

The source-census provenance is regional: low zeta capacity CSV, mid zeta
extension CSV, high zeta/DH900 CSV/JSON; DH beta is obtained from the FULL raw
sigma_right decimal string. Each receipt binds its OWN census SHA-256.
Physical2t sin(tL/2)/sqrt(L) factors are included before combinations.
The consumed low/mid zeta point strings also match the corresponding high
prefix exactly; the final receipts nevertheless read the regional files.

Original zeta600 optimumq600 has residual at its original numeric floor and
is NOT numerically reframed or relatively scored. The only nearby theta<=.75
pair600/601 would needq601=d, yielding J=0 and inadmissibility. See
hermite_ORIGINAL_FLOOR.json. In particular the extra resolved kappa1q333
identity case is not advertised as an active600 transform.

hermite_summary.csv retains every theta comparison; hermite_COVERAGE.csv
marks executed versus unexecuted cells explicitly. The exact invertible-row
argument supplies the coordinate identity on other eligible frozen-grid
pairs; it does not turn absent numerical work into a numerical grid result.
