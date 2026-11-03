# Conditioning and threshold-index scan

DIAGNOSTIC_NEVER_A_PROOF. Original literal even carrier dimensionm+1,
L=logm, Omega=2pi*m/L. Primaryc=1/4, secondaryc=1/2 use
kappa=1+c(1+logL)/L; controlkappa=1. Allm<=120 lie outside the
source's stated L>=16 theorem regime; no asymptotic residual claim is tested.

RawE has one physical Fourier row at each active real positive zero and
two unscaled Re/Im rows for every off-real quartet. No sqrt2 row scaling.
All active conditions use strictheight<T; multiplicity does not add derivative
rows. Track conditionrank separately from zero count/multiplicity.

PredictionC1 (.8): the111.0295/111.8747 pair enters at differentm for the
three cutoffs, and the rawcapacity near that crossing is not explained by
the smallest normalized included-zero gap alone. Discriminator: compare
same-m cutoff variants, edgezero sensitivity and the weakest left singular
vector, preserving both selected ordinates and fullsourceA.

PredictionC2 (.9): rawMP80 conditioning at baseline m24 and pairregion m70..85
replays atMP120 with relativechange<1e-30 where rank is numerically resolved.
If float singular values approach their errorfloor, label them unresolved,
never substitute them for MPcapacity or force a quiet dimension.

PredictionC3 (.99): guardedthreshold Schur inertia matches N_A(2)-r, with
the eliminated quietblock index retained if ||AQ||>=2. No inverse-based
formula is used on a singular/near-zero eliminatedblock without a guard.
The full residual is ||AQ||, not ||Q^T A Q||. FullD/B/G are retained.

First benchmark only: MP80 SVD and fullQR cost at m24,80,120, primarycutoff,
before choosing all-integer highprecision versus selectedvalidation. Then
report resource plan to root before large scans. No unbounded batch or
silent precision reductions. Initial budget: baselinecells m16,24,32,40;
pairregion70..85 andm120. Remaining all-integer cases may use clear
precision guards and cached source matrices, with unresolved values explicit.

Implementation refinements made before the complete scan: use stable complete float QR of an MP-reorthogonalized row frame; cross-check against MP 0/1 projectors. For conditioning, branch on numerical resolvability against an explicit radius: well-resolved float singular vector plus MP Rayleigh/residual, otherwise MP80/120 Gram iteration, small-cell full-SVD fallback, bounded unresolved result for large weak cells. No selection is made according to the desired λ/gap relationship. The cap was applied after pilot runtime revealed slow near-degenerate controls and high-condition DH Gram matrices; unresolved cases are retained.
