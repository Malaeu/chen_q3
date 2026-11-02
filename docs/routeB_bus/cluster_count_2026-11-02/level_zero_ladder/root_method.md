# Physical Fourier root extraction

The union of lifted levels is taken literally as lambda_i >= m^(-8), retaining all modes of every eigenvector. Sources use 180 dps/GL160 for m=16,24,40 and 160 dps/GL128 for m=32. The even basis is the zero-extended normalized cosine basis specified in the eigenpair source.

Define omega_m=2*pi*m/log(m), the highest retained frequency. For each level, set c_n=d_n V_ni and y=(t/omega_m)^2. We form the degree-at-most-m polynomial

    sum_n c_n product_(k != n) (y-k^2/m^2).

The c_n are rounded to 100 decimal significant digits and converted to exact rationals. SymPy isolates every real root of that rational polynomial, including multiplicities, to a rational interval of width at most 1e-35. Positive roots supply seeds only. Each seed is then refined using the full-precision direct sinc transform and its analytic derivative; root drift beyond 1e-20 relative triggers failure. Modal lattice poles are removable in the direct sinc expression and are not accepted as zeros merely because a rational numerator is small. The direct transform value is retained for every accepted root.

All positive polynomial-root candidates are kept, including candidates above the matching range. Structural exterior roots t=k*2pi/L, k>m, are listed separately through t=120 and the next two lattice points. At these points all finite-window cosine transforms vanish exactly. For interior modal lattice points the transform generally does not vanish.

An independent uniform-frequency sign scan on [0.013,120.013], spacing 0.05, uses the rational expression with direct sinc evaluation at removable points. Every detected sign-change bracket must contain a reported root. This scan can miss very close root pairs and is only a supplementary numerical check. Exact real-root isolation certifies the rounded polynomial's roots, not those of an exact CCM eigenvector; neither this computation nor its cross-precision check is an interval certificate for the true Fourier transform.

`roots.csv` preserves `m,i,t_root,kind,polynomial_multiplicity,direct_F_residual,normalized_residual,source_dps`. The normalized residual divides by sqrt(L), an L1 bound for an L2-normalized vector on its window. `root_results_m*_dps*.json` records source hashes, real-root counts and sign-scan diagnostics. `root_validation_m40.json` independently refines the m40 roots against the 160 dps/GL128 eigenvectors; main m40 roots use 180 dps/GL160.

Replay the four `roots.py` carrier jobs (arguments 16; 24; 32 160 128; 40), then `root_finalize.py`. Both require mpmath; the root-isolation jobs also require SymPy. Roots are numerical locations, not symbolic identities with zeta ordinates.

Additional diagnostics: `direct_Fprime` and `estimated_position_residual` refer to the internally refined root; `serialized_F_residual` and `serialized_position_residual` evaluate the saved 125-significant-digit location. The latter prevents treating the much smaller internal residual as accuracy of the rounded stored value. Run `root_counts.py` to independently recount positive/negative/nonreal y roots, and `root_serialized.py` after `root_finalize.py` to add serialized-value diagnostics. Every rounded numerator in this run is square-free. Nonreal y roots occur (up to18 per polynomial), and negative y roots occur (up to2); no real-rootedness assumption is made.
