# SUZUKI_W_v1 and prediction addendum

**DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH.** Finite computations and their limitations are recorded below. No continuum deficiency-space convergence, unrestricted analytic gauge, global kernel positivity or RH result is claimed.

## Source and convention corrections

Suzuki arXiv:2606.09096 has material version changes. Historical v1 uses z²ξ/ξ′. Current v3 uses ξ/(ξ+ξ′), with an analytic exponential gauge and compact convergence in the upper half-plane. The user-specified historical ratio and current ratio are both evaluated. A rectangle containing real derivative poles does not admit the requested ordinary uniform relative-error interpretation. See `theory/AUDIT.md` for version-specific links.

With D=i∂x and T=A−λI in physical L², the corrected loads are v+=T⁻¹ exp(+x), v−=T⁻¹ exp(−x), with equal T norms. Thus the user formula swaps the labels. Both parity blocks are required. A finite Ritz shift does not establish the corresponding continuum lower bound. These distinctions are included in every finite prototype.

Pins: original task base1c91c4c86ef6987782c08c84e22707d1b7324646; addendum basefcb70c5dd82a434dd77f4ea5c001cb6715a917d5; inboxab8d123e124f0a32d04ac6711a770a41073319fa. The pinned screw report is copied exactly in `prediction/SOURCE.md`, Git blobb56a16a0540ed3f81858c113bc48de68c909b8c8, SHA-2562a2132da991839a38a7fcf08512d4dd743ee52704fd3da4bb3f69b53c96ad2d2. Its plant is §6.2, formula18, rather than §5.

The separately named claude/SUZUKI_EXTRACTION_2026-11-02.md and exact K6(0.5,0.6) text were not located in bounded searches of the supplied repository pins. No contents or numerical bets from that unlocated extraction were invented. The executable predictions and kill conditions used here are saved in each PREDICTIONS.md; the primary paper was checked directly.

## W calculations

Every integer m20…240 was computed for both ζ and DH:442 finite full-parity cells. Shifts are ζ−1 and DH one below the full finite minimum. Sixteen representative profiles cover m20,40,60,80,120,160,200,240. All finite T gaps are approximately at least1. At m20, independent80dps physical-source solves agree relatively within2.54e−15 for ζ and9.08e−16 for DH. Finite H¹ endpoint-zero weak tests have maximum correct-sign defect2.45e−15; reversed signs fail. These tests do not control the full continuum adjoint domain.

For sixteen theta values,23,507 nonnegative root candidates are saved, including the explicitly seeded origin at theta0. Positive roots are found by sign changes and refined; the root-comparison summary separates origin seeds from positive counts. `W/real_W_roots.csv` compares each independently to the nearest ζ zero and nearest critical-line ξ′ zero. No bijection or complete-zero-census claim is made. The reference lists and coverage qualifications are retained. Root comparisons for DH use explicitly labeled ζ references.

At θ=π, ζ m20 has16 found positive roots versus5 ζ zeros in the same band; m240 has191 versus90. Median nearest-ζ distances are1.76540 and0.34108; nearest-ξ′ distances1.48486 and0.65845. Decreasing nearest distance alone is not spectral identification, especially with these different counts. The arithmetic-free T=I control already has an exact root lattice of spacing2π/L.

The saved root scans are positive-band scans. Reflection supplies the exact cross-theta relation W_theta(−z)=−exp(i theta)W_(−theta)(z); hence negative-band roots correspond to the positive-band roots at theta index(16−j) mod16. Same-theta symmetry is not assumed for arbitrary theta. This relation does not repair roots missed by the finite sign-change scans.

The gauge protocol is fixed and reproducible: one complex constant anchored at z=i/4; theta selected on calibration coordinates, errors reported on separate heldout coordinates. Both expanding ranges |Re z|≤0.8Ω and a fixed compact with |Re z|≤20, Im z=.05,.25,.5 are tested. The expanding-domain experiment is stronger than the paper's fixed-compact convergence formulation.

|world,target|fixed-compact heldout RMS at m20|at m240|
|---|---:|---:|
|ζ historical v1|1.00183|1.01266|
|ζ current v3|1.88830|2.00998|
|DH historical v1|1.00167|0.99767|
|DH current v3|1.83144|2.54909|

This constant-gauge family does not approach zero error over the tested range. It does not exhaust Suzuki's existential analytic gauges. A pointwise log(target/W) fit was excluded because it would be tautological on suitable zero-free patches. Fixed ζ shift−1 also changes the limiting norm compared with the λ0 heuristic; the conditional interpretation is in the theory audit.

At the actual DH off-line zero z0≈85.6993484854+0.308517182457i, finite m240 thetaπ gives |W(z0)|≈2.59514644. For v3, maximum relative error on circles of radii1e−3,1e−4,1e−5 is1557.36,15479.85,154704.93, so radius*error tends toward1.547. Historical v1 has a much smaller anchored scale and reaches1.281,3.817,29.190 on those radii. Both target versions have a missing zero at this point; an exponential analytic gauge cannot insert a zero into a fixed nonzero W. This finite observation is not a limit theorem for varying gauges.

## Prediction addendum

We compute the user-defined signed quantity sigma²=d−b* K† b, not its square root. The structural zero row t0=0 is removed with its exact range guard. Subsequent prefixes were nonsingular on the tested grids; negative eigenvalues are retained. After loss of positivity, sigma² is a Schur defect rather than a Hilbert-space conditional variance. The plant uses gamma=2π/log2, eta=.25, nu1 on the exact ζ source; it is an explicit source perturbation, not an assertion of RH for its baseline.

All prefixes on[0,6] were scanned at80 digits, with a120-digit DH fine-grid replay:

|world|first negative h=.1|h=.05|h=.025|negative index at6, h=.025|
|---|---:|---:|---:|---:|
|ζ|not seen≤6|not seen≤6|not seen≤6|0|
|DH|not seen≤6|not seen≤6|5.45|2|
|plant|2.4|1.7|1.275|2|

For DH fine-grid, the minimum eigenvalue changes from+2.558001270e−4 at5.425 to−1.224797949e−4 at5.45. All240 prefix inertias agree at80/120 digits. Maximum relative Schur change is9.95e−76. These are numerical source/spectral checks, not outward interval certificates. The full sample kernel contains both parities; its negative index2 is not the even-carrier index1 of one planted quartet.

For ζ, sigma²(6)=0.02044145579,0.01540145034,0.01116491527 at h=.1,.05,.025. The finite profiles decrease while staying positive. These three meshes and finite time horizon do not establish an asymptotic rate to zero in time or mesh size. DH and plant can have positive final Schur defects after earlier negative pivots; final-point sign alone misses their negative inertia.

For fixed old history and alpha=K†b(t), an isolated unshifted arithmetic hinge c_n at t=log n has jump

    Delta (sigma²)' = −2c_n+2c_n sum(alpha_j).

At a shifted hinge t=t_j+log n its contribution is−2c_n alpha_j; coincident contributions add. Finite-difference/Richardson checks agree below2e−10. Positive jumps occur79/98 ζ prime-power probes,61/95 DH probes and62/98 planted probes. Thus a prime hinge is not automatically a negative or positive prediction-error jump. The plant preserves all baseline prime hinges yet changes the global Schur behavior. One near-coincidence required narrower finite-difference steps and is documented.

## Replay and publication

Each directory contains code, reports, source hashes and detailed CSVs. `prediction/profiles.png` and PDF show the signed profiles and ζ mesh dependence. `theory/REVIEW.md` records the bounded independent review. Root postprocessing `python3 root_comparison.py` adds nearest-ζ comparisons after the W finalizer; rerun it if regenerating the producer root CSV. All data remain numerical diagnostics. No source files outside this task directory, route-state files or Lean declarations are changed.

The large complete root CSV and four all-prefix JSON files are published losslessly in the split data archive. On a fresh checkout run `python3 unpack_data.py` (Python3.12+) before reading these raw files or rerunning postprocessing. PUBLICATION_ARCHIVE.json binds each exact uncompressed SHA-256 and archive part. Smaller CSVs, reports, profiles, code and validation are directly available; no scientific rows or precision digits were discarded.
