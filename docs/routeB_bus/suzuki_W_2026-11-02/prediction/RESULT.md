# Finite source prediction probe

DIAGNOSTIC_NEVER_A_PROOF.

The source is `ab8d123`, Git blob `b56a16a0540ed3f81858c113bc48de68c909b8c8`; its copy is SOURCE.md. The planted model is **§6.2, (18)**, not §5. It adds gamma=2pi/log2, eta=1/4, multiplicity1 to the actual arithmetic zeta source. The paper's RH-baseline interpretation is conditional; this computation does not assume or establish RH.

|World|h|First negative prefix time|n− at6|Smallest eigenvalue at6|Schur defect at6|
|---|---:|---:|---:|---:|---:|
|zeta|.1|>6 (censored)|0|0.00536624609|0.02044145579|
|zeta|.05|>6 (censored)|0|0.005045831629|0.01540145034|
|zeta|.025|>6 (censored)|0|0.003966191246|0.01116491527|
|dh|.1|>6 (censored)|0|0.01640120444|0.05191966869|
|dh|.05|>6 (censored)|0|0.008855050151|0.03103961422|
|dh|.025|5.45|2|-0.006935457915|0.02331554162|
|plant|.1|2.4|2|-0.5437596586|0.02384378606|
|plant|.05|1.7|2|-1.136715441|0.01660608934|
|plant|.025|1.275|2|-2.274256977|0.01159498201|

The coarser DH grids miss the negative directions detected at h=.025. The plant detection time also changes with resolution. These are finite sampling results, not intrinsic first failure times of the continuous kernel. The final Schur defect can be positive after the accumulated kernel has become indefinite: inertia is retained independently.

## Source and normalization

Write a=1/2 for zeta, 3/2 for DH and j_a(s)=exp(-a s)/(1-exp(-2s)). With c the signed original constant,

`g(t) = -c |t|/2 - S_a(|t|) + sum_(log n<|t|) b_n/sqrt(n) (|t|-log n) - zeta_pole`,

where `S_a(t)=sum_(r>=0)(1-exp(-(a+2r)t))/(a+2r)^2` and the zeta pole is `16 sinh(t/4)^2`. DH has no pole. Zeta b_n is Lambda(n), including every proper prime power. DH uses every coefficient of the exact logarithmic derivative recurrence from dh_matrix.py, including composite coefficients. The smooth sum is evaluated by trigamma minus a rapidly convergent geometric series, with equivalent dilogarithms near0. Earlier passes used these equivalent expressions separately. At0, g is defined exactly0.

The independent constant-mode quadrature checks m=2,4,8 verify `g(L)=-L A00/2`, retaining both source constants and the pole. See each cell JSON for the error.

## Prediction and range guard

The exact structural t=0 row/column is removed, with its b component exactly0. For every other prefix, signed 80-digit LDL retains **all** pivots, including negatives. With nonzero pivots, Kdagger=K^-1, and the reported defect is `d-b* K^-1 b`. No PSD premise, positive-part inversion, or eigenvalue truncation is used. The guarded pivot threshold is recorded in every row; no run triggered it. Original full K has one additional structural zero. The source matrices and LDL reconstruction residuals are computed in mpmath; all full prefix eigenspectra are also saved in the JSON, with a float64 sign-resolution floor recorded in CSV. No eigenvalue lay inside that diagnostic floor. This is not interval certification.

The 120-digit DH h=.025 replay and separate validation.py compare all prefix Schur values/inertias and source entries; selected full eigendecompositions are checked against120-digit matrices. See validation.json for actual errors. Floating eigenspectrum digits beyond their residual bounds are not claimed.

## Hinges

The hinge CSVs vary only the new point; the preceding h=.1 grid history is fixed on both sides. They test every prime-power threshold up to6, using eps=1e-6 and5e-7 except n=331, where eps=1e-7 and5e-8 avoids the shifted log271+0.2 hinge only4.45502638e-7 away. DH g always retains its additional non-prime-power coefficients; the hinge CSV is a prime-power profile, not a census of all DH hinges. The predicted jump is `-2c+2c sum(alpha)`, alpha=K^-1 b. Additional hinges occur at old sample times plus log n, with jump `-2c alpha_j`; they are not mistaken for unshifted prime thresholds. The sign of a scalar prime coefficient alone does not determine a Schur jump.

## Replay

`uv run --with mpmath --with numpy --with scipy python scan.py WORLD H 80 --no-hinges`, WORLD=zeta/dh/plant, H=.1/.05/.025. Repeat DH,.025 at120digits; run validate.py, hinges.py WORLD, report.py, and plot.py (matplotlib).

profiles.png and profiles.pdf show the fine-grid signed innovations and zeta mesh dependence. A finite positive zeta scan supplies no cofinal positivity bound or canonical Hamiltonian.

## Measured controls

- zeta: 98 nonzero prime-power hinges; 79 positive and 19 negative jumps. Maximum smaller-step FD error 0.000362; two-step Richardson error 1.97e-10. These errors are numerical comparisons, not interval bounds.
- dh: 95 nonzero prime-power hinges; 61 positive and 34 negative jumps. Maximum smaller-step FD error 0.00037; two-step Richardson error 8.13e-11. These errors are numerical comparisons, not interval bounds.
- plant: 98 nonzero prime-power hinges; 62 positive and 36 negative jumps. Maximum smaller-step FD error 0.000348; two-step Richardson error 1.89e-10. These errors are numerical comparisons, not interval bounds.

DH h=.025: all240 prefix inertias match at80/120digits; maximum relative Schur change9.95e-76. At t=5.425 the smallest eigenvalue is +0.0002558001270, at5.45 it is -0.0001224797949. The120-digit full diagonalization residual/orthogonality checks give diagnostic eigenvalue error bounds below1.7e-12 at prefixes217,218,240. Source matrix change bound is1.54e-77.
