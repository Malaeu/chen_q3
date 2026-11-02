# Hypothesis cards

DIAGNOSTIC_NEVER_A_PROOF. No card changes Route B = CHALLENGER / NOT_RH.

## 1. Mesh-stable exponential decay — rejected in the registered finite range

HYPOTHESIS: log sigma² is linear in t with a slope stable within 10% on
the four meshes. Prior supplied by Mythos: 0.35. Fixed tests were registered
in core/PREREGISTRATION.md before the calculations.

EVIDENCE: on [1,6], slopes are −0.162470, −0.217053, −0.270628,
−0.285682 for denominators 32,64,128,256; R² is 0.96497,0.96677,
0.96381,0.98544. The slope range is 50.5% of the median absolute slope.
The fixed [1,3] and [3,6] tests also fail. The last two [1,6] slopes
differ only 5.4%; this does not reject eventual convergence on finer grids.

WHAT KILLS IT: the preregistered finite-range criteria already fail. Stop
fitting alternate windows or adding parameters in this experiment.

HANDOFF TO PROSHKA: the generic reflection relation
sigma_n²=sigma_(n−1)²(1−alpha_n²) records the observed curvature, but
|alpha_n|<1 remains an unpaid source inequality. Conditional on RH,
positive innovations are bounded above by 2Psi(Delta). This generic bound
does not establish a particular decay law. A proposed asymptotic law must
be separately specified and pass the planted judge.

## 2. Euler cone Q_f*(log p^k) <= 0 — rejected by zeta itself

HYPOTHESIS: the optimal full-history residual has nonpositive
autocorrelation on every prime power. Residual preregistration prior: 0.25.

EVIDENCE: genuine positive-history zeta at t=1 has
Q(log2)=+0.4994268897314703 (mesh32) and +0.3679395751355681 (mesh64).
At t=6,mesh64, 89 of 98 nonzero prime-power correlations are positive,
9 negative. Reoptimised source-coefficient finite differences agree with
−Q. These are not arbitrary nonoptimal test functions.

WHAT KILLS IT: the positive values above already do. Do not use this cone
as a zeta property or as a selector separating zeta from DH.

HANDOFF TO PROSHKA: retain source (11), partial sigma²/partial c_n=−Q,
with its full optimizer dependence and signed correlations. This result
rules out the proposed finite cone, not other arithmetic identities.

## 3. Local-cusp magnitude as a discriminator — rejected

HYPOTHESIS: the normalization sigma²/(2Psi(Delta)) itself identifies the
true world. This was an exploratory comparison, not a new preregistered
asymptotic claim.

EVIDENCE: at t=6,Delta=1/256 the ratio is 0.2156143163 for zeta and
0.2161578762 for the plant, although the plant has two negative directions.
Its signed pivot has become positive again. Source (17) also has the same
fixed-history cusp in the plant.

WHAT KILLS IT: near-equal endpoint scales with different accumulated
inertia. Kill endpoint-only acceptance; preserve the complete prefix index.

HANDOFF TO PROSHKA: inverse-history constants in the local remainder
cannot be discarded when refining the history. A finite planted failure
cannot be repaired by a later positive algebraic pivot.

## 4. Exact source compensation matters — finite diagnostic supported

HYPOTHESIS: changing the arithmetic source while preserving the local
archimedean cusp breaks positive continuation. Registered C1 probability
0.8 for at least one control, C2 probability 0.3 for all three.

EVIDENCE: all three controls fail. At mesh64 the first negative length
is 0.78125 for half and three-halves of every positive von Mangoldt atom,
and 0.75 when all atoms n>=2 are replaced by exp(s/2)ds on [log2,infinity).
True zeta
stays positive through 6. All 384 prefix indices agree at 100/160 digits;
negative residuals are independently replayed against the direct form.
These changes are controls, not asserted completed L-functions.

WHAT KILLS IT: independent source/normalization failure, or a precision
repeat reversing the first negative. Neither occurred. This finite test
does not show that an Euler product plus a functional equation supplies a
positive continuation bound.

HANDOFF TO PROSHKA: at zeta t=6,mesh64, the source terms are
4.880575022 −11.756894320 +28.349425257 −21.464876878 =0.008229082.
The full signed compensation on the optimized residual is the object
needing an estimate. Neither absolute budgets nor positive coefficients
alone explain its sign.

## 5. Planted negative-capacity threshold — supported finite explanation

See review/CARD_PLANTED_HAZARD.md for the preregistered, independently
computed rank-four factorization and its two-dimensional threshold.
It passes the planted judge on all four meshes and explains the first
failure. It is not a source estimate for zeta or a finite-rank model of DH.

No zeta-specific arithmetic law guaranteeing all future signs was found.
The bounded experiment closes here; no route promotion or RH claim follows.
