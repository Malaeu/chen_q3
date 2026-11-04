# Method and replay

DIAGNOSTIC_NEVER_A_PROOF. The computation is staged: immutable prediction commit; Gate0; mandatory controls; stop. There is no CCM scan implementation because the prescribed control fails and the literal metric already has an exact universal scalar minimizer.

## Gate0

`scripts/gate0.py` verifies the two source-file Git blobs before importing the unchanged analytic builder. Set CCM_SOURCE_ROOT to the repository's ground_state_zeros_2026-11-03/inputs directory when replaying on another machine. Dependencies: mpmath, gmpy2, numpy, python-flint. Run `python scripts/gate0.py` from any working directory after preserving PREREGISTRATION.json.

The scalar H₀₀ is c+(2/L)∫₀ᴸ u j(u)du+2∫ᴸ∞j(u)du, with c=−EulerGamma−log(8π)−π/2 and j(u)=e^(−u/2)/(1−e^(−2u)). The removable integrand value at0 is1/2. The exact tail is2[atanh(e^(−L/2))+atan(e^(−L/2))]. P₀₀ uses the pinned pole vector and B₀₀ the complete von Mangoldt prime-power support. These scalar values are compared independently with Suzuki's Lerch/Catalan formula and with the builder's actual matrix element. No zero list or changed matrix is used.

All scalar calculations use80mpmath decimal digits. Builder320bits gives360working and392special-function bits under its unchanged implementation. The point-comparison tolerance is1e−40; this is not interval quadrature or a proof of that numerical error bound. A failure breaks the gate loop and stops the scan.

## Control and physical normalization

`scripts/controls.py` requires GATE0.json PASS. It uses m16 and rho=cb=1. In y=x/b the physical orthonormal even basis is d_j(−1)^j cos(πjy)/sqrt2. Define F0(z)=sin(z)/z and Fj(z)=sqrt2*z*sin(z)/(z²−π²j²) for j>0. Then Kij=(2/π)∫₀¹FiFj. The differential Galerkin matrix is obtained by integrating −(1−y²)phi_i′phi_j′−y²phi_i phi_j. The J/T closed forms and five direct-entry checks are in the script/review.

The reported fixed-operator residual is ||[D,K]||F/(||D||F||K||F), exactly the objective after D is normalized in matrix image space. The negative control uses seeded rational symmetric entries, then the exact admissible scalar witness. Both controls use80dps. Only controls are run; the larger source grid is not generated.

## Why an ordinary coefficient SVD is insufficient in general

If E_l are Galerkin images of the six coefficient monomials, define G_lk=<E_l,E_k>F and C_lk=<[E_l,X],[E_k,X]>F. The task's norm requires minimizing tᵀCt/(tᵀGt||X||F²), after removing any coefficient-map kernel. A plain SVD with Euclidean coefficient normalization generally computes another metric unless G is whitened. This distinction does not remove the present scalar short circuit: the constant-b image is I and its commutator column is exactly zero in either formulation. No coefficient normalization or basis whitening was used as a hidden repair.

## Analytical table and stop semantics

R.csv lists the exact normalized scalar minimizer for all30 requested cells. Its zeros are analytical, conditioned on X≠0, not rounded measurements or a non-scalar search. There is no need to construct the planted quartet to know that I commutes with it. This observation is not a claim that every other commutant of A commutes with Q.

The fixed Slepian residual is5.3892e−5, so the prescribed positive control does not meet1e−25. The unconstrained literal minimum is0 for both positive and negative kernels. The report distinguishes these facts rather than calling the literal scalar zero a successful nontrivial Slepian control. The scan remains void.

`scripts/verify.py` validates the saved identities, registration chronology/blob, control normalization, analytical table and all SHA256SUMS. The primary Suzuki PDF and whole matrix-builder outputs remain local; their provenance and exact pins are recorded in INPUTS.json. The deliverable makes no RH claim and changes no route-state or export.
