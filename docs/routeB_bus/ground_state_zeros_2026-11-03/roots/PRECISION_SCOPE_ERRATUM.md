# Authoritative precision-diagnostic scope correction

The frozen raw producer stores `spectral_replay_transform_floor = sqrt(L)*sqrt(dim)*delta_v_infinity` and divides it by the computed Fourier derivative for each polynomial root. The Cauchy-Schwarz expression is a **real-axis, fixed-carrier coefficient-perturbation bound**. It is not a universal complex-plane bound, nor an enclosure of exact-source eigenvector error. Independently recorded low/high changes of L are not enclosed by that coefficient-only bound.

For z=x+iy at the same carrier L, the appropriate coefficient-difference bound is

B(z) = sqrt(dim)*delta_v_infinity * sqrt(sinh(abs(y)*L)/abs(y)),

with limiting value sqrt(L)*sqrt(dim)*delta_v_infinity at y=0. Relative to the stored real-axis expression, the off-axis growth factor is sqrt(sinh(abs(y)*L)/(abs(y)*L)). The frozen per-root unscaled `replay_rootshift_diagnostic` must not be interpreted as an off-axis bound. `PRECISION_SCOPE_INVENTORY.json` supplies corrected off-axis first-order diagnostics and binds the immutable raw artifacts. First-order division by a numerical derivative remains a diagnostic, not a root-error certificate.

The final inventory explicitly checks whether all positive-height critical-strip Fourier roots are real. For a cell with zero nonreal strip roots, its per-cutoff scalar real-axis Cauchy diagnostic is unaffected. For any cell with nonreal strip roots, the corrected inventory is authoritative. Pure-imaginary roots are separately listed, and their raw unscaled diagnostics are superseded by this correction.

Absolute Fourier residuals at a large imaginary argument can be large because the sine prefactor grows exponentially and displayed roots retain 180 digits. Such a residual is not a root-location certificate. Complete polynomial root enclosures and independently rebuilt-vector root replay are the evidence for the locations. The finite-polynomial interval certificates and measured precision replays are unchanged by this diagnostic-scope correction. No exact-source/eigenvector interval certification or mathematical status promotion follows.
