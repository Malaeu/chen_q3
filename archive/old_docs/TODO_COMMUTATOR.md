# Commute–Resonance Build Plan

Goal: codify the “commutator resonance” experiment so that the math side can prove the two key lemmas (No‑fake‑resonance, Explicit bridge).

## Modules to implement

1. `src/hamiltonian.py`
   - `build_hamiltonian(K, M, X_max, kernel='fejer-heat', t_sym=None)` -> `H (numpy.ndarray)`
   - Uses existing Q3 code: Toeplitz part from arch symbol; prime part with weights `w(p)=2*Lambda(p)/sqrt(p)` on nodes `xi=log n/(2pi)` up to `X_max`.
   - Ensure Hermitian (H ≈ H.T.conj), return also metadata (nodes, weights).

2. `src/shift.py`
   - `delta_from_X(X)` -> float (default `2/(2*pi*log X)`).
   - `phase_shift(K, M, delta, xi_grid)` -> diagonal unitary S (phase in frequency basis).
   - Optionally: `cyclic_shift(M, step)`.

3. `src/twins_state.py`
   - `build_twins_vector(X_max, xi_grid, kernel='gauss', t=None, use_chi4=False)` -> normalized vector `psi` on the xi grid.
   - Base weights: `v_p = Lambda(p)*Lambda(p+2)` if (p,p+2) twin else 0. If `use_chi4`, multiply by `chi4(p)*chi4(p+2)`.
   - Lift to xi grid via Gaussian/heat kernel centered at `xi_p`.

4. `src/commutator_resonance.py`
   - Given H, S, psi:
     - `C = psi.conj() @ (H@S - S@H) @ psi`
     - `D2 = np.vdot((H@S - S@H)@psi, (H@S - S@H)@psi)`
     - `R = sqrt(D2) / np.linalg.norm(H@psi)`
   - Sweep over X (or N), store table: X, K, M, |C|, sqrt(D2), R.
   - Optional log–log fit for sqrt(D2) vs log X.

5. `src/spectral_capture.py`
   - Diagonalize H locally; expand psi = Σ a_j v_j.
   - Compute phases φ_j where `S v_j ≈ e^{iφ_j} v_j` on the support of `|a_j|`.
   - Metric: `Var_phi = Σ |a_j|^2 (φ_j - φ̄)^2` (small ⇒ resonance).

6. `src/twin_correlation_bridge.py`
   - Compute classical `T(X) = Σ_{n≤X} Λ(n)Λ(n+2)` and smoothed `T_w(X)`.
   - For the same X, report commutator metrics (|C|, D2, R).
   - Empirical correlation between `T_w(X)` and `D2`.

## Data products

- Tables (CSV/JSON) for each sweep: X, K, M, delta, |C|, sqrt(D2), R, T(X), T_w(X).
- Plots: sqrt(D2) vs log X; R vs log X; T_w vs sqrt(D2).
- Spectral capture plots: |a_j| distribution and phase variance Var_phi vs X.

## Notes

- Reuse existing Q3 builders (`q3_galerkin_phase1.py`, etc.) where possible to avoid code drift; wrap them rather than duplicate logic.
- Keep kernels consistent with main proof (Fejér×heat). Expose parameters t_sym, kernel bandwidth.
- Ensure all vectors/matrices live on the same xi grid for H, S, psi.
- Start with modest sizes (K≈2, M≈256, X≈1e6) to validate pipeline; then scale.

Deliverables: runnable scripts under `src/` plus a `make`/`uv run` target that produces the tables and plots into `output/`.
