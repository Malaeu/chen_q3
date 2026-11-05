# CODEX TASK — ROUND 4 B TRANSPORT LOSS L_m: COMPUTE ITS GROWTH (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3 (public)

- Branch `rh_clean` holds this task file.
- Branch `proshka_inbox_2026-10-31` holds the sources below.
- Result: push to `rh_clean` (or `codex/<name>` + PR into `rh_clean`), per AGENTS.md («Сохранность результатов»).

## SOURCES (read first)

1. Round 4 B verdict. Commit dd22692d, file `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND4_DAMPING_TRANSPORT_2026-11-05.md`, blob ed2bb7f3. Needed sections:
   - §1: the definition of A_m(δ), G_m, Q_f, j(u), c_*;
   - §4: positivity of the terminal H_m(1/2);
   - §5: L_m and Theorem 1;
   - §6: the derivative (6.1)–(6.4).
2. Round 5 verdict. Commit 25f5ac26, file `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND5_PERELMAN_GAUGE_2026-11-05.md`. Needed: the compression B_m(δ) = J_m* H_m(δ) J_m onto the admissible space through the graph isometry J_m. Note: J_m, not a naive projector.
3. Round 3 verdict. Commit 535d2c27, file `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND3_POLE_RENORMALIZED_LIFT_2026-11-05.md`, blob 8d548cb1, §3.1 and the "Квартет" row of the false-world table. This is the planted off-line control.
4. Literal basis f = S_m z, the admissible space K_m = {z_0 = 0, p_m* z = 0} and the pole vector p_m. Take them from the frozen sources cited there:
   - 62f782316d2ba4f83d27db82d0b64e1e8361cad2, blob 2b5e02a0;
   - 8e584bb8.
   - Any existing A_m code in the repo, if present.

   Self-check: G_m = I + diag((2πj/L)²) must equal the Gram matrix of ‖f‖² + ‖f′‖² in your basis. If it does not, stop and report.

## WHAT TO COMPUTE

For each m in the grid, with L = log m:

1. **Matrices.**
   - Build the Hermitian A_m(δ) exactly by §1: Gamma integral, pole term, all prime powers n < m.
   - Build A_m′(δ) by (6.1). Q_{jk}(u) is the bilinear cross-correlation of the basis functions on the zero-extended window; use closed forms where possible.
   - Set H_m(δ) = G_m^{−1/2} A_m(δ) G_m^{−1/2}.
   - Set B_m(δ) = J_m* H_m(δ) J_m.
2. **Eigenvalue velocities** on a δ-grid in [0, 1/2].
   - At each δ: λ_i′ = v_i* H′ v_i, from the eigenvectors v_i of H(δ). The same for B.
   - At near-degenerate points (gap below 1e−9 relative): take λ_max of the derivative compressed onto the cluster. This is the Rellich block rule, §5 of Round 4 B.
3. **Losses.**
   - L_m^full = ∫_0^{1/2} max(0, max_i λ_i′(δ)) dδ for H.
   - L_m^K = the same integral for B.
   - Integrate with a composite rule. Halve the grid until the relative change is below 1e−3, and report the final grid.
4. **Planted control.** L_m^quart, computed as in step 3, with the off-line quartet kernel added to the full Q-form as in Round 3. Use r(s) = 4 cosh(a s) cos(γ s), a = 0.4, γ = 7, with the sign convention of Round 3. Report also a = 1/3.
5. **Profile.** For the largest m, report which eigen-branch carries max_i λ_i′ as a function of δ: low or high frequency index, and its eigenvector's top basis indices.

m-grid: 50, 100, 200, 400, 800, 1600, 3200, plus as far as feasible (target 6400). Dense float64 is enough. Use mpmath only for the checks below if needed.

## JUDGES (build before the run; each must pass, otherwise the run is void)

- **J1 (terminal).** λ_min(H_m(1/2)) ≥ −1e−8·‖H_m(1/2)‖ for every m. Round 4 B §4 proves H_m(1/2) = T*T. A negative value means the implementation is wrong.
- **J2 (derivative).** The central finite difference of H_m(δ) at δ ∈ {0.05, 0.25, 0.45} must agree with (6.1) to a relative error below 1e−6.
- **J3 (identity).** At δ = 0, A_m(0) must equal the literal A_m used elsewhere in the repo, if such code exists. Report the maximum entry difference.
- **J4 (theorem consistency).** λ_min(H_m(0)) ≥ −L_m^full and λ_min(B_m(0)) ≥ −L_m^K. This is (5.4).
- **J5 (control discriminates).** At the largest m, L_m^quart(a = 0.4) / L_m^K ≥ 3. If it is not, the experiment cannot tell the worlds apart; report INCONCLUSIVE and stop the interpretation.

## PRE-REGISTERED PREDICTIONS (Mythos, before any run; scored after)

- **M1** (p ≈ 0.7): L_m^K looks polylog on the grid. The local log-log slope d log L / d log m at the two largest m is below 0.15, and the fit a + b·L² is better than c·m^e.
- **M2** (p ≈ 0.6): L_m^quart(a = 0.4) shows a power slope ≥ 0.25 at the two largest m.
- **M3** (p ≈ 0.55): max_i λ_i′ is carried by low-frequency branches (indices ≲ 2L), not by the top of the spectrum.
- **M4** (p ≈ 0.8): L_m^full ≥ L_m^K. The pole and e0 directions add loss.

## OUTPUT

Folder `docs/routeB_bus/diag/ROUND4B_LM_TRANSPORT_LOSS_2026-11-05/`, containing:
- the script, run with uv; long loops get an ASCII progress bar with ETA;
- a CSV with these columns:
  - m, L, dim, δ-grid;
  - L_full, L_K, L_quart_04, L_quart_033;
  - λ_min H(1/2), λ_min H(0), λ_min B(0);
  - J1–J5 pass/fail;
  - runtime;
- `REPORT.md` with:
  - the table;
  - plots of L vs log m and L vs m (log-log);
  - the fits;
  - the score of M1–M4 (HIT / MISS, no retro-editing);
  - the branch profile from step 5;
  - any deviation from the source definitions, stated explicitly.

Give the commit hash, the paths and the blobs in your final message.
