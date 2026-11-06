# CODEX TASK — OPTIMAL NB COEFFICIENTS vs MÖBIUS TAPER: WHERE DOES THE OPTIMUM "REPAIR" MÖBIUS? (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3 (public)

- Branch `rh_clean`:
  - this task;
  - optimal coefficients, `docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/part_a_coefficients.csv` (commit ba5654b4), with the Gram/Vasyunin code in the same folder;
  - rational certificate witnesses, `docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/certificate_witness_N*.json` (commit a180142f).
- Branch `proshka_inbox_2026-10-31`, for definitions:
  - R8, commit 70c4e6b0;
  - R7 B, commit 8a994500, §2 (the discrete/continuous relation) and §7.4 (V_N);
  - reciprocity verdict, commit aabf1a70, §2: a_n = μ(n)·log(N/n)/log N and the residual convention R_N(k) = 1 + Σ a_n r_n(k).
- Result: push to `rh_clean` per AGENTS.md.

## Question (owner's hypothesis)

The Möbius taper's error is sensitive to small |ζ′(ρ)| (near-colliding zeros, Lehmer pairs). In the literature this is the H₋₁/J₋₁ hypothesis of Bettin–Conrey–Farmer and Ng. The optimal NB coefficients are not: by Báez-Duarte, d_N → 0 ⇔ RH alone.

Does the optimum differ from Möbius **systematically**? If it does, is the improvement **localised near zeros with small |ζ′(ρ)|**?

## PART A — coefficient space

For N ∈ {500, 1000, 2000, 5000}:

1. Load c^opt. Align sign and convention with a_n = μ(n)·log(N/n)/log N. Prove the alignment by recomputing both errors, see J1–J2.
2. Report:
   - cosine similarity cos(c^opt, a);
   - δ = c^opt − a;
   - ||δ||² / ||c^opt||².
3. Energy split of ||δ||²: n ≤ √N vs n > √N; n > N/2; squarefree vs non-squarefree n (where μ = 0); primes, prime powers, other n.
4. **Stability.** Correlate the profiles δ_n(N₁) and δ_n(N₂) as functions of n/N, for all pairs of N, after rescaling. A stable profile means systematic; an unstable one means noise.
5. **Regression** of δ_n on the features μ(n), μ(n)·log n/log N, Λ(n)/log N, 1/n, 1_{n≤√N}, ω(n). Report R².

## PART B — t-side: localisation near zeros

For D = c^opt and D = a, define

    I_D(t) = |1 − ζ(½+it)·D(½+it)|²,  D(s) = Σ c_n n^{−s}.

Use whatever centring R7 B §2 prescribes for the continuous norm; state it.

1. Δ(t) = I_a(t) − I_opt(t), on t ∈ [0, 1000], with a fine grid adapted to zero spacing. mpmath, 20 dps is enough; ζ is computed directly.
2. For each zero ρ_j = ½ + iγ_j with γ_j ≤ 1000 (mpmath zetazero, about 649 zeros):
   - compute |ζ′(ρ_j)|;
   - compute the local improvement W_j = ∫ Δ(t) dt over the half-gaps around γ_j.
3. Report:
   - the Spearman correlation between W_j and 1/|ζ′(ρ_j)|²;
   - the same for W_j against the local gap min(γ_j − γ_{j−1}, γ_{j+1} − γ_j);
   - the 20 zeros with the largest W_j, with their |ζ′|, their gaps, and their rank in 1/|ζ′|.

## JUDGES (build first)

- **J1 (data integrity).** Recompute e_N from the loaded c^opt with the folder's Gram. It must match the ba5654b4 table to 1e−10.
- **J2 (convention).** Recompute E(a) in the same code. It must match the E(V_N) column of ba5654b4 (centred form) to 1e−10.
- **J3 (two sides agree).** For the fixed coefficient vectors, the t-integral (1/2π)∫ I_D(t) dt/(¼+t²), with an explicit tail bound beyond the computed range, must equal the discrete norm via the exact relation of R7 B §2. If R7 B gives only inequalities for fixed coefficients, report both numbers and the inequality; do not invent an identity.
- **J4 (null for Part B).** Recompute both Spearman correlations against 1000 random permutations of the zero labels. Report empirical p-values. A correlation inside the null band is NOT evidence.

## PRE-REGISTERED PREDICTIONS (Mythos, before any run; scored after)

| ID | Prediction | p |
|---|---|---|
| Q1 | cos(c^opt, a) ≥ 0.8 at N = 5000 | 0.55 |
| Q2 | δ is systematic: profile correlation ≥ 0.7 between N = 2000 and N = 5000, on the n/N scale | 0.6 |
| Q3 | More than 50% of ||δ||² sits at n > √N | 0.5 |
| Q4 | Non-squarefree n carry ≥ 10% of ||c^opt||² | 0.5 |
| Q5 (owner hypothesis) | Spearman(W_j, 1/\|ζ′(ρ_j)\|²) ≥ 0.3 with permutation p < 0.01 at N = 5000 | 0.45 |
| Q6 | Spearman(W_j, small gap) has the same sign as Q5, with p < 0.01 | 0.45 |

## OUTPUT

Folder `docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/`, containing:
- PREREGISTRATION.json, committed before any numbers;
- the scripts (uv, ASCII progress with ETA);
- the CSVs: coefficients, δ, features, and the per-zero table (γ_j, |ζ′|, gaps, W_j);
- plots: δ_n vs n/N for each N; W_j vs 1/|ζ′|²; Δ(t) near the top-5 zeros;
- REPORT.md with J1–J4, the tables, HIT/MISS for Q1–Q6, and every truncation stated.

Give the commit, the paths and the blobs in the final message.
