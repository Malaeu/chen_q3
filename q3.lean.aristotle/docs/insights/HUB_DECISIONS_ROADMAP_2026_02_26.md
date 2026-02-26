# Hub: Decisions Risks Roadmap

Источник: `docs/insights/INSIGHTS_legacy_2026_02_26.md`.
Решения, аудиты, риски, плановые развилки и общая дорожная карта.

## Included Sections

- line 492: Audit (2026-01-29) — PDF vs Lean mainline divergence (in progress)
- line 516: Plan (future de-axiomization) — a_star growth + heat-weight summability
- line 630: Synthesis (2026-01-27, in progress) — Connes–Consani–Moscovici “Zeta Spectral Triples”
- line 661: Synthesis (2026-01-23, in progress) — fixed‑t/τ=0 one‑scale closure
- line 996: Спеки
- line 1140: Tail bound reduction (2026-01-30)

<!-- wave2_related_start -->
## Related Legacy Files (Wave 2)

Связанные standalone-файлы по домену `roadmap`:

- `docs/insights/carleson_implicit_proof_2026_01_17.md`
- `docs/insights/carleson_implicit_proof_2026_01_17.md`
- `docs/insights/explore_agent_for_mathlib_search_2026_01_17.md`
- `docs/insights/h_cap_numerical_estimates_2026_01_14.md`
- `docs/insights/localization_argument_full_analysis_2026_01_16.md`
- `docs/insights/localization_argument_full_analysis_2026_01_16.md`
- `docs/insights/PERIODIZATION_BOTTLENECK_FIX.md`
- `docs/insights/schur_test_l2_vs_linfty_2026_01_20.md`
- `docs/insights/szego_bottcher_not_needed.md`
- `docs/insights/t_parameter_forms.md`
- `docs/insights/v1_surprise_real_tp_bounds_2026_01_14.md`
- `docs/insights/v4_success_full_tp_bound_2026_01_14.md`
<!-- wave2_related_end -->

## Content

<!-- legacy_line:492 -->

## Audit (2026-01-29) — PDF vs Lean mainline divergence (in progress)

- RH_Q3.pdf формулирует **классический Weil‑конус**; mainline Lean использует
  **`Weil_cone_tau0` (τ=0 + фиксированный B‑range)**.
- PDF использует two‑scale (`t_sym`, `t_rkhs`); mainline использует single‑scale `t_critical`.
- Полная секция‑к‑Lean карта + сводка расхождений:  
  `docs/struktura_q3_with_mapping_toLEAN.md` (раздел “2026-01-29 Audit — PDF vs Lean Mainline”).


<!-- legacy_line:516 -->

## Plan (future de-axiomization) — a_star growth + heat-weight summability

- a_star growth: use digamma asymptotics (DLMF 5.11) to show
  `|a_star ξ| <= C0 + C1 * log(1 + |ξ|)` on tails, and combine with
  `a_star_bdd_on_compact` on `Icc (-R) R` to get a global bound.
- heat-weight summability: use basic bound `vonMangoldt(n) <= log n` and
  `xi_n = log n / (2*pi)` to show
  `w_Q n * exp(-c * (log n)^2) * |log n|` is absolutely summable.
- glue: `log(1+|ξ|) <= |ξ|` then Gaussian integrability of
  `(1 + |ξ|) * exp(-c ξ^2) * |ξ|`.


<!-- legacy_line:630 -->

## Synthesis (2026-01-27, in progress) — Connes–Consani–Moscovici “Zeta Spectral Triples”

Source: Zotero ingest
`full/q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md`
(paper: *Zeta Spectral Triples*, Connes–Consani–Moscovici).

**Core idea (from cache):** construct self‑adjoint operators `D(λ,N)` as
rank‑one perturbations of a spectral triple for the scaling operator on `[λ⁻¹, λ]`.
The construction uses **finite Euler products** (`p ≤ x = λ²`). Spectra of `D(λ,N)`
numerically align with low ζ‑zeros. Self‑adjointness relies on an **extension of the
Carathéodory–Fejér theorem for Toeplitz matrices**.

**Formal Chain (possible bridge points):**
- CF‑extension ⇒ **Toeplitz self‑adjointness** in a finite‑rank/finite‑prime regime.
  This could become a *formal* lemma stub that mirrors our Toeplitz/Rayleigh steps
  (Szegő–Böttcher + Rayleigh bounds).
- Rank‑one perturbation control ⇒ spectral stability lemma (if formalized,
  could justify controlled operator deformations in the A3 path).

**Speculative Edges (do NOT activate without stubs):**
- “Finite Euler product” ⇒ **prime‑term truncation** with explicit error bound.
  Potential leverage for PrimeCert Lipschitz/ margin bounds, but currently speculative.
- Spectral triple / scaling operator formalization is out of scope for the mainline.

**Actionable next step (lightweight):**
- Add a speculative edge entry in the external graph:  
  `CF_toeplitz_selfadjointness` (source = 6H6WHGDU, status = speculative).
- If we pursue it: create a Lean stub lemma in `Q3/Proofs/PrimeCert/` or
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` documenting the intended statement
  (self‑adjoint Toeplitz from truncated data), **without** wiring it into mainline.


<!-- legacy_line:661 -->

## Synthesis (2026-01-23, in progress) — fixed‑t/τ=0 one‑scale closure

- q3search "AtomCone_K_fixed" / "Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom" failed: 403 Spend limit exceeded.
- websearch "AtomCone_K_fixed Lean" failed: 403 Spend limit exceeded.
- Target lemma: close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Option A (primary): implement fixed‑t cone/τ=0 guard in `Q3/Axioms.lean`, then wire one‑scale chain using
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`, `Q3/Proofs/RKHS_cap_rayleigh.lean`, and `Q3/Proofs/Params_Critical.lean`.
- Option B (fallback): keep RKHS embedding path; fill missing `kernel_dict` in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  or discharge `hA` via `Q3/Proofs/RKHS_Interface_C1.lean` + `Q3/Proofs/Heat_RKHS_Interface.lean`.
- Success check: `lake env lean Q3/Atoms_Positive.lean` and `./scripts/check_axioms.sh` drop the axiom.
- Progress: `t0_critical` wired into `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
  `Q3/Atoms_Positive.lean`, `Q3/T5_Transfer.lean`, `Q3/AxiomsTheorems.lean`;
  BaseAtomCone guard `Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS` added.
- Proshka request drafted: `full/q3.lean.aristotle/PROSHKA_REQUEST_5.md` (one‑scale A3 floor + cap at t_critical).


<!-- legacy_line:996 -->

## Спеки

- Основной спецификатор инвариантов: `docs/PROJECT_SPECS.md`.

---


<!-- legacy_line:1140 -->

## Tail bound reduction (2026-01-30)

- Added `prime_b_grid_tail_bound_of_tail_term` in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean`:
  it reduces the prime‑term tail inequality to the **pure tail term**
  `prime_b_grid_tail_term` using `Summable.tsum_le_tsum`.
- Remaining inputs: summability of the tail term and the numeric inequality
  `∑' n, prime_b_grid_tail_term (n + (N+1)) ≤ prime_b_grid_tail_bound`.
