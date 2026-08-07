# PROSHKA REQUEST — UNIFIED CONDITIONAL CHAIN (CCM+SUZUKI+ROUTE B) AND Δ-PROBE RATIFICATION

SELF_CONTAINED: yes (no external chat context required)
DATE: 2026-08-06
AUTHOR: Mythos (orchestrator)
REPO: github.com/Malaeu/chen_q3 · BRANCH: rh_clean · TIP: 6d4dd030a0fe9724065b7f74f7da8e2cfadf331e
BOUNDARY: DELEGATED_STRATEGIC_REVIEW (exactly ONE batch; machine classes TRY_/KILL_/RUN_ only)
PROPOSED_LANDING: docs/routeB_bus/proshka/PROSHKA_VERDICT_UNIFIED_CHAIN_2026-08-06.md (+ SHA-256)

CONSTRAINTS IN FORCE (unchanged): CHALLENGER / NOT_RH · BUS_010: VOID · GOAL_055: HOLD ·
G2/CCM front FROZEN (this request does NOT unfreeze it; external imports stay candidates) ·
PX_RH_CLAIM is the only owner gate · CLOSED_GOAL_IMMUTABLE · frozen glossary
("beam" below is prose alias only, not a new term).

---

## 0. TL;DR OF THE ASK

Four rulings in one batch:
R1 audit the conditional chain S1–S5 below (validity + hidden gaps);
R2 after the pending Codex push: verify the V_n_m-completeness closure and rule which
   056q premise it discharges;
R3 ratify the Δ-probe as the next RUN_ (decisive-test-first), register/adjust predictions;
R4 rule on planted-violation (judge-integrity) protocol going forward.

---

## 1. THE ASSEMBLED CONDITIONAL CHAIN (three inputs ⇒ RH)

Notation. Window [λ⁻¹, λ], multiplicative measure d*u = du/u; log coordinate u = e^x,
a = log λ ⇒ interval [−a, a], Lebesgue. Suzuki's threshold "first prime enters" is
λ² = 2 ⇔ a = ½·log 2. QW_λ = semilocal Weil quadratic form on the window
(primes p ≤ λ²); W_λ = its Friedrichs operator (= Suzuki's A_a, his Thm 1.1:
Friedrichs extension of B_a = D*G_a D on L²₀(−a,a), spectrum discrete, bounded below).

S1 — FINITE REALITY (cheap side).
  (i) CCM Thm 1.1 (arXiv:2511.22755): with ε_N the smallest eigenvalue of the
      truncation QW_λ^N to E_N = span{V_k : |k| ≤ N}, ASSUMED simple with even
      eigenvector ξ, the rank-one perturbed operator
      D_log^{(λ,N)} = D_log^{(λ)} − |D_log^{(λ)} ξ⟩⟨δ_N|
      is self-adjoint w.r.t. QW_λ^N − ε_N⟨·|·⟩ on E_N/ℂξ ⊕ E_N^⊥;
      det_reg(D − z) = −i·λ^{−iz}·ξ̂(z); ξ̂ entire, ALL zeros real = spec(D).
      CLASS: THEOREM conditional on (simple, even) at truncated level.
  (ii) Suzuki Thm 1.5 (arXiv:2606.09096): unconditional, ALL a — the self-adjoint
      extensions D_{a,θ} of i·d/dx on the de Branges space H(T_a) have eigenvalues
      = the (all real) zeros of W(a,θ;z) (his eq. 1.11). Needs only finitely many
      primes at fixed a. CLASS: THEOREM. (Strictly stronger than CCM Thm 5.10,
      which consumes simple+even as hypotheses.)

S2 — INPUT A (open): simple + even for ALL λ.
  Known: Suzuki Thm 1.4 — for sufficiently SMALL a only: λ_a positive, simple,
  even eigenfunction; λ_a = log(1/a) + μ₁ − log(2π) + ψ(2) − 1 + O(a), μ₁ > 0.
  Mechanism: limiting Dirichlet form generates a positivity-improving semigroup
  (Beurling–Deny + irreducibility ⇒ Perron–Frobenius ⇒ simple, fixed-sign hence
  even ground state), transferred to A_a by Kato perturbation. CLASS: THEOREM
  (small a). OPEN: every prime threshold λ² = p re-attacks the kernel sign;
  no published result past λ² = 2. Closing A for all λ removes the hypotheses
  of S1(i) and of CCM Thm 5.10 entirely.
  Sector fact (Suzuki eq. 4.10, THEOREM): λ_a = min(λ_a⁺, λ_a⁻) over even/odd
  sectors — but NO bound on the sector separation is proven.

S3 — INPUT B (open): prolate guess ≈ arithmetic ground vector.
  Guess (CCM §7, from zeta-cycles): k_λ := 𝓔(h_λ), 𝓔(f)(u) = u^{1/2}·Σ_{n≥1} f(nu),
  h_λ = the unique zero-integral combination of h_{0,λ}, h_{4,λ}, eigenfunctions of
  PW_λ = −∂_x((λ²−x²)∂_x) + (2πλx)².
  PROVEN (import candidates, THEOREM class, pending source audit):
    · CCM §7 Lemma "hermfact1": k̂_λ → Ξ uniformly on closed substrips
      |Im z| < ½, rate O(λ^{−1/2−α}) on Im z = α; tail killed by Poisson
      symmetry k(u) = k(1/u).
    · Meixner–Schäfke Satz 9 (γ = 2πλ²): max_{[−λ,λ]} |h_{n,λ} − h_n| ≤ c·λ^{−2},
      n = 0,4; hence same for h_λ.
    · Fuchs 1964 Thm 1: 1 − χ(λ) ~ (2^{14}/3)·√2·π⁵·e^{−4πλ² + 9 log λ}.
  NEEDED: ‖k_λ − c_λ·ξ_λ‖ → 0 in weighted L¹(d*u), weight u^η + u^{−η}, with
  RATE o(λ^{−η}) for EVERY η < ½ (weight transfer from L²(window) costs ~λ^η;
  without the rate, Hurwitz on substrips does not engage).
  Route: quasimode. With μ_λ = Rayleigh quotient of k_λ and r_λ = (W_λ − μ_λ)k_λ:
  sin∠(k_λ, ground) ≤ ‖r_λ‖ / Δ_λ (Kato sin-θ; Temple/Kato–Temple two-sided
  localization; Reed–Simon IV §XIII.2). r_λ is computable in the V_n basis via the
  explicit matrices W_{0,2}, W_p, W_ℝ of CCM §4.
  RISK (registered, K6): CC zeta-cycles (Enseign. Math. 69, 2023) observe ~2λ²
  VERY small eigenvalues of the projection pair — if the QW_λ bottom is a
  near-degenerate cluster, Δ_λ is superpolynomially small, the naive quasimode
  dies, AND the target itself ("the" ground vector) becomes ill-posed inside the
  cluster; the object must then be reformulated (cluster projection / cluster
  determinant), which also reshapes CCM's ladder. Mythos prediction P-Δ:
  p ≈ 0.6 that Δ_λ decays faster than any power.
  FACT (evidence of absence, checked): NO published bound/asymptotic/numeric for
  Δ_λ = λ₂ − λ₁ of QW_λ in: CC Selecta 27 (2021) №77; CC Enseign. 69 (2023);
  CCM Ann. Funct. Anal. 15 (2024) №87 / arXiv:2310.18423; CCM arXiv:2511.22755;
  Connes–van Suijlekom CMP (2025) 406:312 / arXiv:2511.23257; Suzuki JLMS 2023
  and arXiv:2606.09096; third-party numerics arXiv:2607.24830 (μ₁ ≈ 0.101,
  λ₁ only) and arXiv:2601.12133. Our probe would be first.

S4 — INPUT C (open, OURS): Galerkin span at fixed λ, N → ∞.
  Truncated ground data (ε_N, ξ_N) → (ε_λ, ξ_λ) and det_reg(D_log^{(λ,N)} − z)
  → −i·λ^{−iz}·ξ̂_λ(z) locally uniformly. CCM state this as strategy (§7, first
  bullet), no proof. This span is exactly what the Route B pipeline is building:
  see §2 (056q two-premise receiver; 056s exact complement-Parseval machinery;
  V_n_m completeness in flight).

S5 — TRANSFER. Finite spectra real (S1) + ξ̂_{N,λ} → Ξ locally uniformly on the
  open substrips (S2+S3+S4 with rates) + Hurwitz on zeros of uniform limits +
  classical zero-free boundary lines Re s ∈ {0,1} (Hadamard–de la Vallée Poussin)
  ⇒ all zeros of Ξ real ⇒ RH. The Hurwitz consumer is already wired on our side
  (CanonicalRHRouteSkeleton, SlotS2 slot).

CONCLUSION (conditional theorem, no input proven anywhere):
  (A for all λ) ∧ (B with rate o(λ^{−η}) ∀η<½, in the correct gap-world)
  ∧ (C at fixed λ) ⇒ RH.

---

## 2. WHAT THE REPO ALREADY HOLDS (verify from tip 6d4dd03)

Machine-verified (paths relative to repo root):
  · Sorry frontier 0 active / 0 root-impacting over 3340 Lean files; roots
    Q3.Main.RH_of_Weil_and_Q3 (66 files), RH_of_shifted_atom_route —
    q3.lean.aristotle/ACTIVE/graphs/SORRY_FRONTIER.md (2026-08-06 19:01 UTC).
  · 056a–056p: 17/17 CLOSED (Galerkin scaffolding: log-window transport +
    orthonormality 056l; finite reconstruction 056m; contract 4B discharged
    056k+056p) — docs/routeB_bus/056*.{goal,answer}.md.
  · 056q CLOSED CONDITIONAL: two-premise selected-residual L² decay receiver;
    premises = selected projection convergence AND SelectedProjectionTailDecay S;
    unconditional decay OPEN — docs/routeB_bus/056q_d0_selected_residual_l2_decay_receiver.*,
    verdict docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL056_SELECTED_RESIDUAL_L2_DECAY_2026-08-06.md.
  · 056r OPEN: universal tail theorem shape KILLED by judge; same-m source
    repair selected — docs/routeB_bus/056r_d0_prolate_source_n_coherence_repair.*,
    verdict …PROLATE_SOURCE_N_COHERENCE_2026-08-06.md.
  · 056s CLOSED: EXACT_RESULT G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED —
    complete Hilbert basis + summable dominating weight ⇒ exact complement
    Parseval identity (coefficient tsum on the complement of the retained Finset);
    2 public theorems, 1 private; 2 load-bearing negative plants; explicitly does
    NOT yet prove V_n_m completeness or log-window unitary transport —
    docs/routeB_bus/056s_d0_generic_hilbert_basis_weighted_tail.answer.md.
  · Canon flags: H2b, G3, Theorem510RealZeroBridge OPEN; CCM
    operator/determinant/real-zero package classified
    SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY —
    q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md.
  · RegularRow blocker card (shared stone with S3):
    q3.lean.aristotle/ACTIVE/pipeline/oracle_questions/2026_08_05_routeb_g5_mode4_regular_pswf_row.md.
  · PSWF source dossier: docs/routeB_bus/imports/PSWF_STURM_LIOUVILLE_SOURCE_DOSSIER.md.
  · Spine: orchestrator/state/SPINE_VIEW.md — P9 ACTIVE, 11 delegated reviews,
    0 violations, PX/RH NOT_READY.

OWNER_REPORTED_AHEAD_OF_PUSH (relayed 2026-08-06 evening; tip still 6d4dd03 =
"[Docs] Research Goal 056 V_n_m completeness"; DO NOT consume before the push,
verify from bus artifacts after it lands):
  · V_n_m proven a COMPLETE Hilbert basis (not merely orthonormal);
  · instantiation through the 056s theorem ⇒ EXACT infinite coefficient sum
    (complement-tsum Parseval) on the modeSet complement;
  · 8/8 mutation plants fired correctly;
  · temporary sorries removed.

---

## 3. MAPPING inputs ↔ assets

  INPUT C (Galerkin span): 056s Parseval machinery + V_n_m completeness (pending
    push) + 056q receiver — the completeness result is the natural supplier of
    the 056q premise SelectedProjectionTailDecay via the exact complement tsum.
    RULING NEEDED (R2): confirm or kill this binding after push.
  INPUT B: r_λ computable in our V_n basis with CCM §4 matrices; residual bounds
    feed from MS Satz 9 / Bonami–Karoui / Dunster; Δ_λ unknown ⇒ probe (R3).
    RegularRow (genuine prolate source inhabitation) is the same stone as
    "k_λ vs ξ_λ" — one quarry, two labels.
  INPUT A: outside our current fronts; candidate line = extend Suzuki's
    positivity-improving argument across λ² = 2 (numerics first). No front
    change is requested here; classification only.

---

## 4. THE FOUR RULINGS (single batch; TRY_/KILL_/RUN_ only)

R1 AUDIT_CHAIN. TRY_ or KILL_ the conditional theorem of §1 as stated. Hunt
   specifically: (a) order of limits N→∞ vs λ→∞ (any hidden uniformity in N
   needed at S4→S5?); (b) evenness convention u ↦ u⁻¹ vs our centered Müntz
   coordinate — is the involution the same after transport (056l)?; (c) the
   weight-transfer cost λ^η and whether o(λ^{−η}) ∀η<½ is exactly sufficient for
   Hurwitz on all substrips; (d) the cluster-world failure mode of S3 (is the
   ground-vector target well-posed if Δ_λ collapses; what replaces it);
   (e) recurrence of prime thresholds in S2 (does a per-threshold induction
   scheme even typecheck); (f) the normalization e^{a+ib s} in CCM's det_reg
   convergence — any hidden constant drift.

R2 VERIFY_AND_BIND (after Codex push). Verify V_n_m completeness closure from
   the pushed bus artifacts (goal/answer + plant log + #print axioms trace).
   Then rule: does (056s exact complement Parseval) ∘ (V_n_m completeness)
   discharge premise SelectedProjectionTailDecay of 056q — TRY_BIND, or name
   the exact residual obligation if not (KILL_ the binding with the missing
   lemma named). If it discharges: state which single premise of 056q remains
   and its cheapest supplier.

R3 RATIFY_PROBE (RUN_ class). Δ-probe spec: assemble QW_λ^N matrices in the
   V_n basis from the explicit entries of CCM §4 (W_{0,2}, W_p for p ≤ λ²,
   W_ℝ); even/odd sectors separately (Suzuki eq. 4.10); grid λ² ∈
   {1.5, 1.9, 2.1, 3, 5, 8, 13, 21, 30}, N up to convergence plateau; outputs:
   λ₁, λ₂ per sector, gap law fit (polynomial vs exponential in λ²), and the
   kernel-sign check of e^{−tW_λ} just above λ² = 2 (positivity-improving
   indicator). Predictions registered BEFORE run (adjust/add yours):
   P-Δ (Mythos): Δ_λ superpolynomially small, p ≈ 0.6.
   P-thr (Mythos): positivity-improving indicator survives just past λ² = 2
   numerically, p ≈ 0.55.
   Scored publicly after the run; no retroactive repair.

R4 JUDGE_INTEGRITY. 056s logs 2 load-bearing negative plants; owner reports
   8/8 across the evening set. Rule: is plant coverage adequate for this phase,
   and is a planted-violation control on approve-verdicts themselves required
   after the 7/7-approve streak observed earlier in the 056 series.

NON-GOALS: no unfreeze of G2/CCM; no promotion of external imports past
candidate status before source audit; no route promotion; no RH claim.

— end of request —
