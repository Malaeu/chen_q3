# Track B / E5p Closure Evidence Bundle

Status: EVIDENCE_AND_SPECIFICATION_ONLY.  This file is not a proof of E5p,
not a Lean proof file, not a route mutation, and not a claim of RH.

Requested output path: `trackB/E5P_CLOSURE_EVIDENCE_BUNDLE.md`.
Existing Track B source documents are under `docs/trackB/`.

## 1. Executive Status

| Question | Answer |
| --- | --- |
| Is E5p currently proved? | NO |
| Is there a local E5p closure theorem? | NO |
| Is old Step32F/LDL reusable as a pre-edge reserve? | NO |
| Current `m_old` value | `m_old = 0` |
| Main remaining gap | No same-unit analytic `mu_K` comparison for the finite supplied thresholds. |

The current repository evidence reduces E5p to exact proof obligations.  It
does not close E5p.  In particular, float finite-operator diagnostics and S3
bookkeeping are not proof objects.

## 2. Source Inventory

Only local repository evidence is used.  Web search is not proof evidence.
The untracked `docs/trackB/TRACKB_E5P_*` drafts from the interrupted prior pass
are deliberately excluded as sources.

| File | Why it matters | Exact definitions / theorem names found | Status |
| --- | --- | --- | --- |
| `CLAUDE.md` | Project workflow, no proof claims. | Commit/check rules; no E5p definitions. | DOC |
| `q3.lean.aristotle/PROJECT_WORKFLOW.md` | Aristotle/Lean workflow and proof-gate discipline. | Aristotle and `lake env lean` rules; no E5p theorem. | DOC |
| `SESSION_ENTRY.md` | Session routing guard; confirms not to switch routes silently. | General Q3 entry and active monitors; no Track B E5p theorem. | DOC |
| `q3.lean.aristotle/PROJECT_STATUS.md` | Broad project status. | Mainline/Q3 status; no Track B closure theorem. | DOC |
| `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` | Current mainline and route separation. | Mainline H/PSD-pd route status; no E5p closure theorem. | DOC |
| `q3.lean.aristotle/FORMALIZATION_STATS.md` | Formalization inventory. | Counts/status only. | DOC |
| `q3.lean.aristotle/PROOF_MAP.md` | Legacy proof map. | Global Q3 proof-chain entries. | DOC |
| `q3.lean.aristotle/PROOF_MAP_NEW_KERNEL.md` | New-kernel proof map. | New-kernel route entries. | DOC |
| `docs/trackB/TRACKB_PRICE_TABLE.md:56-68` | Track B control panel. | Route table; old Step32F row; S5C-LP red row. | DOC / NUMERIC / GAP |
| `docs/trackB/TRACKB_PRICE_TABLE.md:70-102` | Records the corrected budget interface. | `budget_slack_K=mu_K-d_K-transfer_guards_K`, `certificate_gap_K=d_K-p_K-finite_guards_K`, `p_K`, `d_K`. | DOC / GAP |
| `docs/trackB/MU_BUDGET_INTERFACE.md` | Corrects the budget interface. | `budget_slack_K=mu_K-d_K-transfer_guards_K`, `certificate_gap_K=d_K-p_K-finite_guards_K`. | DOC / GAP |
| `docs/trackB/TRACKB_PRICE_TABLE.md:211-215` | Status dictionary. | REFUTED/GAP lines for old reserve and LP guards. | DOC / GAP |
| `docs/trackB/VERDICT_B2B.md:8-18` | Current Track B verdict. | Overall Track B status: OPEN, not proved. | DOC |
| `docs/trackB/VERDICT_B2B.md:169-195` | PSD-first tax status. | `S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN`; `B_K=1` tax table. | NUMERIC / GAP |
| `docs/trackB/VERDICT_B2B.md:197-206` | Explicit-formula gap anatomy. | arch / zero_PSD / prime / boundary gap table. | DOC / GAP |
| `docs/trackB/VERDICT_B2B.md:311-359` | Analytic E5 attack inputs. | OPEN analytic E5 attack; same-unit `mu_K` source still open. | DOC / GAP |
| `docs/trackB/S5_FAILURE_ATLAS.md:1-48` | Negative knowledge. | Do not use `L=Mplus*F_v`; clipping may lose edge-control. | DEAD / DOC |
| `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md:1-99` | Old reserve audit. | `m_old`, `E_edge`, `D + tau_D Q^TQ`, Task 0A/0B. | DOC / FORMAL references / GAP |
| `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md:103-153` | Old Step32F certificate inventory. | `C=A-P`, `R=R_kappa`, `D=D_theta`, LDL identities. | FORMAL references / DOC |
| `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md:158-166` | Same-unit comparison audit. | Different operator/basis/G normalization verdicts. | GAP |
| `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md:173-236` | Old-cell raw-edge stress test. | Old raw-edge opnorm about `1.10`; reserve `1e-4..1e-5`. | NUMERIC / PROBE |
| `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md:245-299` | Final old-reserve verdict. | Reuse LDL pattern only, not old reserve as Track B budget. | DOC / GAP |
| `docs/trackB/lemmas/MU_K_SAME_UNIT_BRIDGE_AUDIT.md` | Same-unit bridge audit for theorem assumption (A3). | `E5P_BRIDGE_SOURCE_GAP`: no analytic `mu_K` source in current Track B units. | GAP |
| `docs/trackB/TRACKB_LP_REFORMULATION.md:41-80` | Finite cone and primal object. | `C_K`, `G_K`, `D_K`, `p_K`. | DOC / GAP |
| `docs/trackB/TRACKB_LP_REFORMULATION.md:123-170` | LP dual-clamp and budget wording. | `d_K`, `certificate_gap_K=d_K-p_K-finite_guards_K`, `budget_slack_K=mu_K-d_K-transfer_guards_K`. | DOC / GAP |
| `docs/trackB/TRACKB_LP_REFORMULATION.md:188-204` | LP solve shape. | `lambda G0_K - D0_K >= 0`. | DOC / GAP |
| `docs/trackB/TRACKB_LP_REFORMULATION.md:264-281` | LP status dictionary. | `LP_GAP_NONPOSITIVE`; no proof yet. | DOC / GAP |
| `docs/trackB/b2b_finiteop_tail_probe.md:1-65` | Finite-op branch status. | Local convention `lambda_min*G <= P_edge-P0_edge <= lambda_max*G`. | PROBE / NUMERIC |
| `docs/trackB/b2b_finiteop_tail_probe.md:101-145` | K=2 finite-op result. | `lambda_min`, `lambda_max`, `kerQ_dim`. | NUMERIC / PROBE |
| `docs/trackB/b2b_finiteop_tail_probe.md:175-210` | K=3 summary and verdict. | `two_sided_epsilon ~= 0.498476`; not E5p closure. | NUMERIC / GAP |
| `docs/trackB/k2_sanity_gap.md:19-39` | Raw-log normalization. | `a=r log p`, `xi=log n/(2*pi)`. | DOC / GAP |
| `docs/trackB/k2_sanity_gap.md:91-128` | K=2 raw-edge diagnostic. | `opnorm_G(Pnu_edge^circ)=0.441671876...`. | NUMERIC / PROBE |
| `Q3/Basic/Defs.lean:35-153` | Global Q3 formal definitions. | `xi_n`, `Nodes`, `w_Q`, `arch_term`, `prime_term`, `Q`, `W_K`. | FORMAL |
| `Q3/Axioms.lean:67,510` | Global axioms / wired names. | `explicit_formula`, `Q_Lipschitz_on_W_K`. | FORMAL declarations / AXIOM-level |
| `Q3/T5_Transfer.lean:234-241` | Global transfer theorem. | `Q_nonneg_on_W_K`, `W_K_subset_Weil_cone_K_with_cont`. | FORMAL |
| `Q3/Proofs/Rayleigh_Q_identification.lean:41-626` | Q/prime/arch Rayleigh bridge. | `T_P_comp_real_shift`, `arch_rayleigh_eq_shift`, `prime_rayleigh_eq_shift`, `rayleigh_Q_eq_Q_shift`. | FORMAL |
| `Q3/Proofs/PSD_PenaltyCertificate.lean:25-30,636-828` | Generic penalty receiver. | `quadForm`, `BoundaryNull`, `penalty_lower_bound_of_ratMatrixWeightedSquare_identity`, `quadForm_nonneg_on_boundaryNull_of_penalty_nonneg`, `FinitePenaltyCert`. | FORMAL |
| `Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean:31-120,1484-1536` | Old Step32F rational payload. | `CoeffIndex23`, `BoundaryIndex2`, `CenteredCoeffPayloadData`, `primaryK11C/R/D`. | FORMAL |
| `Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean:25-278` | Old Step32F floors and penalty cert records. | `primaryK11TauD`, `primaryK11DFloor`, `primaryK11DLowerBound`, `controlK9DLowerBound`. | FORMAL |
| `Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean:28-1360` | Exact old LDL certificates. | `primaryK11DLDL_identity`, `primaryK11DLowerBound_ldl`, `controlK9DLDL_identity`, `controlK9FinitePenaltyCert_ldl`. | FORMAL |
| `scripts/trackb_edge_operator_probe.py:152-199,1698-1773,7487-7695` | Track B probe implementation. | `build_P0_edge`, `run_edge`, `run_finiteop`, `run_s5clp`, `lambda_min`, `lambda_max`, `certificate_gap_dK_minus_pK`. | PROBE |
| `scripts/trackb_raw_edge_interval_cert.py` | Finite interval raw-edge certificate generator. | Arb interval `mu*G-(P_edge-P0_edge)+tau Q^TQ` certificate. | NUMERIC / INTERVAL CERT |
| `trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json` | Saved finite certificate artifact. | PASS for supplied `mu=(0.45,0.51,0.75)`, `tau=100000000`. | INTERVAL CERT / GAP for analytic mu |
| `q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py:152-265` | Packet/Gram/Q construction used by probe. | `prime_power_shifts`, `build_G`, `build_Q`, `boundary_null_basis`. | PROBE |

Lean compile checks were run on the selected Lean files above.  They passed
with no errors; `Rayleigh_Q_identification`, `T5_Transfer`, and `Q_Lipschitz`
emitted warning-only linter output.  A hole scan over the selected Lean files
found no `sorry`, `admit`, or `exact?`.

## 3. Definition And Normalization Ledger

| Item | Exact spelling in repo | Source | Current meaning | Units / normalization | Status |
| --- | --- | --- | --- | --- | --- |
| E5p / E5P | `E5p`, `analytic E5 attack` | `VERDICT_B2B.md:311-359` | Open Track B edge-defect goal. | Not formalized as local theorem. | DOC / GAP |
| raw-edge | `raw edge`, `a = r * log p`, `[2K,4K]` | `k2_sanity_gap.md:19-39`, `TRACKB_REUSE_OLD_LOWER_BOUND.md:183-188` | Edge interval in raw log variable. | Raw `a`; Q3 `xi=a/(2*pi)`. | DOC / PROBE |
| edge defect | `E_edge = P_edge - P0_edge`, `D_K` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:18-22`, `TRACKB_LP_REFORMULATION.md:60-70` | Finite prime-edge minus continuum edge matrix, or signed defect matrix. | Must be compared in projected `G` units. | DOC / PROBE |
| μ / mu / μ_K | `mu_K`, `mu-ledger`, legacy `mu_budget` labels | `TRACKB_PRICE_TABLE.md:70-102`, `VERDICT_B2B.md:194-195` | Allowed budget for edge defect. | Same-unit bridge to `d_K` missing. | GAP |
| B_K | `B_K`, `1/B_K` | `VERDICT_B2B.md:184-190`, `b2_uncertainty_tax_preflight.md:39-107` | Fourier slack / bandwidth controlling Selberg tax. | Current tax examples use `B_K=1`. | DOC / NUMERIC |
| kerQ | `ker Q`, `kerQ_dim`, `BoundaryNull` | `TRACKB_LP_REFORMULATION.md:41-58`, `PSD_PenaltyCertificate.lean:30` | Boundary-null finite subspace. | Probe uses null basis `N`; Lean has generic `BoundaryNull Q v`. | FORMAL generic / PROBE Track B |
| W_K | `W_K` | `Q3/Basic/Defs.lean:153`, `T5_Transfer.lean:234-241` | Global Q3 compact Weil class. | Function-space support class, not Track B raw-edge matrix. | FORMAL |
| QᵀQ / Gram kernel | `Q^T Q`, `tau * Q^T Q` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:44-45`, `PSD_PenaltyCertificate.lean:636-689` | Penalty that vanishes on boundary-null vectors. | Full-space penalty; on `ker Q`, equals raw quadratic form. | FORMAL pattern |
| G-norm | `G_K`, `||v||_G`, `projected Gram metric` | `TRACKB_LP_REFORMULATION.md:50-58`, `b2b_finiteop_tail_probe.md:34-42` | Finite packet normalization matrix. | Generalized eigenvalue / Loewner comparison against `G`. | PROBE / GAP |
| D_theta / Dθ | `D_theta`, `Dtheta`, `D` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:115-123`, `PayloadImport.lean:1496-1500` | Old Step32F `D=C-theta*R`. | Old `CoeffIndex23` cell, Euclidean floor. | FORMAL old / not E5p |
| R_kappa / Rκ | `R_kappa`, `Rkappa`, `R` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:115-123`, `PayloadImport.lean:1490-1494` | Old Step32F `R=A-kappa*P0`. | Old `CoeffIndex23` cell, Euclidean floor. | FORMAL old / not E5p |
| Step32F | `Step32F` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:103-113` | Old finite penalty lower-bound engine. | `L=3`, `ell=0.3`, `delta=0.25`, old 23-center space. | FORMAL old |
| LDL pattern | `LDL`, `DLDL_identity`, `RLDL_identity` | `PSD_CenteredCoeffPenaltyLDLImport.lean:344-680` | Exact rational weighted-square identities. | Proves old D/R penalty lower bounds. | FORMAL |
| m_old | `m_old` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:18,97-99` | Candidate old reserve budget. | Not proved same-unit/pre-edge for E5p. | GAP, default 0 |
| old reserve | `old reserve`, `old Step32F lower-bound` | `TRACKB_REUSE_OLD_LOWER_BOUND.md:63-99` | Candidate reuse of old positivity. | Post-edge/mixed for old self-cell; not free E5p reserve. | GAP |
| d_K | `d_K` | `TRACKB_LP_REFORMULATION.md:123-139` | Infimum dual clamp / required certificate level. | Must be in same `G`/defect units as `mu_K`. | DOC / GAP |
| p_K | `p_K` | `TRACKB_LP_REFORMULATION.md:72-80`, `S5C_LP_FINITE_DUAL_FEASIBILITY.md:116` | Sup edge-defect Rayleigh over finite cone. | `||v||_G=1` finite cone units. | DOC / PROBE |
| budget_slack | `budget_slack_K = mu_K - d_K - transfer_guards_K` | `MU_BUDGET_INTERFACE.md`; this bundle. | Remaining allowed budget after covering dual requirement. | Same units required; bridge missing. | GAP |

Important correction: do not identify the `duality_gap` `d_K - p_K` with the
μ-budget.  It is a certificate gap or finite relaxation margin, not the external allowed
budget.

## 4. Old Reserve Reuse Verdict

`TRACKB_REUSE_OLD_LOWER_BOUND.md` records two facts:

1. The old Step32F certificate is alive as exact rational LDL infrastructure.
   It proves old `D` and `R` penalty lower bounds of the form
   `D + tau_D Q^T Q >= dFloor*I` and
   `R + tau_R Q^T Q >= rFloor*I` in the old Step32F coefficient space.
2. It does not prove a same-unit E5p raw-edge reserve.  The old object proves
   positivity of full `C=A-P`; the old `P` already includes edge prime support,
   so treating it as free pre-edge reserve would double-count.

Answers from local evidence:

| Question | Answer |
| --- | --- |
| What does `TRACKB_REUSE_OLD_LOWER_BOUND.md` actually prove? | It documents that exact rational Step32F LDL lower-bound certificates exist for old `D/R` blocks and that direct reuse as E5p reserve is not justified. |
| Does Step32F provide an exact LDL pattern? | YES. |
| Does it provide free pre-edge reserve for E5p? | NO. |
| Is there a same-unit ledger-support proof? | NO local artifact found. |
| Current `m_old` | `m_old = 0`. |

Conclusion: Step32F/LDL may be reused as a pattern for a future certificate
checker, but not as an E5p budget unless a same-unit bridge is added.

## 5. Raw-Edge Numerical Diagnostics

Commands used:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py edge \
  --K 2 3 3.5 --ell 0.35 --grid-delta 0.5 --k-spline 5 --p0-na 8001

.venv/bin/python scripts/trackb_edge_operator_probe.py finiteop \
  --K 2 3 3.5 --ell 0.35 --grid-delta 0.5 --k-spline 5 --p0-na 8001 --top 8
```

Local convention quoted from `b2b_finiteop_tail_probe.md`:

```text
lambda_min * G <= P_edge - P0_edge <= lambda_max * G.
```

Observed float diagnostics:

| K | packet grid / basis | norm used | raw-edge operator estimate | inferred μ requirement | object type | proof-grade? |
| ---: | --- | --- | ---: | ---: | --- | --- |
| 2 | `ell=0.35`, `grid_delta=0.5`, `k_spline=5`, `n_centers=16`, `kerQ_dim=14` | projected `G` generalized eigenvalue | two-sided opnorm `0.4416718760986586`; upper `lambda_max=0.43707976289804495` | `mu_K >= 0.4371` in this finite model, practically about `0.44` | float/probe | NO |
| 3 | `ell=0.35`, `grid_delta=0.5`, `k_spline=5`, `n_centers=24`, `kerQ_dim=22` | projected `G` generalized eigenvalue | two-sided opnorm `0.49847340804127216`; upper `lambda_max=0.4976712109972619` | `mu_K >= 0.4977`, about `0.50` | float/probe | NO |
| 3.5 | `ell=0.35`, `grid_delta=0.5`, `k_spline=5`, `n_centers=28`, `kerQ_dim=26` | projected `G` generalized eigenvalue | two-sided opnorm `0.734943076148279`; upper `lambda_max=0.7349382268295058` | `mu_K >= 0.73494`, about `0.735` | float/probe | NO |

These float values motivated the supplied thresholds used by the interval
certificate.  They are not proof objects by themselves.

Current interval certificate command:

```bash
.venv/bin/python scripts/trackb_raw_edge_interval_cert.py \
  --K 2 3 3.5 \
  --mu 0.45 0.51 0.75 \
  --tau 100000000 \
  --ell 0.35 \
  --grid-delta 0.5 \
  --k-spline 5 \
  --arb-prec 192 \
  --out trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json
```

Interval finite certificate results:

| K | supplied mu | tau | dim | kerQ if rank 2 | interval min eigenvalue lower | verdict |
| ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 2 | `0.45` | `100000000` | 16 | 14 | `0.0129205025641165041756244529888550415698384941606131420373443264160324450064242783099439232` | PASS for supplied mu |
| 3 | `0.51` | `100000000` | 24 | 22 | `0.0123292749542153373865150679879004070578799322422451094887694119834991629981888736052152297` | PASS for supplied mu |
| 3.5 | `0.75` | `100000000` | 28 | 26 | `0.0150616591834281164859458636664893080895405879259411551698018373140686699526777271522623609` | PASS for supplied mu |

This is proof-grade finite interval evidence for the supplied thresholds, but
it is not an E5p proof until the same-unit analytic `mu_K` bridge is supplied.

## 6. Budget Comparison Rule

Correct comparison:

```text
budget_slack_K = mu_K - d_K - transfer_guards_K
```

Meanings:

| Quantity | Meaning | Units |
| --- | --- | --- |
| `mu_K` | Allowed E5p edge-defect budget from the analytic ledger. | Must match raw-edge `G`-normalized operator units. |
| `d_K` | Required dual clamp / certificate level needed to dominate the finite defect. | Must match `mu_K` units before comparison. |
| `p_K` | Primal worst edge-defect Rayleigh value over the finite cone. | `G`-normalized finite cone units. |
| `d_K - p_K` | Certificate/`duality_gap` before finite guards. | Same finite optimization units if all constraints match. |
| `budget_slack_K` | Actual remaining budget after paying the required defect level. | Same-unit only if `mu_K` and `d_K` have a proved bridge. |

Current status: GAP.  The same-unit proof connecting the analytic `mu_K` ledger
to the finite `d_K` raw-edge domination level is missing.

## 7. Minimal E5p Proof Chain

| Lemma | Exact intended statement | Source artifact if existing | Status | Missing assumptions | Lean can see it? |
| --- | --- | --- | --- | --- | --- |
| A. Kernel/Gram positivity | For the Track B finite packet space, `G_K` is positive on `ker Q_K` and `BoundaryNull Q_K` matches the probe nullspace. | Generic `BoundaryNull` in `PSD_PenaltyCertificate.lean`; probe `build_G/build_Q`. | FORMAL generic / PROBE Track B | Track B rational `G_K/Q_K` payload and positivity cert. | Only generic receiver, not Track B payload. |
| B. Packet cone compatibility | The finite coefficient vectors represent the intended Hermitian-square / positive-definite cone after boundary constraints. | Track B docs and Step13 probe. | DOC / PROBE / GAP | Formal packet-cone statement and exact normalization. | NO |
| C. Edge localization | Raw edge `[2K,4K]` in `a=r log p` corresponds to the finite matrix `P_edge-P0_edge` in the same basis. | `k2_sanity_gap.md`, probe code. | PROBE / GAP | Interval/rational construction and proof that this is the theorem object. | NO |
| D. Raw-edge domination | `P_edge - P0_edge <= mu * G_K` on `ker Q_K` for supplied thresholds. | `trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json`. | INTERVAL CERT for supplied mu | Same-unit proof that analytic `mu_K` meets these thresholds. | NO Lean port |
| E. Same-unit μ comparison | `budget_slack_K = mu_K - d_K - transfer_guards_K >= 0`. | Current docs name the interface but not the bridge. | GAP | Definition/source of `mu_K` and proof it uses same units as `d_K`. | NO |
| F. Defect accounting | Finite raw-edge domination plus tail/boundary/cell bookkeeping equals the E5p defect ledger. | S3 closure docs; route-gap table. | NUMERIC / DOC / GAP | Proof-grade arch/zero/prime/boundary accounting, not S3 float closure. | NO |
| G. Final E5p inequality | For all admissible `h in C_K cap kerQ`, `Edge_K(h) <= mu_K Norm_K(h)`. | No local theorem found. | GAP | Lemmas A-F plus exact theorem statement. | NO |

## 8. Required Proof-Grade Certificate

The certificate needed now is a proof-grade replacement for the float generalized
eigenvalue diagnostics.  Acceptable certificate forms:

- rational PSD certificate,
- interval PSD certificate,
- Lean-verifiable matrix inequality,
- Python certificate with independently checkable rational output.

It should certify, in the repository's actual finite-op convention:

```text
lambda_min * G <= P_edge - P0_edge <= lambda_max * G
```

and specifically the upper half needed for E5p:

```text
P_edge - P0_edge <= mu_K * G
```

on the projected `ker Q` finite space, after a same-unit proof that the chosen
`mu_K` is the analytic budget for the same object.  Equivalently, a full-space
penalty certificate may be used if it is tied to the actual Track B matrices:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0
```

This last display is a receiver shape, not an existing local theorem for E5p.
It must be instantiated with actual rational/interval Track B matrices before
it becomes evidence.

## 9. Current Blockers

1. No local E5p closure theorem.
2. No same-unit ledger-support proof allowing old Step32F reserve into E5p.
3. `m_old` therefore defaults to `0`.
4. Same-unit bridge audit result: `E5P_BRIDGE_SOURCE_GAP`.
5. Raw-edge float/probe diagnostics are now backed by interval finite PSD
   certificates for supplied `mu=(0.45,0.51,0.75)`.
6. No proof that analytic `mu_K` in the same normalization is at least those
   supplied thresholds after guards.
7. `mu_K` vs `d_K` normalization bridge is unclear/unproved.
8. Current docs now distinguish `certificate_gap_K=d_K-p_K-finite_guards_K`
   from the real budget comparison
   `budget_slack_K=mu_K-d_K-transfer_guards_K`.
9. S3 closure is numerical bookkeeping only, not proof-grade defect accounting.

## 10. Next Implementable Patch

Chosen next action: C. Add normalization ledger tests / same-unit `mu_K` bridge
audit.

Reason: the naming cleanup is done and the raw-edge finite PSD certificate now
passes for supplied thresholds.  The smallest useful next step is to prove,
source, or refute the same-unit analytic comparison

```text
mu_2   >= 0.45
mu_3   >= 0.51
mu_3.5 >= 0.75
```

after all guards in the same `G_K/Q_K` normalization.  If no such source exists,
the node is terminal as

```text
GAP_EXACTLY_NAMED: SAME_UNIT_ANALYTIC_MU_BRIDGE
```
