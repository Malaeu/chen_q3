# PROSHKA VERDICT — REQ-2026-10-28-THETAGRADE (verbatim, pasted by the owner 2026-10-28)

Request: `PROSHKA_REQUEST_THETAGRADE_2026-10-28.txt` at 63eec554. Observer audit: `THETAGRADE_AUDIT_2026-10-28.md`.

```
OPERATIVE_CLASS: RUN_THETAGRADE_DISCRIMINATOR
REQUEST_ID: REQ-2026-10-28-THETAGRADE
BOUNDARY_ID: GOAL058_ROPES_THETA_GRADING
SOURCE_BASE_COMMIT: 4a847548e3ee45b2f8a548349110ceb437abe3a4
Q1a: WITNESS_CONFIRMED_CONDITIONAL
Q1b: WITNESS_CONFIRMED_CONDITIONAL
Q1c: WITNESS_GAP_ARBITRARY_THETA_UPPER_AND_ENDPOINT
Q1iii: WITNESS_CONFIRMED_CONDITIONAL
Q2: G1_UNDECIDED_FIRST_FACT
Q3: SOURCE_VERIFICATION_INCOMPLETE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 3
PX_RH_CLAIM: NOT_MADE
REPO_WRITTEN: false
LEAN_EXECUTED: false
```

## Source lock and limitations
Read the byte-exact request at commit 63eec554, the Proshka protocol at rh_clean, and the pinned ROPES_THETA_MAP.md, PAPER_CHAIN.md, SOURCE_TRANSFER.md, NEXT.md, PROSHKA_JOINT_HILBERT_INLINE_2026-10-06.md and independent complement-floor verdict. The external OpenAI paper.tex was not accessible; therefore Q3 cannot receive a source-verified degree code. This is an explicit fail-closed boundary, not a guess. No repository changes or Lean runs.

## Q1 — necessary tracking exponent, conditional
[COFINAL_FAMILY | PAPER] Assume the same literal selected-Ferrers family F_m, with (1) entire real-rooted F_m (G2 instantiated from a simple ground state with nonzero center pairing, G2b), (2) T_m -> Xi uniformly on compact discs (G4 plus selected-shell crosswalk, hmode/hchi and G3c where required), (3) the T3 bound with the conditional positive center floor on the matched port, and (4) T5's superpolynomially small t_m. These are hypotheses, not results established here. The eventual cell schedule and normalization must coincide throughout.

Suppose Xi(z0)=0 with Im z0 != 0. Choose a closed disc D disjoint from the real axis, containing only that zero, and put b=min_{∂D}|Xi|>0. For all sufficiently large m, sup_{∂D}|T_m-Xi|<b/4. If sup_{∂D}|F_m-T_m|<b/4, Rouché implies that F_m has a zero in D, contradiction. Therefore for every sufficiently large m,
\[
\sup_{\partial D}|F_m-T_m|\ge b/4.
\]
For every H>|Im z0| containing the disc in |Im z|<=H, T3 implies
\[
\alpha_m+4t_m\ge {b\over4C_H}\,{m^{-H/2}\over\sqrt{\log m}}.
\]
As t_m decays faster than any power,
\[
\alpha_m\ge {b\over8C_H}\,{m^{-H/2}\over\sqrt{\log m}}
\]
eventually. Thus alpha_m=O(m^{-a}(log m)^A) is impossible if a>H/2. Choosing |Im z0|<H<2a proves Q1a. Code: WITNESS_CONFIRMED_CONDITIONAL. First unpaid term: the cofinal G1 instance, together with matched-family T3 center-floor and crosswalk hypotheses. The prompt's “only places it can break” list is incomplete unless those dependencies are bundled into T3/G4/G2.

[COFINAL_FAMILY | PAPER] Q1b: under the same assumptions, any a>0 gives a zero-free open strip 1/2<Re s<1/2+2a (and its reflected counterpart). If independently validated ZF78 yields Theta<=7/8, then a>3/16 excludes all off-line zeros. This is a conditional implication, not a proved rate or RH. Code: WITNESS_CONFIRMED_CONDITIONAL. First unpaid term: the rate on the literal ground-tracked family.

[ABSTRACT | PAPER] Q1(iii): locally uniform convergence F_m->Xi on an open horizontal strip, with F_m entire and real-rooted and Xi nonzero as a function, excludes every nonreal zero strictly inside it by Hurwitz, regardless of vector-norm control. Nothing follows at the strip boundary without extra convergence. Transform-level cancellation can bypass the sufficient T3 norm estimate. Code: WITNESS_CONFIRMED_CONDITIONAL. First unpaid term: direct compact-uniform transform error.

[COFINAL_FAMILY | CONDITIONAL] Q1c: the cited off-line-zero witness lambda_min(K_m)<=-c m^delta/(log m)^(2delta) for each actual zero with delta=Re rho-1/2>0 (NEXT.md; source proof not rederived here) excludes every proposed cofinal lower floor -C m^eta with eta<delta. Supremizing zeros gives a necessary threshold eta>=Theta-1/2, not attainment at the endpoint. The MTY-based full-frequency contour estimate in the shelf does not itself prove an upper floor for every arbitrary zero-free abscissa sigma>Theta; the shift must repay Perron cutoffs, finite-height exceptions, log-derivative bounds, and all matrix frequencies. Even if that extension works, it gives an infimum of power exponents, generally with epsilon, not a uniform endpoint bound. Code: WITNESS_GAP(arbitrary-Theta upper envelope; endpoint). First unpaid term: source-specific uniform contour bound for every sigma>Theta with explicit losses. Failure to establish a sufficient upper bound does not refute the actual floor.

## Q2 — the parity-twin inference fails, G1 remains undecided
[ABSTRACT | PAPER] Let R be parity, [K_m,R]=0, and v_+=(v+Rv)/2, v_-=(v-Rv)/2. Then exactly
\[
\langle v,K_mv\rangle
=\langle v_+,K_mv_+\rangle+\langle v_-,K_mv_-\rangle.
\]
The normalized full quotient is a convex combination of the two sector quotients. A negative full quotient implies negativity of at least one sector, not both. The elementary parity-commuting diag(-M,+1) is a counterexample to the proposed inference, not a counterexample to the literal CCM family. Even two sector upper bounds of order -m^delta/(log m)^(2delta) do not establish equality of leading coefficients, an odd ground-state flip, or failure of ||r_m||/delta_m->0.

[COFINAL_FAMILY | CONDITIONAL] Code: G1_UNDECIDED_FIRST_FACT. The first missing source-specific fact is a signed even/odd spectral comparison on the original cell schedule: D_m=lambda_min(K_m|odd)-lambda_min(K_m|even), accompanied by a controlled ground projection of the selected q_m, the actual residual ||r_m||, and the cellwise complement gap delta_m. A cofinal inequality forcing D_m<=0, or a residual/gap obstruction, would be a witness; a cofinal positive comparison and independently small residual could refute that particular witness. No exact orders beyond the relayed full-minimum m^delta/(log m)^(2delta) can currently be assigned to both sectors. The old fixed-positive complement floor is killed without zero input, but simplicity, evenness and positive cellwise floors remain open. DISCRIMINATOR: certified signed sector-gap-to-residual comparison on an unbounded original family, not finite samples.

## Q3 — bounded reading, primary manuscript unavailable
[ABSTRACT | CONDITIONAL] The request's relayed formula sigma0=1-h/6+losses gives 11/12 for h=1/2 and zero loss, and 7/8 for h=13/16 and loss=1/96, since 1-13/96+1/96=7/8. If the relayed constraints h=1-l_x+ell, M+ell=1, M>=0, l_x>0 are accurate, then h=2-M-l_x<2, and with nonnegative losses sigma0>2/3. These are arithmetic checks on RELAY, not verification of paper.tex.

[ABSTRACT | CONDITIONAL] The relayed cubic-theta frequencies u a^6 and order-six character suggest that six is an object-specific construction parameter; they do not establish whether the abstract continuation criterion imposes that degree. In particular, naming a linear or quadratic “lowest admissible theta” and its first loss without reading the criterion would invent mathematics. Code: SOURCE_VERIFICATION_INCOMPLETE (neither allowed positive degree code is earned). First unpaid term: primary-source inspection of the continuation criterion, exact lower-degree admissibility and first loss. The source URL supplied in the request is https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex. No manuscript theorem is imported as established.

## Consumer-first audit and route map
[ABSTRACT | PAPER] DOWNSTREAM_CONSUMER: same-family Hurwitz G5. ACTUAL_CONSUMER_REQUIREMENT: entire real-rooted F_m with compact-uniform F_m->Xi. ORIGINAL_REQUESTED_OBJECT: G1 simple even ground state plus norm tracking alpha_m. ORIGINAL_OBJECT_IS: UNKNOWN as necessary interface; real-rootedness still requires a supplier, while direct transform tracking can replace norm tracking. KNOWN_WEAKER_INTERFACES: sup_K|F_m-T_m|->0 and T_m->Xi imply F_m->Xi. FAILURE_TYPE: NO_DERIVATION. EPISTEMIC_STATUS: RESEARCH_DEBT. NOVELTY_AXIS: TRANSFORM_LEVEL / PARITY_RESOLVED. REOPEN_TRIGGER: exact cofinal transform estimate or parity-gap comparison. No route-family KILL is asserted.

Candidate A — transform-dual: control the analytic error E_m(z)=F_m(z)-T_m(z) directly, preserving prime powers, normalization and boundaries. Kill-power HIGH (bypasses norm tracking), cost HIGH (signed arithmetic). Cheapest falsifier: Rouché on a nonreal target-zero disc under G2. Candidate B — parity-block Schur: represent both parity minima, residual and selected-row overlap jointly. Kill-power MEDIUM-HIGH (tests parity twin), cost MEDIUM-HIGH (cofinal spectral bounds). Cheapest falsifier: a signed source-specific sector comparison inconsistent with twin asymptotics. These are proposals, not theorems.

Cross-domain bridges checked conceptually: oscillation/Sturm theory needs an actual intertwiner to the CCM blocks (not supplied); the Weil-nullplane identity explains the constant-floor obstruction but does not order parity sectors; a signed two-sector comparison plus residual is the minimal collapse object. No third restatement of the same floor is authorized.

## Strongest attack and registered predictions
Q1 attack: failure of the T3 sufficient norm bound cannot imply failure of actual transform convergence. The proved direction instead uses Rouché to force a necessary lower bound on alpha_m. Q2 attack: negativity of a direct sum does not give negativity of both summands. Q3 attack: no primary text, so no verified degree theorem.

Frozen P1: partially confirmed (Q1a/b conditional, extra matched-port dependencies). P1c: unconfirmed (arbitrary-Theta and endpoint). P1t: confirmed for direct locally uniform convergence in an open strip. P2: undecided; this does not mathematically refute NOT_GRADED. P3: unscored pending primary source. No probabilities retroactively changed.

## Proshka's own line
The transform-error route is the first choice because the roof consumes functions, not coefficient vectors.
The nearest alternative is a parity-resolved spectral attack, necessary for G1 but not by itself for convergence.
The second alternative is a stronger global SP floor, useful but not automatically a ground-tracking supplier.
I would first seek an exact source-preserving cancellation identity for F_m-T_m.
A missing boundary or prime-power contribution would kill that proposed identity.
I would next seek the signed even/odd spectral difference and the selected-row residual together.
If the signed difference is not controlled relative to the residual, the parity-twin move dies.
I would ask for the pinned external paper.tex bytes before judging its continuation criterion.
I would also ask for the exact parity block decomposition on the literal CCM matrix.
The most useful shelf insight is T1: projection transfer does not amplify by the spectral gap.
The most suspicious word in the map is “exactly” for the Theta floor exponent.
A necessary threshold is not an attained endpoint estimate.
The second suspicious move is symmetrizing one negative witness into two independent witnesses.
A convex combination gives only one negative sector.
The third is treating the fixed-floor kill as death of every cellwise gap.
Those are different theorem shapes.
Finite samples can test a claim, not supply a cofinal quantifier.
A same-family normalization mismatch would invalidate an otherwise clean Hurwitz chain.
No numerical improvement can replace that source lock.
The next genuine gain must close a family-level quantifier or kill a precise theorem shape.

## Research log
- READ GitHub Malaeu/chen_q3 pinned 4a847548, docs/literature/RETRO_HISTORY_2026-10-28/ROPES_THETA_MAP.md: observer's Theta map, treated as hypotheses.
- READ same pin, docs/Codex/PAPER_CHAIN.md: G0–G5 and same-family status.
- READ same pin, docs/routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md, T1–T7: norm transfer and conditional center floor.
- READ same pin, docs/Codex/NEXT.md: off-line zero floor witness, RELAY rather than independently re-proved.
- READ same pin, docs/routeB_bus/source_observability_2026-09-28/PROSHKA_JOINT_HILBERT_INLINE_2026-10-06.md, §2: MTY contour calculation, not arbitrary-Theta endpoint.
- READ same pin, docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md: constant-floor theorem-shape kill.
- RELAY arXiv:2511.22755, Thm 5.10 and Lemma 7.3: primary PDF not independently inspected.
- NOT READ OpenAI paper.tex at adc7f124: retrieval failed; no source-verified Q3 verdict.
- ABANDONED “Hurwitz alone gives a quantitative bound”: requires Rouché boundary minimum b>0, supplied above.
- ABANDONED “negative full minimum implies negative even and odd minima”: convex-combination identity defeats it.
- ABANDONED “MTY shift proves exact arbitrary-Theta exponent”: no arbitrary-abscissa full-frequency contour audit or endpoint.
- REUSABLE IDENTITY Q(v)=||v_+||²Q(v_+)/||v||²+||v_-||²Q(v_-)/||v||²; useful for future sector-resolved witnesses.
- REUSABLE TEST min_{∂D}|Xi|>0 turns real-rootedness into a uniform transform-error lower bound.

## Single next directive and closeout
CODEX DIRECTIVE (read-only, no repository write): Fetch the exact pinned OpenAI paper.tex; extract the continuation criterion's quantified hypotheses, the normalization/probe-loss formulas, and the first lower-degree theta admissibility obstruction. Return exact line spans, with no new construction, and distinguish the criterion's requirements from those of the cubic theta. Validation: source SHA-256 must match 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3; otherwise stop.

META CLOSEOUT: smaller — Q1 now has a rigorous Rouché discriminator and explicit missing hypotheses; killed — only the inference from one full negative witness to two negative parity witnesses; do not retry blind parity symmetrization or endpoint exponent relabeling; smallest gaps — cofinal signed parity comparison and primary Q3 criterion; next cheapest test — source hash and exact criterion extraction. Memory: THETAGRADE: Q1 conditional witness valid; Q1c endpoint unproved; Q2 parity-twin unsupported; Q3 primary source missing. RH remains OPEN.
