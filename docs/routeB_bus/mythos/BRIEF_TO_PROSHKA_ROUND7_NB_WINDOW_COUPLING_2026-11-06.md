# PROSHKA REQUEST — PROVE RH, ROUND 7: THE NATURAL NB ↔ WINDOW COUPLING (2026-11-06)

Repository: https://github.com/Malaeu/chen_q3

Branches:
- `rh_clean` holds this file. The commit is given in the owner's message.
- `proshka_inbox_2026-10-31` takes the verdict as a NEW file:
  `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06.md`.
  If the name is taken, add a suffix (`_B`, `_C`, …). Never overwrite another verdict.

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749.

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## INPUTS (branch proshka_inbox_2026-10-31)

1. **Round 6 C.** Commit 0005623e, freeze afaaeb06. File `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_C.md`.
   - The autonomous NB residue chain.
   - The finite bridge (C20)–(C23): e_N ≤ m^{−6} ⇒ A_m ≥ −40000(1 + log m)² m^{−3/2} G_m.
   - The open capture (C28).
   - The off-line evaluation barrier (C31).
2. **Round 6 B.** Commit 888b8080. File `docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_B.md`.
   - Positive self-dual plants v_b kill any universal "positivity + Poisson" return.
   - The discriminating link is the **exact** Gaussian/Γ local factor, (7.2).
3. **Round 6 brief and addendum C** on `rh_clean`:
   - commit 7db22a05: `docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND6_FORWARD_ARROW_2026-11-05.md`;
   - commit 9dc00979: `docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND6_ADDENDUM_C_2026-11-05.md`.

## OWNER'S DIAGNOSIS (context; verify every cited result yourself)

The bridge of Round 6 C is logically valid but consumes an enormous prefix. Known results on the NB distance d_N² = inf over A_N of (1/2π)∫|1 − ζA_N(½+it)|² dt/(¼+t²):

- **Unconditional lower bound.** liminf d_N² log N ≥ Σ_{Re ρ = ½} m(ρ)²/|ρ|². Due to Báez-Duarte, Balazard, Landreau and Saias, sharpened by Burnol (arXiv:math/0103058, Thm 1.3). So d_N² cannot decay faster than c/log N.
- **Under RH, unconditional upper bound.** d_N² ≪ (log log N)^{5/2+ε}/√(log N) (Balazard–de Roton, as cited in Bettin–Conrey–Farmer).
- **Under RH plus a mild 1/|ζ′(ρ)|² hypothesis.** d_N² ~ (2 + γ − log 4π)/log N, attained by V_N(s) = Σ_{n≤N}(1 − log n/log N)μ(n)n^{−s} (Bettin–Conrey–Farmer, arXiv:1211.5191).
- **Four off-line zeros.** If ζ has exactly four zeros off the line at σ₀, then (1/2π)∫|1 − ζV_N|²dt/(¼+t²) behaves like (A N^{2σ₀−1}cos(2γ₀ log N) + B N^{2σ₀−1})/log²N (Maier–Rassias, arXiv:1705.09918; Canad. Math. Bull. 61 (2018)).

Consequence for us: with the threshold m^{−6}, the chain needs log N ≳ m^6, so N ≳ exp(c m^6). The natural RH-predicted rate is 1/log N. The threshold and the natural rate live on incompatible scales.

Note: the e_N of Round 6 C is the discrete Báez-Duarte residue form. Establish its exact relation to d_N² before using these citations.

## THE TASK

Find the **natural coupling** between the NB approximation and the CCM window. The new content is quantitative.

1. **Optimal threshold function.** Determine the weakest condition on the NB residue, as a function τ(m, N), that still implies

       A_m ≥ −C(1 + log m)^r G_m   on 𝒦_m,

   with explicit C and r, and the coupling N = N(m) that makes it weakest. Target: a threshold of size 1/polylog(m) at N(m) ≤ exp(polylog m), or a proof that no such threshold exists.
2. **Matching the natural rate.** If (1) succeeds, state the exact residual lemma: the NB rate at the coupling, e.g. e_{N(m)} ≤ C′/log N(m), or its averaged version. Prove that this lemma ⇒ polylog floor ⇒ RH (via 62f78231, blob 2b5e02a0, §6), and that RH (plus at most the named mild hypotheses) ⇒ the lemma. Every extra hypothesis must be classified THEOREM / CONDITIONAL / CONJECTURE.
3. **Discriminator consistency.** For the planted quartet, the Maier–Rassias growth N^{2σ₀−1} at the coupling must reproduce the window damage m^{a} = m^{σ₀−1/2}, the same one Rounds 3 and 6 use. State the exact correspondence of exponents. A mismatch is a FATAL finding about the coupling and must be reported as a result.
4. **Exact local factor.** Name the link where the exact Γ factor enters. Round 6 B proved that positivity plus Poisson cannot replace it.

## OWNER'S PRACTICAL IDEAS (ideas, not orders)

- **Idea 1 — same interval.** The NB space of length N uses dilates ρ(θ/x), θ ∈ [1/N, 1], so it lives on a logarithmic interval of length log N. The CCM window lives on an interval of length L = log m. Test the identification N = m (log N = L): do the two Hilbert spaces, or their Gram/residue forms, coincide up to an explicitly paid boundary/pole defect? If they do, the m^{−6} loss may be an artefact of passing through a non-matched intermediate.
- **Idea 2 — the smoothing weight is our damping.** The Bettin–Conrey–Farmer weight (1 − log n/log N) is a Fejér-type taper on the same logarithmic interval. Compare it with the damping e^{−δu} of Round 4 B and with the window's pole renormalization. A matched taper may carry the coupling.
- **Idea 3 — unextinguishable unit.** At an off-line zero ρ, ζ(ρ)A_N(ρ) = 0, so 1 − ζA_N = 1 there for every N (Round 6 C, (C31)). Quantify how much of this unit the window at the coupling must see. That quantity is the discriminator in (3).

## ACCEPTANCE (fixed before you start)

1. **Freeze first**, as a separate commit: the coupling candidate N(m), the threshold form, the registered predictions. The freeze is never edited.
2. **Explicit constants** in every bridge inequality; boundary, pole and Γ terms paid exactly.
3. **No relabelling.**
   - "Prove e_N → 0" restated is NO_PROGRESS.
   - "Threshold m^{−6}" restated is NO_PROGRESS.
   - The progress must be a strictly weaker sufficient threshold, or an obstruction theorem for weakening it.
4. **False worlds.**
   - The planted quartet: exponent correspondence, as in task (3).
   - DMV: name the link that fails.
   - The curve over 𝔽₃: it must pass.
5. **Falsifiers.** For each finite claim stronger than a proved one, give a Codex test fixed in advance: quantity, N/m grid, precision, plant, pass/fail. Example: e_N for V_N at N = m on a grid, compared with the window floor.
6. **Literature.** Check each cited result for corrections or errata before use, and record the check.
7. **Bottom of the chain**, one of:
   - (a) RH proved;
   - (b) optimal coupling plus the exact residual lemma, both RH-equivalence directions proved;
   - (c) a proof that no threshold weaker than a stated one can imply a polylog window floor, with the obstruction named.
