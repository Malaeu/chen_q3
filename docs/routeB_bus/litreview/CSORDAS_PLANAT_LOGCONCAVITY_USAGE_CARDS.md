# Log-concavity of Φ(√t) — Csordas 2015 (arXiv:1309.0055) and Planat–Solé 2026 (arXiv:2608.19160)

Written 2026-09-11 by the observer after the SLACK verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md`, origin e8a95fac).
Trigger: Proshka's single next_decisive_test THETA_SQUARED_COORDINATE_LOG_CONCAVITY (SL23).

## 1. What is said VERBATIM

**Csordas, G., "Fourier transforms of positive definite kernels and the Riemann ξ-function",
Comput. Methods Funct. Theory 15 (2015) 373–391; arXiv:1309.0055.** PDF `pdfs/1309.0055.pdf`,
printed page 11 (pdftotext line 649 ff.):

> Theorem 4.2. Let Φ be defined by (4.1). Then Φ satisfies the following concavity properties.
> (a) ([16, Proposition 2.1]) If K_Φ(t) := ∫_t^∞ Φ(√u) du (t ≥ 0), then log K_Φ(t) is strictly concave for t > 0.
> (b) ([21, Theorem 2.1]) The function log Φ(√t) is strictly concave for t > 0.

> Remarks 4.3. (a) A calculation shows that log Φ(√t) is strictly concave for t > 0 if and only if
> g(t) := t(Φ′(t)² − Φ(t)Φ″(t)) + Φ(t)Φ′(t) > 0 for t > 0.

Φ there is (4.2): Φ(t) := Σ_{n≥1} πn²(2πn²e^{4t} − 3) exp(5t − πn²e^{4t}).
[16] = Csordas, Norfolk, Varga, Trans. AMS 296 (1986) 521–541.
[21] = Csordas, Varga, "Moment inequalities and the Riemann hypothesis", Constr. Approx. 4 (1988) 175–198 — the ORIGINAL proof of (b) (RELAY: not fetched).
Open Problem 4.14 (printed/PDF page 13, verified locally 2026-09-11): with s(t) := Φ(√t), f(t) := s′² − s s″, "By Theorem 4.2(b), f(t) > 0 for t > 0"; conjecture (log f)″ < 0.

**Planat, M., Solé, P., "Second-Level Concavity of the Riemann Ξ Kernel", arXiv:2608.19160v1 (19 Aug 2026).**
PDF `pdfs/2608.19160.pdf`, page 1 (lines 45–46): "Theorem 4.2(b) of Csordas [2] gives the strict log-concavity of s, and in particular f(t) > 0 for t > 0; see also Coffey–Csordas [5]." Theorem 1.1 proves (log f)″(t) < 0 for all t > 0 (second level), two proofs, computer-assisted directed-interval certificates, Python + SymPy scripts. Section 7: "It remains a necessary-condition result in the Riemann-Ξ program and does not prove the Riemann Hypothesis."
[5] = Coffey, Csordas, "On the log-concavity of a Jacobi theta function", Math. Comp. 82 (2013) 2265–2272 (RELAY: not fetched).

## 2. Variable correspondence with our objects

| Ours (SLACK verdict) | Csordas / Planat–Solé | Check |
|---|---|---|
| Φ_ours(x) = e^{x/2} Σ (4π²n⁴e^{4x} − 6πn²e^{2x}) e^{−πn²e^{2x}} | Φ_C(r), (4.2) | Termwise substitution in (4.2) proves Φ_ours(x) = 2·Φ_C(x/2); the earlier three-point ratio is a diagnostic only |
| f = Φ_ours/A | — | positive constant, drops out of every sign |
| SL23: J_f(x) = x(f′² − f f″) + f f′ ≥ 0, x > 0 | Remark 4.3(a): g(t) > 0 | exactly J_f(x) = (2/A²) J_ΦC(x/2) > 0 by the chain rule |
| same, in t = x² | Planat–Solé f(t) = s′(t)² − s(t)s″(t), s(t) = Φ(√t) | f(t) = J(√t)/(4t^{3/2}); not literally J, same sign for t > 0 (sympy 2026-09-11; Codex OC2 correction of my first wording) |
| ℓ(s) = log f(√s) concave | Theorem 4.2(b): log Φ_C(√t) strictly concave | s = 4t, linear rescale preserves concavity |

## 3. What it gives US

- SL23 is a published theorem: Csordas–Varga 1988 Thm 2.1 (relay) restated as Csordas 2015 Thm 4.2(b) (READ, page 11). Strict inequality, all t > 0.
- Hence SL24 is paid: V_f(x,x) ≥ V_f(x,−x) for all x ≥ 0 (Proshka's own derivation via Jensen; the only missing input was SL23).
- Observer probe `docs/routeB_bus/proshka/slack_jf_probe_2026-09-11.py` (14 points, all J_f > 0) is consistent; it is now a control, not evidence.
- Planat–Solé state the second-level theorem with certificates. Its proof/certificates have not been independently audited here; it is a candidate supplier if a future comparison needs that stronger hypothesis, not a premise of the accepted SLACK report.

## 4. What it does NOT give

- Nothing about SL20 (full theta-kernel positivity on all complex compact tests), the even sector, or off-diagonal quadratic directions. Proshka: "It does NOT prove all off-diagonal quadratic inequalities, the even sector, or SL20."
- Planat–Solé section 7 says it explicitly: necessary-condition result, does not prove RH.

## 5. Not read

Csordas–Varga 1988 (original proof), Coffey–Csordas 2013, Csordas–Norfolk–Varga 1986. Planat–Solé sections 3–6 and their certificate scripts were not rerun.
