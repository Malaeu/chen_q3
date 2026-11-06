# Route B — rounds 4–9 (2026-11-05/06): reduction chain, kills, numbers

Status: CHALLENGER / NOT_RH. RH is not proved. Everything below is PAPER, unaudited by an independent reader, unless marked DIAG (numerical, finite) or CERT (certified finite computation).

Repository: https://github.com/Malaeu/chen_q3. Proshka verdicts are on branch `proshka_inbox_2026-10-31`, path prefix `docs/routeB_bus/proshka/`. Codex runs and Mythos briefs are on `rh_clean`.

## 1. The chain in one line

    literal window floor A_m ⪰ −polylog·G   ⇐   NB capture e_N → 0   ⇐   (26) bounded Möbius core H_N on the crossing set S   ⇐   ???

The arrows into RH are proved: the window floor via the Gaussian export 62f78231, and the other links via R6 C, R7 B and R8 B. The bottom link, (26), is open. R9 B proved that "moment-only" information cannot supply it.

## 2. Rounds

| Round | Commit (freeze) | Result | Class |
|---|---|---|---|
| R4 A | 7a1d9a53 (a14bd4e1) | Radial square K = ∂_δ(δH); RH ⇔ K ≥ 0; window-curvature SOS obstruction | PROOF_PROGRESS |
| R4 B | dd22692d (05e90085) | Damping transport from the positive terminal H_m(1/2) = T*T (σ = 1) to the window. Minimal loss L_m. Non-arithmetic budget 9/25 after exact pole + prime-main cancellation. Unconditionally L_m = O(√m/(log m)^4); RH ⇒ L_m ≤ 14Σ₀L² | PROOF_PROGRESS |
| R4, curvature | 1de8ebb2 (6a1a879a) | Poisson-kernel square ∂²_c log k_c + 5/(4c²) = S² (5/4 optimal). Monotonicity only for δ > 1/2 (right of Re s = 1). The step to the line is unpaid: term (4) is RH-equivalent | NO_PROGRESS on sign |
| R5 | 25f5ac26 (ca746d4f) | Null-gauge rigidity; unrestricted path = circular. R5.GAP = D_ψ(u) = e^{−u/2}(ψ(e^u) − e^u) | PROOF_PROGRESS (kills) |
| R6 B | 888b8080 (c89977f6) | Theta/Poisson positive chain built. KILLED by positive self-dual plants v_b whose ξ·Q_b has an off-line quartet. The exact Γ/Gaussian local factor is the only discriminator | KILL |
| R6 C | 0005623e (afaaeb06) | Autonomous NB residue chain (k mod n)/n. Bridge e_N ≤ m^{−6} ⇒ A_m ≥ −40000(1+log m)²m^{−3/2}G | PROOF_PROGRESS |
| Limit 9 | c09713ed | The exact-head Möbius interpolant does NOT converge (Báez-Duarte). A bounded-norm subsequence suffices via averaging (B/J + 1/J²) | FALSIFICATION_PROGRESS |
| R7 B | 8a994500 (97f4cf03) | d_N² ≤ e_N ≤ (log 2π − γ)d_N². Threshold m^{−1}. (R_fast): e_m ≤ 1/(2 log m) ⇒ RH. (R_slow): N = exp((log m)³), ⇔ RH. Exact head identity (7.10): R_N^V(k) = k·b_N − ψ(k)/log N. Maier–Rassias growth belongs to V_N, not to inf e_N | PROOF_PROGRESS |
| R8 B | 70c4e6b0 (6d50c6f9) | NEW OBJECT: finite rational PSD upper Gram G_up ≥ G_∞ for all coefficients, giving certificate ê_N ≥ e_N with the tail paid explicitly. Möbius taper: tail ≤ 5/log²N. S = {b_N b_{N+1} ≤ 0} infinite, unconditionally. (26) ⇒ RH. Lower bound e_N ≥ (2β−1)/|ρ|² for every right zero | PROOF_PROGRESS |
| R9 B | b5fc098b (a0f1bf80) | KILL of the method class "scalars b, s + \|c\| ≤ 1 + squarefree support + exact initial block + generic Gram/tail": explicit counterarray with the same S and H_N ≥ N/(2·10⁹ log²N). Proving (26) requires exact μ values, the full convolution μ*1 = ε, and coherence of one coefficient set across all prefixes | KILL (theorem shape) |

## 3. Numbers (DIAG / CERT, finite only)

- **Thermometer** (a33870cb): log-mean of the corner scalar Ψ(log m) for m ≤ 10⁸ is 0.0461841. Compare 2 + γ − log 4π = 0.0461914 = Σ 1/(ρ(1−ρ)). This is unconditional (Hadamard); it is no test of RH. DIAG.
- **NB rate** (ba5654b4): optimal e_N·log N ∈ [0.045, 0.047] for N = 50…5000, i.e. on the Burnol/BCF constant. Margin to the threshold 1/2 is ≈ 11×. DIAG.
- **Certificate** (a180142f): ê_N·log N ≤ 1/2 certified for N ≤ 2000 (rational/Arb); ê/e falls from 2.18 (N = 10) to 1.18 (N = 2000). CERT.
- **Crossing set** (a180142f): S starts at N = 43297; 27 crossings up to 10⁷, all certified at 192 bits. On S, the head part of H_N times log N lies in [0.125, 0.165] and drifts down. The shoulder is ≪ the head. The planted quartet is detected with slope 2/3. DIAG/CERT.

## 4. Killed — do not repeat

- External-force δ-flow and any gauge on it.
- Free interior paths.
- The δ-curvature square as the whole chain.
- De Bruijn–Newman heat flow (Rodgers–Tao).
- The universal positivity + Poisson + self-duality return.
- The full exact-head NB sequence.
- Transferring V_N growth onto the optimal e_N.
- Universal o(N²) rational-frequency bounds (R8 (31)).
- Moment-only bounds on the core over S (R9).
- Head-on PNT/sieve/mean bounds: they give √m/(log m)^A with no sign.

## 5. Literature frontier (checked by Proshka)

- **Bettin–Gonek** (Mathematika 63, 2017), Thm 1: a rough long-mollifier bound gives a zero-free region with boundary 1/2 + 1/(2θ). θ = ∞ ⇒ RH.
- **Conrey 1989**: θ < 4/7.
- **Burnol** (Adv. Math. 170, 2002): lower bound with multiplicities squared.
- **Bettin–Conrey–Farmer** (arXiv:1211.5191): conditional on RH + H_{−1}.
- **Maier–Rassias** (2018): growth of the explicit V_N when there are off-line zeros.

## 6. Open

- **MMI (26):** there is B < ∞ such that {N ∈ S : H_N ≤ B} is unbounded, for the unmodified μ(n)(1 − log n/log N). Requires exact Möbius arithmetic (μ*1 = ε) plus prefix coherence.
- **Pending Codex task:** Round 4 B transport loss L_m (ca5831bb). Status unknown.

## 7. Error log (Mythos)

Kept in project memory: topics/mythos-fehlerlog.
