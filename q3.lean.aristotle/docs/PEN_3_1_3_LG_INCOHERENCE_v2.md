# PEN NOTE 3.1.3 — Incoherence of the Jump Comb over Zeros (v2, post-adversarial)

STATUS: v2. Adversarial pass (Прошка) integrated: verdict "GAP repaired,
no fatal kill". Changes vs v1 are marked [R:*]. Node 3.1.3. Feeds 3.1 -> G3a.

---

## 0. Objects and the split convention [R:A3 — the half-open fix]

M = floor(lambda^2); D_s(gamma) = sum_{m<=M-1} m^{-s+i*gamma}; D := D_{1/2}.
SPLIT CONVENTION (half-open; kills the boundary double count found in the
adversarial pass): at INTEGER lambda^2 the m = M tooth sits EXACTLY at the
window edge u = lambda/M = lambda^{-1}. Therefore:
  K^comb := jumps at u = lambda/m for 1 <= m <= M-1 (strictly interior;
            includes the right window edge u = lambda, which is the m=1 tooth);
  B_L    := the single boundary atom at u = lambda^{-1}, carrying the FULL
            boundary value E(g)(lambda^{-1}+) (this absorbs the m = M tooth
            content AND the window truncation drop) — bounded in PEN 3.1.4a;
  K^smooth := the AC part (node 3.1.4b, parked).
No point mass is counted twice; the deciding numerical identity is bus
goal 004 (SplitIdentityCheck).

From 3.1.1 (IBP): K^comb(gamma) = g(lambda) lambda^{1/2-i*gamma} D(gamma)/(i*gamma),
g^2 ~ lambda^{10} E (node 3.1.2; k_edge^2 = lambda g^2 ~ lambda^{11} E,
two channels 11.27 / 10.61).

ZERO-COUNT CONVENTION [R:A4]: N_+(T) = #{0 < gamma <= T} (positive
ordinates, with multiplicity), N_pm(T) = 2 N_+(T). The Guinand–Weil sum in
a_1 is written as 2 * sum over the positive-ordinate multiset; all density
integrals below use dN_+ ~ (1/2pi) log(t/2pi) dt. No implicit factor 2.

## 1. Lemma FarComb-U (UNCONDITIONAL magnitude bound; G3a-grade)

Claim. With no hypothesis on zero locations,
  2 sum_{|gamma_rho| > Gamma} |Khat^comb(rho) Khat^comb(1-rho)|
     <= C * lambda^{11} (log lambda) * E,        Gamma = 4*pi*lambda^2.

[R:A1] SCOPE SENTENCE: this lemma bounds the ABSOLUTE zero-side comb
contribution; it discards the Hermitian sign/phase information (conjugate
cancellations, the distinction 1-rho vs conj(rho)). It is a magnitude
budget, not a positivity or RH-diagnostic statement. For a real test
function Khat(conj(rho)) = conj(Khat(rho)); an off-line quartet contributes
4 Re{Khat(rho)Khat(1-rho)} <= 4 |Khat(rho)Khat(1-rho)|; multiplicities ride
on the ordered multiset.

Proof. At rho = beta + i*gamma the comb weight becomes m^{-beta}; for the
symmetrized pair
  |Khat(rho) Khat(1-rho)| <= g^2 lambda * S(beta) S(1-beta) / gamma^2,
  S(beta) = sum_{m<=M-1} m^{-beta}.
[R:A2 — sharp sup, adversarial gift] log S(beta) is convex, so
log S(beta) + log S(1-beta) is convex and symmetric on [0,1]; its maximum
is at the boundary:
  sup_{beta in [0,1]} S(beta) S(1-beta) = S(0) S(1) = (M-1) H_{M-1}
     <= M (log M + 1).
(The center beta = 1/2 gives only ~ 4M.) Summing over zeros with the
unconditional Riemann–von Mangoldt density dN_+:
  sum_{gamma > Gamma} gamma^{-2} dN_+ <= (log(Gamma/2pi) + 1)/(2 pi Gamma).
Multiplying: g^2 lambda * M H_M * log(Gamma)/Gamma-scale
  ~ lambda^{10} E * lambda * lambda^2 log lambda * (log lambda / lambda^2)
  = lambda^{11} (log lambda)^2 E;  with the sharp M H_M in place of the
v1 worst-case guess the honest class is C lambda^{11} (log lambda)^2 E and
the constant is explicit. QED.

ASSEMBLY LINE [R:A3]: for the full K = K^comb + B_L + K^smooth, per pair
  |K(rho)K(1-rho)| <= (|K(rho)|^2 + |K(1-rho)|^2)/2,
  |K|^2 <= 3(|K^comb|^2 + |B_L|^2 + |K^smooth|^2),
so FAR <= 3 (FarComb-U + B_L-budget [PEN 3.1.4a: lambda^3 (log) E]
            + SmoothBudget [3.1.4b, the single open item]).
Cross terms never need separate treatment.

## 2. Lemma FarComb-S (SHARP class; RH-conditional / on-line label)

[R:B4 — EXPLICIT FIREWALL BLOCK]
  FarComb-S is RH-conditional / on-line only.
  It may calibrate the mechanism and explain observed zero-line data.
  It is not an input to FarComb-U.
  It is not an input to any implication whose conclusion is RH.

Engine: BFM Theorem 3.1 [Bui–Florea–Milinovich; Bull. LMS 2024,
DOI 10.1112/blms.13092; arXiv:2310.03949; CONDITIONAL(RH)], specialized
to a_n = 1, x = M:
  sum_{0<gamma<=T} |D(gamma)|^2 = N_+(T) H_M - (T/pi) A_M
                                   + O(M (log MT)^2 H_M),
[R:B1 — exact closed form, adversarial gift]
  A_M := sum_{kn<=M} Lambda(k)/(kn) = sum_{m<=M} (log m)/m
  (Chebyshev: sum_{k|m} Lambda(k) = log m). No stray factor: the -T/pi
  already contains the 2 Re of the off-diagonal pairs.
Numerical values (M = 13): H_13 = 3.1801337551; A_13 = 3.3145471980.

Partial summation over [Gamma, infinity), Gamma = 4*pi*M:
log(Gamma/2pi) = log(2M), and the (log M)^2 pieces of H_M log(Gamma/2pi)
and 2 A_M cancel:
  sum_{gamma > Gamma} |D(gamma)|^2/gamma^2
     = [H_M (log(Gamma/2pi) + 1) - 2 A_M]/(2 pi Gamma) + err = O(log M)/Gamma.
[R:B2 — finite-M brackets, all positive at M = 13]:
  leading normalization:      H_13 - 2 A_13 / L        = 1.1455  (L = log 26)
  with the RvM "-1":          H_13 - 2 A_13 / (L - 1)  = 0.2444
  with the "+7/8" term:                                 0.2875
Sign does not flip; the margin at the working point is thin but positive.
Resulting sharp class: FAR^comb_S <= C' lambda^9 (log lambda) E;
safe fallback (drop the negative arithmetic term): lambda^9 (log lambda)^2 E.

[R:B3 — independence sentence] The falsifier comparison (bus 001:
measured 1.8647 vs predicted 1.853 at J = 2000, 0.63%) is independent in
the CALIBRATION sense: the prediction uses only the analytic BFM/Gonek
arithmetic terms and zero-density normalization, not the measured
ordinates; it is not independent in the stronger ontological sense, since
BFM is itself a theorem about the same zeta zeros.

## 3. Adjacent imports (adversarial literature channel)

- Benli–Elma–Ng, arXiv:2311.13554: twisted sums zeta(rho+alpha) X(rho)
  Y(1-rho), N << T^theta, theta < 1/2; unconditional and GRH regimes.
  Adjacent (functional-equation-paired), NOT a substitute for the
  real-ordinate |D|^2 form. Useful for future twisted bookkeeping.
- DHPC 2026 (arXiv:2601.06292, 2601.18025): derivative discrete moments
  and chi(rho) X^rho generalizations; complementary, not superseding.
- Negative search re-confirmed: no unconditional real-argument |D(gamma)|^2
  over ordinates with N ~ T^theta; the sum_rho |beta - 1/2| obstruction
  stands.

## 4. Status

U-branch: adversarially PASSED (magnitude scope + half-open split +
sharp beta-sup + locked zero-count conventions). Comb incoherence CLOSED.
Assembly of full FAR waits only on 3.1.4b SmoothBudget.
S-branch: PASSED as conditional mechanism (firewall explicit); falsifier
001 confirmed at 0.63%.
Deciding numerical check of the split convention: bus goal 004.
