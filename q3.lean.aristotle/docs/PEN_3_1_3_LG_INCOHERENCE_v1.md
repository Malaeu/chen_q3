# PEN NOTE 3.1.3 — Incoherence of the Jump Comb over Zeros (draft v1)

STATUS: DRAFT v1 (Mythos pen), awaiting adversarial pass (Прошка) per P5.
Node: 3.1.3 of PROJECT_TREE. Feeds: EdgeJumpTailBound (3.1) -> G3a (3).
FIREWALL-COMPLIANT: the unconditional branch uses no zero-location input;
the sharp branch is explicitly labeled (on-line ordinates / RH-class) and
is NOT part of the concluding chain — it is the mechanism/ledger science.

---

## 0. Objects

M = floor(lambda^2);  D_s(gamma) = sum_{m<=M} m^{-s+i*gamma}  (s in [0,1]);
D := D_{1/2}.  From node 3.1.1 (jump ladder + IBP), the comb part of the
Fourier–Mellin transform of the guess is

  K^comb(gamma) = g(lambda) * lambda^{1/2 - i*gamma} * D(gamma) / (i*gamma),

with g(lambda) = endpoint value of the prolate combination (node 3.1.2:
g^2 ~ lambda^{10} E, since k_edge^2 = lambda * g^2 ~ lambda^{11} E,
E = exp(-4*pi*lambda^2); measured two channels 11.27 / 10.61).
Decomposition K = K^comb + K^rem, where K^rem = (left-edge term at
u = lambda^{-1}) + (smooth remainder). K^rem is parked in node 3.1.4
(SmoothRemainderTail; amplitude calibrated ~3e-29 at (13,120) by
TroughBoundary). For UPPER bounds the triangle inequality
|K|^2 <= 2|K^comb|^2 + 2|K^rem|^2 suffices; measured cancellation
(the trough) only helps.

FAR := 2 * sum_{gamma_rho > Gamma} (zero-pair mass),  Gamma = 4*pi*lambda^2 = 4*pi*M.

## 1. Lemma FarComb-U (UNCONDITIONAL budget bound; G3a-grade)

Claim. There is an absolute C such that, with no hypothesis on zero
locations,

  2 * sum_{|gamma_rho| > Gamma} |Khat(rho) Khat(1-rho)|_comb
      <= C * lambda^{11} (log lambda)^2 * E.

Proof (6 lines). Zeros come in pairs rho <-> 1-rho, beta in [0,1]. The
IBP comb evaluated at rho = beta + i*gamma replaces the m^{-1/2} weight by
m^{-beta}; hence
  |Khat^comb(rho)| <= g * lambda^{1/2} * (sum_{m<=M} m^{-beta}) / |gamma|.
For the symmetrized pair,
  |Khat(rho) Khat(1-rho)| <= g^2 lambda * (sum m^{-beta})(sum m^{-(1-beta)}) / gamma^2
      <= g^2 lambda * C0 * M * (log M + 1) / gamma^2
(uniformly in beta in [0,1]: worst case beta -> 0 or 1 gives M * (log M + O(1))).
Sum over zeros with the UNCONDITIONAL Riemann–von Mangoldt density:
  sum_{gamma > Gamma} gamma^{-2} dN(gamma) <= (log(Gamma/2pi) + 1) / (2*pi*Gamma).
Multiply: g^2 ~ lambda^{10} E, M ~ lambda^2, Gamma ~ 4*pi*lambda^2 gives
  <= C * lambda^{10} E * lambda * lambda^2 log lambda * (log lambda / lambda^2)
   = C * lambda^{11} (log lambda)^2 * E.   QED.

Consequence. For the G3a budget (|a| <= poly(lambda) * E) the comb part of
FAR is CLOSED unconditionally by this coherent bound. The Landau–Gonek
machinery is NOT needed for the budget — only for the sharp class below.

## 2. Lemma FarComb-S (SHARP class; labeled: on-line ordinates / RH-class)

First-moment engine: Gonek's uniform Landau formula
[Invent. Math. 75 (1984), 123-141; digest item 1.2; THEOREM, unconditional]:
  sum_{0<gamma<=T} x^{rho} = -(T/2pi) Lambda(x) + O(x log(2xT) loglog(3x))
      + O(log x * min(T, x/<x>)) + O(log 2T * min(T, 1/log x)).
Assembled discrete second moment (digest item 1.3 = Bui–Florea–Milinovich
Thm 3.1, arXiv:2310.03949; CONDITIONAL(RH) via |A(rho)|^2 = A(rho)A(1-rho))
specialized to a_n = 1 (n <= M), x = M:

  (A)  sum_{0<gamma<=T} |D(gamma)|^2
        = N(T) * H_M  -  (T/pi) * A_M  +  O( M (log MT)^2 H_M ),
       H_M = sum_{m<=M} 1/m,
       A_M = sum_{n<=M} (1/n) sum_{p^k <= M/n} Lambda(p^k) p^{-k}.

By Mertens (unconditional): A_M = (log M)^2/2 + O(log M);
H_M = log M + gamma_E + O(1/M).

Partial summation over [Gamma, infinity):

  (B)  sum_{gamma > Gamma} |D(gamma)|^2 / gamma^2
        = [ H_M (log(Gamma/2pi) + 1) - 2 A_M ] / (2*pi*Gamma) + err.

KEY CANCELLATION at the crossover Gamma = 4*pi*M:
log(Gamma/2pi) = log M + log 2, hence
  H_M (log M + log 2 + 1) - 2 A_M = (log M)^2 - (log M)^2 + O(log M) = O(log M):
the squared logarithms cancel EXACTLY at the measured crossover height.
Therefore
  (C)  FAR^comb_sharp <= C' * lambda^9 (log lambda) * E,
one logarithm BETTER than the registered class lambda^9 (log lambda)^2 E.
Safe fallback (dropping the negative arithmetic term, still an upper
bound): lambda^9 (log lambda)^2 E.

Epistemic label. |A(rho)|^2 = A(rho)A(1-rho) needs beta = 1/2. An
unconditional real-argument version of (A) would need control of
sum_{zeros} |beta - 1/2| (digest: structural obstruction, negative search
confirmed). Hence (C) is stated for the on-line mass (equivalently under
RH) and serves as the MECHANISM result explaining the measured ledger; it
never enters the concluding chain — FarComb-U does that job.

Sign check: the arithmetic term is NEGATIVE — primes repel zeros; the
truncated zeta correlates with zeta, so |D| is suppressed at ordinates.
Quantitative form of the measured zeta-signature (dips of |K| at zeros).

## 3. Registered falsifiers (Codex; bus goal 001)

Constants (M = 13): H_13 = 3.18013;
A_13 = 2.11003 + 0.60398 + 0.29538 + 0.17820 + 0.06931 + 0.05776 = 3.31466
(n = 1..6; empty for n >= 7).
F1 predictions: mean_{j<=2000} |D(gamma_j)|^2 = 1.853, band [1.55, 2.15];
mean_{j<=500} = 1.468, band [1.10, 1.90]; null 3.18 excluded at J=2000.
F2: midpoint mean >= zero mean (direction only).

## 4. Attack surface for Прошка (self-declared)

(a) K = K^comb + K^rem split: left-edge term at u = lambda^{-1} parked in
    3.1.4; until 3.1.4 closes, FarComb-U bounds the comb part only; the
    triangle-inequality assembly is written in Section 0.
(b) Uniformity of the beta-bound at beta -> 0, 1: worst case gives
    M(log M + O(1)); a safety log was added to the class.
(c) Exactness of the (log M)^2 cancellation depends on Mertens constants;
    the safe class (log)^2 stands regardless.
(d) Multiplicities: RvM counts with multiplicity; all bounds are
    per-zero-pair and survive verbatim.

## 5. Node status after this note

3.1.3 = TWO branches:
  U-branch (budget, unconditional): CLOSED at pen level (6-line proof),
    class lambda^{11}(log lambda)^2 E — awaiting adversarial pass only.
  S-branch (mechanism, labeled): class lambda^9 (log lambda) E with exact
    log-cancellation at Gamma = 4*pi*M — awaiting bus goal 001 (F1/F2)
    and adversarial pass.
G3a-consequence: with 3.1.1 + 3.1.2 + FarComb-U, the ENTIRE far tail
except the 3.1.4 remainder is unconditionally within poly * E.
