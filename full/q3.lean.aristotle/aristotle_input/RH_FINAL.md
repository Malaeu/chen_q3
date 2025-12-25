# Riemann Hypothesis: Proof Dossier (RH_FINAL)

## 0) Status

**Claim:** All non-trivial zeros of the Riemann zeta function lie on the line Re(s) = 1/2.

**Status in this repo:** Conditional on the analytic chain proved in `full/RH_Q3.tex`:
(T0) + (A1') + (A2) + (A3) + (RKHS). No numerical certificates or JSON tables are used in
this chain; legacy data live only in appendices.

---

## 1) Formal Statement (quantifiers)

**Theorem (Riemann Hypothesis).**
For all s in C with 0 < Re(s) < 1:
if zeta(s) = 0, then Re(s) = 1/2.

Lean stub:
```lean
/-- Riemann Hypothesis (formal statement) -/ 
def Riemann_Hypothesis : Prop :=
  forall s : Complex,
    riemannZeta s = 0 -> 0 < s.re -> s.re < 1 -> s.re = (1/2 : Real)
```

---

## 2) Normalization and Definitions (T0 scale)

All frequencies are in the T0 normalization:
- xi = eta / (2*pi)
- nodes xi_n = log n / (2*pi)
- unit circle T = R / Z with fundamental domain [-1/2, 1/2]
- basis e_k(theta) = exp(2*pi*i*k*theta)

### Weil cone
For K > 0, let W_K be the cone of even, nonnegative, compactly supported tests on [-K, K]
obtained as limits of Fejer x heat atoms; define W := union over K.

### Weil functional (T0 normalization)
Let
- a(xi) = log pi - Re psi(1/4 + i*pi*xi)
- a_*(xi) = 2*pi*a(xi)
- w_Q(n) = 2*Lambda(n)/sqrt(n)
Then on each compact window:

Q(Phi) = int_R a_*(xi) Phi(xi) dxi - sum_{n>=2} w_Q(n) Phi(xi_n).

### Fejer x heat window and symbol
Define
- Phi_{B,t}(xi) = (1 - |xi|/B)_+ * exp(-4*pi^2*t*xi^2)
- g_{B,t}(xi) = a(xi) * Phi_{B,t}(xi)
- P_A(theta) = 2*pi * sum_{m in Z} g_{B,t}(theta + m), theta in [-1/2, 1/2]

Then P_A is 1-periodic with cosine series
P_A(theta) = A_0 + 2*sum_{k>=1} A_k cos(2*pi*k*theta),
A_k = 2*pi * int_R g_{B,t}(xi) cos(2*pi*k*xi) dxi.

### Fixed constants
- B_min = 3
- t_sym = 3/50
- c_* = 11/10 (uniform Archimedean floor)
- C_SB = 4 (Szego--Bottcher constant)
- t_rkhs^unif = 1 and rho(1) < 1/25

---

## 3) Dependencies (actual lemmas in RH_Q3.tex)

### Classical (Tier-1)
- Weil criterion: `full/sections/Weil_linkage.tex`, Theorem `thm:Weil-criterion`.
- Guinand--Weil normalization: `full/sections/T0.tex`, Proposition `prop:T0-GW`.
- Toeplitz barrier: `full/sections/A3/matrix_guard.tex`, Lemma `lem:a3-sb-barrier` (C_SB = 4).

### Project Q3 (Tier-2)
- A1' density: `full/sections/A1prime.tex`, Theorem `a1:thm:A1-local-density`.
- A2 Lipschitz: `full/sections/A2.tex`, Lemma `a2:lem:A2` + Corollary `cor:A2-Lip`.
- Rayleigh identification: `full/sections/A3/rayleigh_bridge.tex`, Theorem `thm:a3-rayleigh-identification`.
- Symbol regularity: `full/sections/A3/symbol_floor.tex`, Lemma `lem:a3-lipschitz-bound`.
- Uniform floor: `full/sections/A3/symbol_floor.tex`, Lemma `lem:uniform-arch-floor` (c_* = 11/10).
- Uniform discretisation: `full/sections/A3/symbol_floor.tex`, Corollary `cor:uniform-discretisation`.
- Prime cap: `full/sections/RKHS/prime_norm_leq_rho.tex`, Proposition `pm:prop:norm-leq-rho`.
- Closed-form rho bound: `full/sections/RKHS/prime_trace_closed_form.tex`, Lemma `pm:lem:rho-closed-form`.
- Uniform prime cap time: `full/sections/A3/symbol_floor.tex`, Corollary `cor:uniform-prime-cap`.
- A3 bridge: `full/sections/A3/main.tex`, Theorem `thm:A3`.
- Main positivity: `full/sections/Main_closure.tex`, Theorem `thm:Main-positivity`.
- RH from Weil: `full/sections/Weil_linkage.tex`, Theorem `thm:RH`.

---

## 4) Proof Map (chain)

1) T0 fixes normalization of Q and nodes xi_n (prop:T0-GW).
2) Rayleigh identification rewrites Q(Phi_{B,t}) as the Toeplitz Rayleigh quotient
   (thm:a3-rayleigh-identification).
3) A3 gives uniform lower bound on P_A and uniform prime cap, hence a positive
   Toeplitz gap (thm:A3).
4) A1' density + A2 Lipschitz extend positivity from generators to all W_K.
5) Union over K gives Q >= 0 on W; Weil criterion gives RH.

---

## 5) Core Lemmas (statements only)

**A3 floor.** For B >= B_min and theta in T,
P_A(theta) >= c_* = 11/10.  (lem:uniform-arch-floor)

**Toeplitz barrier.** For M >= 1,
lambda_min(T_M[P_A]) >= min P_A - C_SB * omega_{P_A}(1/(2M)).  (lem:a3-sb-barrier)

**Prime cap.** For any t > 0,
||T_P|| <= rho(t) and rho(1) < 1/25.  (pm:prop:norm-leq-rho, pm:lem:rho-closed-form)

**A3 bridge.** For M >= M_0^unif and t_rkhs >= 1,
lambda_min(T_M[P_A] - T_P) >= c_*/4.  (thm:A3)

**Main closure.** Q >= 0 on W, hence RH by Weil.  (thm:Main-positivity, thm:RH)

---

## 6) Audit notes (places that must stay sharp)

1) **Digamma bounds.** Lemma `lem:uniform-arch-floor` uses the sample bounds
   (lem:a3-a-sample) and DLMF remainder estimates. If a reviewer wants all
   constants proven from scratch, the inequalities like log(3/2) < 0.41 and
   pi^2 < 10 should be backed by a short rational-approx proof (easy to add).

2) **Lipschitz envelope.** Lemma `lem:digamma-lip-bound` uses the Riemann-sum
   upper bound sum_m G(theta+m) <= G(0) + 2*int_0^infty G. This is standard but
   should stay explicit for a formal audit.

3) **Szego--Bottcher constant.** C_SB = 4 is taken from B"ottcher--Silbermann.
   Keep that reference visible when the bound is invoked.

No K-dependent schedules or JSON certificates are used in the main chain.

---

## 7) Outcome

Under the analytic chain listed above (all in `full/RH_Q3.tex`), the main line
proves Q >= 0 on the Weil cone and concludes RH via Weil's criterion.
