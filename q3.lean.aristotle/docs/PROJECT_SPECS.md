# PROJECT SPECS: Rayleigh bridge + fixed-t density (BASE-SYNCED)

---

## §0. Status and goal

**Goal:** Prove only $Q(\Phi) \ge 0$ for all $\Phi \in \mathcal{W}$.

**Status:** Conditional chain "Tier-2 ==> RH" via Weil criterion (no "RH proven").

---

## §0.1 Audit guardrails (prevent drift)

- Canonical checklist: `full/q3.lean.aristotle/docs/CHECKLIST_AUDIT_2026_01_17.md`.
- Quick invariant check: `full/q3.lean.aristotle/scripts/check_audit_invariants.sh`.
- Before merge: run the script; if any anchor changed, update the checklist.

## §1. Normalization / sign / torus (LOCKED)

### Sign (MINUS)
$$
Q(\Phi) = Q_{\mathrm{arch}}(\Phi) - Q_{\mathrm{prime}}(\Phi)
$$

### T0 normalization
$$
a_*(\xi) = 2\pi a(\xi), \qquad \xi_n = \frac{\log n}{2\pi}
$$

### Period-1 torus
$$
\mathbb{T} = [-1/2, 1/2], \quad e_k(\theta) = e^{2\pi i k\theta}, \quad d\theta
$$

### A3 symbol (period-1)
$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t_{\mathrm{sym}}}(\theta + m),
\quad g_{B,t}(\xi) = a(\xi)\Phi_{B,t}(\xi)
$$

---

## §1.1 Contract checks (RH_Q3)

- A3 symbol is `P_A` (periodized, windowed). Do not use `a_star` as A3 symbol.
- Toeplitz in A3 uses Fourier/Rayleigh on period-1 torus; sampling `P(π(i-j)/M)` is not allowed in the main chain.
- Prime operator in A3 is the compression/rank-one sum `T_P^{(M)}` with `w_Q`, not direct-indexed Gaussian.
- Keep `t_sym` (symbol) and `t_rkhs` (cap) distinct; do not mix `w_Q` and `w_RKHS`.

---

## §2. Tier-1 facts

### Weil criterion
$$
Q \ge 0 \text{ on } \mathcal{W} \iff \mathrm{RH}
$$

### Toeplitz quadratic form (Rayleigh core)
For trig polynomials $p$ in $P_M$:
$$
\langle T_M[P_A]p,p\rangle = \int_{\mathbb{T}} P_A(\theta) |p(\theta)|^2\,d\theta
$$

### Rayleigh lower bound (no Szego-Bottcher needed)
$$
\lambda_{\min}(T_M[P_A]) \ge \min_{\theta \in \mathbb{T}} P_A(\theta)
$$

**Note:** The classical Szego-Bottcher estimate
$$
\lambda_{\min}(T_M[\sigma]) \ge \min \sigma - C_{SB} \cdot \omega_\sigma(1/(2M))
$$
is **optional** and follows as a corollary since $\omega_\sigma \ge 0$.

---

## §3. Tier-2 modules (current plan)

### A1' density (fixed $t_0$, hat interpolation)
Atoms are restricted by the margin condition:
$$
|\tau| + B \le K
$$
so support stays in $[-K,K]$. Use hat interpolation (Lemma 6.4) on $[-K,K]$.

### A2 (Lipschitz)
$Q$ is Lipschitz on each $\mathcal{W}_K$.

### A3 floor (pointwise)
$$
P_A(\theta) \ge c_* = 11/10 \quad \forall \theta \in [-1/2, 1/2]
$$

### RKHS cap
For $t_{\mathrm{rkhs}} \ge t_{*,\mathrm{rkhs}}^{\mathrm{unif}} = 1$:
$$
\|T_P\| \le \rho(1) < 1/25
$$

### Rayleigh bridge (p = 1)
$Q(\Phi_{B,t_{\mathrm{sym}}})$ matches the Rayleigh identity at $p \equiv 1$ in two
equivalent forms (see `full/sections/A3/calibration.tex` and
`full/sections/A3/rayleigh_bridge.tex`):

- **Infinite-dimensional idealization:** $\langle (T_M[P_A]-T_P)1,1\rangle = Q(\Phi)$.
- **Finite-dimensional compression:** $\langle T_M[P_A]1,1\rangle - (2M+1)\langle T_P^{(M)}1,1\rangle = Q(\Phi)$.

The factor $(2M{+}1)$ comes from the normalization of $v_n^{(M)}$ and the identity
$\iota_M^\ast T_P \iota_M = (2M{+}1)\,T_P^{(M)}$.

---

## §4. Discretization (optional)

No $M_0$ is required if we use the Rayleigh lower bound directly.
If we still want Szego-Bottcher, treat it as a weaker corollary:
$$
\lambda_{\min} \ge \min P_A \ge \min P_A - 4\,\omega_{P_A}(1/(2M))
$$

---

## §5. Positivity on generators

1) **A3 floor:** $P_A \ge c_*$ (pointwise)
2) **Rayleigh:** $\lambda_{\min}(T_M[P_A]) \ge c_*$
3) **RKHS cap:** $\|T_P\| \le c_*/4$

Hence
$$
\lambda_{\min}(T_M[P_A] - T_P) \ge c_* - \|T_P\| \ge 3c_*/4 > 0
$$
so $Q(\Phi_{B,t_{\mathrm{sym}}}) \ge 0$ in the idealized operator form. For the
finite-dimensional Lean operator, replace $T_P$ by the compressed $T_P^{(M)}$
(a.k.a. `T_P_comp`); the cap applies to the normalized vectors, and the
$(2M{+}1)$ factor only appears when converting $\langle T_P^{(M)}1,1\rangle$
to the prime sum in the $p\equiv1$ identity.

---

## §6. Closure and RH

By A1'+A2 we extend $Q \ge 0$ from generators to all of $\mathcal{W}_K$, then to $\mathcal{W}$.
By Weil criterion we obtain **RH (conditional on Tier-2)**.

---

## §7. Key invariants (checklist)

| # | Invariant | Value |
|---|-----------|-------|
| 1 | Sign | $Q = Q_{\mathrm{arch}} - Q_{\mathrm{prime}}$ |
| 2 | Normalization | $\xi_n = \log n/(2\pi)$, $a_* = 2\pi a$ |
| 3 | Torus | period-1, $\mathbb{T} = [-1/2, 1/2]$ |
| 4 | Symbol | $P_A = 2\pi \sum_m g(\theta+m)$ |
| 5 | Floor | $c_* = 11/10$ (NOT 1.5) |
| 6 | Rayleigh | $\lambda_{\min} \ge \min P_A$ (no SB needed) |
| 7 | Prime cap | $t_{\mathrm{rkhs}} \ge 1 \Rightarrow \rho(1) < 1/25$ |
| 8 | Goal | $Q(\Phi) \ge 0$ (NOT $\ge 1.125$) |

---

## §8. Response format

- Short "matches / mismatches" report for items 1-8
- Reassembled text of §0-§8 (single block)
- No new notation, no external links

---

## DO NOT DO

- Do NOT revert to $c_* = 1.5$
- Do NOT require Szego-Bottcher as a blocker (use Rayleigh bound)
- Do NOT change the sign convention
- Do NOT switch to $2\pi$-periodic torus
- Do NOT claim $Q \ge 1.125$ without normalization
- Do NOT use sampling Toeplitz `P(π(i-j)/M)` in the A3 chain
- Do NOT mix `t_sym` with `t_rkhs` or `w_Q` with `w_RKHS`

---

## Context pack (.tex base)

| File | Module |
|------|--------|
| `full/sections/T0.tex` | T0 normalization |
| `full/sections/A3/symbol_floor.tex` | A3 floor |
| `full/sections/A3/rayleigh_bridge.tex` | Toeplitz quadratic form + Rayleigh |
| `full/sections/A3/matrix_guard.tex` | (Optional) Szego-Bottcher discretization |
| `full/sections/RKHS/prime_trace_closed_form.tex` | RKHS cap |
| `full/sections/A1prime.tex` | A1' density (fixed t0) |
| `full/sections/A2.tex` | A2 Lipschitz |
| `full/sections/Main_closure.tex` | Closure |
| `full/sections/Weil_linkage.tex` | Weil linkage |

---

**END OF PROSHKA REQUEST v4**
