═══════════════════════════════════════════════════════
MODULE: A3 (Toeplitz Bridge) — Analytic Rewrite Template
═══════════════════════════════════════════════════════

## OVERVIEW
- Goal: Section A3 contains a full analytic proof of 
  \[
    \lambda_{\min}\!\bigl(T_M[P_A]-T_P\bigr) \ge \frac{1}{2}(\,c_0(K)-\rho_K\,)
  \]
  on each compact $[-K,K]$, without JSON/ATP artifacts.
- Deliverables: self-contained lemmas/theorems replacing all “lock” tables; explicit references to published sources (Böttcher–Silbermann, Stein–Shakarchi, etc.).

## STRUCTURE (BRICKS)

### Brick A3.1 — Rayleigh Identification (2–3 pages)
- Input: Definition of $Q$, normalization T0, operator framework.
- Task: Show $Q(\Phi) = \langle (T_M[P_A]-T_P)u,u\rangle$ for appropriate vectors $u$.
- Output: Theorem A3.1 (Rayleigh–Toeplitz correspondence).
- Status checklist: ☐ draft ☐ review ☐ final.

### Brick A3.2 — Szegő–Böttcher Symbol Floor (3–4 pages)
- Input: Archimedean density $a(\xi)=\log\pi-\Re\psi(\tfrac14+i\pi\xi)$.
- Tasks:
  - Prove $P_A$ is Lipschitz and $P_A(\theta)\ge c_{\min}(K)>0$ analytically.
  - Cite Böttcher–Silbermann for the barrier constant $C_{\mathrm{SB}}$.
- Outputs: Lemma A3.2(a) (explicit $c_{\min}$), Lemma A3.2(b) (symbol barrier).
- Status: ☐ draft ☐ review ☐ final.

### Brick A3.3 — Fejér × Heat Modulus Control (4–5 pages)
- Input: Fejér kernel $F_M$ and heat kernel $\rho_t$.
- Tasks:
  - Bound $\omega_{P_A}(\pi/M)$ purely analytically.
  - Prove uniform Lipschitz estimates on $[-K,K]$.
- Outputs: Lemma A3.3(a) (modulus bound), Lemma A3.3(b) (Lipschitz control).
- Status: ☐ draft ☐ review ☐ final.

### Brick A3.4 — Gershgorin & Mixed Bound (3–4 pages)
- Input: Bricks A3.1–A3.3.
- Tasks:
  - Apply Gershgorin / spectral estimates to $T_M[P_A]$.
  - Combine with Rayleigh form to obtain $\lambda_{\min}\ge \tfrac12(c_0-\rho_K)$.
- Output: Theorem A3.4 (Mixed bridge inequality).
- Status: ☐ draft ☐ review ☐ final.

### Brick A3.5 — Transition to RKHS Path (1–2 pages)
- Input: Theorem A3.4, RKHS framework (Paulsen–Raghupathi).
- Task: Show how the Toeplitz bound interfaces with RKHS contraction / IND route.
- Output: Corollary A3.5 (feeds RKHS/T5 section).
- Status: ☐ draft ☐ review ☐ final.

## DEPENDENCIES
- A3.1 ← T0 normalization, operator preliminaries.
- A3.2 ← digamma properties (cite NIST DLMF), Böttcher–Silbermann.
- A3.3 ← Fejér/heat analysis (cite Stein–Shakarchi).
- A3.4 ← matrix analysis (Gershgorin, Horn–Johnson).
- A3.5 ← RKHS sampling (Paulsen–Raghupathi) or IND route appendix.

## EXTERNAL REFERENCES TO CONFIRM
- Böttcher & Silbermann, *Introduction to Large Truncated Toeplitz Matrices* (2006).
- Stein & Shakarchi, *Fourier Analysis* (2003).
- Grenander & Szegő, *Toeplitz Forms*.
- Horn & Johnson, *Matrix Analysis* (Gershgorin, matrix inequalities).
- Paulsen & Raghupathi, *RKHS Theory*.

## SUCCESS CRITERIA
- All bounds $c_0(K)$, $\omega_{P_A}$ derived analytically.
- No `\input{...param_tables}` or references to `cert/bridge/…`.
- Each lemma/theorem has statement + proof with journal-ready references.
- Section A3 build succeeds standalone; appendices contain only supplemental numerics.

## TIMELINE (FIRST 20 HOURS SNAPSHOT)
1. Inventory legacy materials in `docs/` related to A3 (≈2h).
2. Draft Brick A3.1 + A3.2(a) (≈6h).
3. Complete A3.2(b) + A3.3 (≈6h).
4. Assemble A3.4 + interface to RKHS (≈6h).

Progress log:
- [ ] Hour 0–2:
- [ ] Hour 2–8:
- [ ] Hour 8–14:
- [ ] Hour 14–20:

