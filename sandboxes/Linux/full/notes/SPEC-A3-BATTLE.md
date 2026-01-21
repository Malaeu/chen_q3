
SPEC-A3-BATTLE.md
══════════════════

Phase 0: Material Harvest (≈2h)
  - [x] Extract legacy analytic content:
    • docs/lemmas/A3_bridge_outline.md
    • docs/tex/A3_toeplitz_symbol_bridge.tex
    • docs/tex/A3_calibration_kappa.tex
    • docs/tex/theorems/A3LockGlobal.tex
  - [x] Identify which lemmas are purely analytic vs. reliant on JSON.
  - [x] Catalog constants (c₀(K), Lipschitz bounds, C_SB).

  _Notes:_  
  • `docs/lemmas/A3_bridge_outline.md` summarises the Rayleigh–Toeplitz equivalence and required Lipschitz bounds.  
  • `docs/tex/A3_toeplitz_symbol_bridge.tex` contains detailed lemmas (model-space restriction, prime projection, Lipschitz/positivity bounds) suitable for Bricks A3.1–A3.3.  
  • `docs/tex/A3_calibration_kappa.tex` fixes the scale factor $\kappa_{\mathrm{A3}}$, clarifying the role of the Archimedean density in the Rayleigh pairing.  
  • `docs/tex/theorems/A3LockGlobal.tex` collects earlier formal statements for A3-lock; needs rederivation without JSON inputs.
  
  _Dependency audit:_  
  • Legacy tex files listed above are analytic (no references to `cert/bridge`).  
  • Current `sections/A3/main.tex` imports `sections/A3/param_tables.tex`, which in turn reflects JSON data (`cert/bridge/K*_A3_lock.json`).  
  • Assumption (A3.3) and grid parameters presently depend on these tables; they must be replaced by analytic bounds during rewrite.

  _Constants summary:_  
  • $c_0(K)$ — Archimedean floor from Corollary in `A3_toeplitz_symbol_bridge.tex` (depends on $B$, $t_{\mathrm{sym}}$, local infimum $m_r$).  
  • $L_A(B,t_{\mathrm{sym}})$ — Lipschitz bound computed in Proposition (11.4) of the same file.  
  • $C_{\mathrm{SB}}$ — Szegő–Böttcher constant (explicitly recorded as 4 in `A3_toeplitz_symbol_bridge.tex`, to be tied to Böttcher–Silbermann).  
  • $\kappa_{\mathrm{A3}}=2\pi$ — calibration constant from `A3_calibration_kappa.tex`.  
  • $\rho_K$, $\rho_{\mathrm{cap}}$ — RKHS/trace caps defined in existing RKHS section; will require analytic restatement.

Phase 1: Brick A3.1 — Rayleigh Identification (≈6h)
  1.1 [x] Parse “Rayleigh identification” outline in A3_bridge_outline.md.
  1.2 [x] Extract Lemmas (model-space restriction, prime projection) from A3_toeplitz_symbol_bridge.tex.
  1.3 [x] Formalize Theorem A3.1: Q(Φ)=⟨(T_M[P_A]-T_P)u,u⟩.
  1.4 [x] Draft proof independent of tables/locks.
  1.5 [x] Self-audit (Haiku RULE 1–5).

  _Deliverable:_ `sections/A3/rayleigh_bridge.tex` now contains Lemmas~\ref{lem:a3-model-space}, \ref{lem:a3-rayleigh-quotient} and Theorem~\ref{thm:a3-rayleigh-identification}, reproducing the Rayleigh identification purely analytically (citations: Grenander–Szegő, Lemma~\ref{t0:lem:T0}). No references to param tables or JSON remain.

Phase 2: Brick A3.2 — Symbol Floor (Szegő–Böttcher) (≈6h)
  2.1 [x] Use BV→Lip lemmas to estimate Lipschitz constants.
  2.2 [x] Derive explicit symbol floor c_min from digamma bounds (cite NIST DLMF).
  2.3 [x] Record Szegő–Böttcher constant C_SB (Böttcher–Silbermann 2006).
  2.4 [x] Write Lemma A3.2a (c_min) & A3.2b (barrier inequality).
  2.5 [x] Audit per Haiku RULE 6–8.

  _Deliverable:_ `sections/A3/symbol_floor.tex` now provides Lemma~\ref{lem:a3-lipschitz-bound}, Lemma~\ref{lem:a3-core-lower-bound}, Lemma~\ref{lem:a3-arch-floor} and Corollary~\ref{cor:a3-arch-floor-compact}, giving analytic expressions for $L_A(B,t_{\mathrm{sym}})$ and $c_{\mathrm{arch}}(K)$. References: Stein–Shakarchi~\cite[Ch.~2]{SteinShakarchi2003}, Zygmund~\cite[Ch.~I]{Zygmund2002}, NIST DLMF~\cite[§5.2]{NISTDLMF}, Böttcher–Silbermann~\cite[Ch.~5]{BoettcherSilbermann2006}. No tables or JSON inputs remain in this step.

Phase 3: Brick A3.3 — Fejér×Heat Modulus Control (≈6h)
  3.1 [x] Analyze Fejér kernel bounds (Stein & Shakarchi Ch.2).
  3.2 [x] Add heat kernel smoothing estimates (A3_calibration_kappa.tex).
  3.3 [x] Combine to obtain ω_{P_A}(π/M) analytically (Lemma A3.3a).
  3.4 [x] Deduce Lipschitz constant for discretization (Lemma A3.3b).
  3.5 [x] Audit: ensure no reliance on JSON/ATP, constants explicit.

  _Deliverable:_ `sections/A3/fejer_modulus.tex` (Lemma~\ref{lem:a3-fejer-uniform}, Lemma~\ref{lem:a3-fejer-lip}, Corollary~\ref{cor:a3-omega-fejer}) provides analytic bounds for the Fejér×heat smoothing, giving explicit dependence on $(M,t_{\mathrm{sym}})$ and verifying the modulus used in Theorem~\ref{thm:A3}. References: Stein--Shakarchi~\cite[Ch.~2]{SteinShakarchi2003}.

Phase 4: Brick A3.4 & A3.5 — Synthesis (≈6h, next stage)
  - [x] Gershgorin / matrix bounds (Horn & Johnson) on $T_M[P_A]$ (see `sections/A3/matrix_guard.tex`, Lemma~\ref{lem:hw-kf}).
  - [x] Mixed bridge inequality with analytic constants (Theorem~\ref{thm:a3-mixed-margin} in `sections/A3/matrix_guard.tex`).
  - [x] Link to RKHS/IND via Proposition~\ref{prop:a3-prime-cap}, Remark~\ref{rem:a3-ind-bridge}, and the Frobenius guard (legacy tables moved to Appendix~\ref{app:a3-repro}).
  - [x] Final audit, integrate into sections/A3/main.tex and lock checklist (latexmk build clean).

Success Criteria
  • All constants derived analytically.
  • No `\input{param_tables}` or cert references in main text.
  • Lemmas/Theorems have complete proofs & citations.
  • Section A3 passes Haiku audit RULES 1–10.

Logbook
  [x] Phase 0 start:
  [x] Phase 0 done:
  [x] Phase 1 progress:
  [x] Phase 2 progress:
  [x] Phase 3 progress:
  [x] Phase 4 start: matrix guard + mixed bridge entered (`sections/A3/matrix_guard.tex`), RKHS cap derived analytically (no direct JSON references).
  [x] Phase 4 done: `make -C Q3_paper pdf` passes, Theorem~\ref{thm:A3} restated with analytic inputs; legacy data parked in Appendix~\ref{app:a3-repro}.
