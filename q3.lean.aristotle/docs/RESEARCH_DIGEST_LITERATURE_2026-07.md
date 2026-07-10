# RESEARCH DIGEST — Literature for the Weil-Positivity / Prolate RH Paper
(Landau–Gonek · PSWF edge machinery · Weil-positivity status 2024–26 · venues & AI policy)

STATUS: **READ-ONLY FOR CODEX.** Read, cite, import — **do not edit.**
Corrections go through Mythos review only. sha256 pinned in ROUTE_B_STATE.md.
Provenance: deep literature run by Mythos, 2026-07-07. All arXiv IDs / DOIs
verified against arXiv/publisher pages unless explicitly marked UNVERIFIED.
Classification legend: THEOREM (unconditional) · CONDITIONAL(on X) ·
CONJECTURE/HEURISTIC. Every import into a gate or the paper must quote its
classification line verbatim (K7).

---

## EPISTEMIC FIREWALL — READ FIRST (hard rules for all gates and pen work)

1. **The discrete second moment over zeros is CONDITIONAL ON RH.**
   Bui–Florea–Milinovich (arXiv:2310.03949, Thm 3.1): for x>=2, T>1,
   sum_{0<gamma<=T} |sum_{n<=x} a_n n^{-rho}|^2
     = N(T) * sum_{n<=x} |a_n|^2/n
       - (T/pi) * Re( sum_{kn<=x} conj(a_{kn}) a_n Lambda(k)/(kn) )
       + O( x (log xT)^2 * sum |a_n|^2/n ),   rho = 1/2 + i*gamma.
   The identity |A(1/2+i*gamma)|^2 = A(rho)A(1-rho) NEEDS 1-rho = conj(rho),
   i.e. RH. Therefore: this theorem may CALIBRATE and CROSS-CHECK, it may
   NEVER stand inside the positivity chain that concludes RH (K5 circularity).
   Unconditional substitutes: Gonek's uniform Landau formula (item 1.2) and
   the twisted moment (item 1.4).
2. **In-house obligations (no off-the-shelf citation exists — negative
   searches confirmed):**
   - SmoothRemainderTail lemma: Poisson/Euler–Maclaurin for
     E(f)(u) = u^{1/2} sum_{m>=1} f(mu) with error bounded by out-of-band
     mass. Must be proven in the paper.
   - The lambda^11 edge-amplitude prefactor: program-specific; derive
     explicitly. Exponential factor exp(-4*pi*lambda^2) is consistent with
     plunge-region super-exponential decay (Bonami–Karoui, Kulikov), but the
     polynomial prefactor is ours to establish.
   - Re-verify the Bonami–Karoui identity d/dc log(lambda_n) =
     2*psi_{n,c}(1)^2/c VERBATIM before submission. In-session check pointed
     to arXiv:1012.3881 eq. (43); the independent research pass could not
     re-confirm the exact equation number/normalization. FLAG: check both
     arXiv:1509.02646 and 1405.3676 directly.
   - No fully explicit-constant version of Gonek's bare sum x^rho formula
     was located; if effective constants are needed for the jump comb,
     derive them (Cully-Hugill–Johnston covers x^rho/rho sums only).
3. **Citation hazards (both resolved, do not reintroduce):**
   - arXiv:2603.07407 ("Sharp estimates ... BEFORE the plunge region") and
     arXiv:2603.23832 (Kulikov–Larsen, "... with applications to area laws")
     are DISTINCT real papers. For our pre-plunge edge regime cite 2603.07407.
   - NEVER attach DOI 10.1007/978-3-319-32162-2_5 to Connes arXiv:2602.04022.
     That DOI is a 2016 Springer essay; the 2026 paper is arXiv-only so far.

---

## DIRECTION 1 — Landau/Gonek formulas and discrete mean values over zeros

1.1 Landau (1911), fixed x>1:
    sum_{0<gamma<=T} x^rho = -(T/2pi) Lambda(x) + O_x(log T).
    E. Landau, Math. Ann. 71 (1911), 548-564. THEOREM. VERIFIED. Baseline.

1.2 **Gonek's uniform Landau formula (THE unconditional engine).**
    Uniformly for x, T > 1:
    sum_{0<gamma<=T} x^rho = -(T/2pi) Lambda(x)
      + O( x log(2xT) loglog(3x) )
      + O( log x * min(T, x/<x>) )
      + O( log(2T) * min(T, 1/log x) ),
    where <x> = distance from x to the nearest prime power (other than x
    itself). i*gamma-form: divide main term by sqrt(x); error
    E(x,T) << sqrt(x) log(xT) loglog(3x) + (log x/sqrt(x)) min(T, x/<x>)
            + (log T/sqrt(x)) min(T, 1/log x).
    S. M. Gonek, Invent. Math. 75 (1984), 123-141, DOI 10.1007/BF01388565;
    and Contemp. Math. 143 (1993), 395-413.
    THEOREM (unconditional). VERIFIED (quoted verbatim in arXiv:2310.03949
    Lemma 3.2; arXiv:2007.10533 eq. (27); arXiv:0806.0786 Lemma 4.1).
    -> Pipeline: off-diagonal incoherence engine for the jump comb over zeros.

1.3 Discrete second moment of Dirichlet polynomials over zeros:
    see EPISTEMIC FIREWALL item 1. CONDITIONAL(on RH). VERIFIED.
    Useful range: error beats main term only for x <~ T/log T; mollifier
    literature uses length T^theta with theta < 1/2 (later < 4/7).
    Shifted two-length variant: Cicek, arXiv:2007.10533, Lemma 3.1/eq.(29).
    -> Pipeline: the a_1 = 2 sum_j |K(gamma_j)|^2 mechanism — diagonal
       N(T) sum|a_n|^2/n + von Mangoldt off-diagonal. RH-conditional; use
       only as calibration/cross-check, never in the concluding chain.

1.4 NEGATIVE SEARCH + unconditional substitute. No unconditional
    sum |A(rho)|^2 with N = T^theta exists; the obstruction
    (need 1-rho = conj(rho)) is structural. Unconditional twisted sum:
    sum_{0<gamma<=T} zeta^(mu)(rho) zeta^(nu)(1-rho)
      = (T/2pi) P_{mu,nu}(log(T/2pi)) + O(T exp(-C sqrt(log T))),
    P explicit of degree mu+nu+2; error O(T^{1/2+eps}) under RH.
    Durkan–Hughes–Pearce-Crump, arXiv:2601.06292, Thm 1.
    THEOREM (unconditional, twisted form). VERIFIED. Jan-2026 preprint:
    treat exact error constants as preprint-stage.

1.5 Gonek 1984 under RH: sum_{0<gamma<=T} |zeta'(rho)|^2
      = (1/24pi) T (log(T/2pi))^4 + O(T (log T)^3).
    CONDITIONAL(on RH). VERIFIED.

1.6 Simple zeros. Conrey–Ghosh–Gonek, Proc. LMS (3) 76 (1998), 497-522:
    >= 19/27 (~70.37%) of zeros simple, >= 84.57% distinct, under RH + GLH.
    Bui & Heath-Brown, arXiv:1302.5018: GLH removed — 19/27 simple under
    RH ONLY. CONDITIONAL(on RH). VERIFIED.

1.7 Aryan, J. Number Theory 233 (2022), 389-404; arXiv:1902.05473:
    unconditional pair-correlation consequences of Landau–Gonek; two-thirds
    simple under a zero-density hypothesis weaker than RH.
    THEOREM (pair-correlation part) / CONDITIONAL(zero-density) for the
    simplicity corollary. VERIFIED.

1.8 Durkan–Hughes–Pearce-Crump, arXiv:2601.18025 (distinct from 2601.06292):
    generalisations of Landau–Gonek for sum chi(rho) X^rho, regimes X<T,
    X ~ T, X>T; new proof of Shanks' conjecture. THEOREM (unconditional).
    VERIFIED. Jan-2026 preprint caveat.

1.9 Explicit-constant explicit formulas (for the x^rho/rho counting sums,
    NOT bare x^rho): Cully-Hugill & Johnston, Int. J. Number Theory 19(6)
    (2023), 1205-1228, arXiv:2111.10001: for max{51, log x} < T <
    (x^alpha - 2)/2, psi(x) = x - sum_{|gamma|<=T} x^rho/rho +
    O*(M x log x / T); admissible triples include (40, 1/2, 5.03) and
    (10^3, 1/100, 0.5597). Sequel arXiv:2402.04272 gives explicit O(x/T).
    THEOREM (explicit constants). VERIFIED.

## DIRECTION 2 — Prolate spheroidal machinery

2.1 Fuchs (1964), fixed n, c -> infinity: 1 - lambda_n(c) decays at an
    optimal exponential rate. J. Math. Anal. Appl. 9 (1964), 317-330.
    THEOREM. VERIFIED (as quoted in Bonami–Jaming–Karoui arXiv:1804.01257).

2.2 Widom (1964), fixed c, n -> infinity:
    lambda_n(c) ~ ((e pi c)/(8n+4))^{2n+1}. THEOREM. VERIFIED
    (quoted in Kulikov arXiv:2306.12430).

2.3 Bonami–Karoui:
    (i)  C. R. Acad. Sci. Paris 352 (2014), 229-234,
         DOI 10.1016/j.crma.2014.01.004 — bounds for psi_{n,c}(1), uniform
         eigenvalue decay.
    (ii) Constr. Approx. 43(1) (2016), 15-45; arXiv:1405.3676 — explicit
         psi_{n,c}(1) via complete elliptic integrals; Liouville normal
         form + Olver bounds; restricted to q = c^2/chi_n(c) < 1.
    (iii) Appl. Comput. Harmon. Anal. 42 (2017), 1-20; arXiv:1509.02646 —
         explicit integral approximation of lambda_n(c) from the plunge
         region; precise super-exponential decay.
    All THEOREM. VERIFIED. The d/dc log(lambda_n) identity: see FIREWALL 2.
    -> Pipeline: edge-amplitude class (exp factor consistent; lambda^11
       prefactor OURS to derive).

2.4 Kulikov, Appl. Comput. Harmon. Anal. 71 (2024), Paper 101639;
    arXiv:2306.12430: lambda_n(c) > 1 - delta^c for n = [(1-eps)c], any
    eps>0 (Bargmann-transform proof; improves BJK eps >= 0.42).
    THEOREM. VERIFIED.

2.5 2026 sharp estimates — two distinct papers:
    - arXiv:2603.07407, "Sharp estimates for eigenvalues of localization
      operators BEFORE the plunge region": asymptotics of 1-lambda_n(c)
      for n < c. Most relevant to our edge regime. VERIFIED to exist;
      pull exact theorem numbers directly before citing.
    - arXiv:2603.23832 (Kulikov & Larsen), "...with applications to area
      laws": sharp counting-function bounds in the plunge. THEOREM. VERIFIED.

2.6 NEGATIVE SEARCH: no canonical theorem for Mellin/Poisson tails of
    E(f)(u) = u^{1/2} sum f(mu) with f a zero-integral PSWF combination.
    SmoothRemainderTail is original to our paper. Nearest infrastructure:
    Connes–Consani Selecta 2021 (Sonin-space analysis).

## DIRECTION 3 — Weil positivity and explicit-formula status 2024–2026

3.1 Weil's criterion (modern operator form): RH (for all Grossencharakter
    L-functions of K) <=> Tr theta(f * f^sharp) >= 0 on the convolution
    algebra; may restrict to compactly supported g with integral g dx = 0
    and integral g d*x = 0. A. Weil, Comm. Sem. Math. Univ. Lund (1952);
    Connes, Selecta Math. (N.S.) 5 (1999), 29-106. THEOREM (equivalence).
    VERIFIED. -> This equivalence IS the alpha-Gate.

3.2 Yoshida: RH <=> positive definiteness of Q_W; positivity proven for
    sufficiently small support + nondegeneracy criterion. H. Yoshida,
    Adv. Stud. Pure Math. 21 (1992), 281-325. THEOREM (small support).
    VERIFIED.

3.3 Bombieri, Atti Accad. Naz. Lincei 11 (2000), 183-233: Q_W psd <=> RH;
    minimum attained in the unit ball of L^2[-t,t]; if RH fails with
    finitely many off-line zeros, #negative eigenvalues of the truncation
    = half the number of off-line zeros (large truncation). THEOREM.
    VERIFIED. -> Structural basis of the ZEO detector narrative.

3.4 Connes–Consani, Selecta Math. 27 (2021), Paper 77,
    DOI 10.1007/s00029-021-00689-4; arXiv:2006.13771: conceptual Weil
    positivity at the archimedean place via semi-local trace formula;
    W_infty(g * g^adj) >= Tr(theta(g) S theta(g)^adj); strengthens Yoshida.
    THEOREM. VERIFIED.

3.5 Connes–Consani–Moscovici, Ann. Funct. Anal. 15 (2024), Paper 87;
    arXiv:2310.18423: semilocal prolate wave operator; negative part
    (Sonin space) reproduces squares of zeta zeros in the UV. THEOREM +
    conceptual. VERIFIED.

3.6 **Connes–van Suijlekom, Commun. Math. Phys. 406 (2025), Paper 312,
    DOI 10.1007/s00220-025-05493-1; arXiv:2511.23257, Theorem 6.1:**
    for a real distribution D on [0,L] with even extension, if the kernel
    tilde-D(x-y) defines a lower-bounded self-adjoint operator on
    L^2([-L/2, L/2]) whose lowest spectral value is a simple isolated
    eigenvalue with even eigenfunction xi, then ALL zeros of hat-xi lie on
    the real line. Step (1): C*-algebraic Caratheodory–Fejer (1911).
    THEOREM (unconditional, finite-cutoff criticality). VERIFIED.
    -> The finite-c half of the alpha-Gate. The c->infinity half is OPEN.

3.7 CCM "Zeta Spectral Triples", arXiv:2511.22755: D_log^{(lambda,N)} as
    rank-one perturbations; spectra match lowest zeros with striking
    accuracy for small x = lambda^2; **convergence as x->infinity OPEN**
    (their Section 8). Finite-x criticality THEOREM via 3.6; convergence
    CONJECTURE/HEURISTIC. VERIFIED.

3.8 Connes, arXiv:2602.04022 (3 Feb 2026), "The Riemann Hypothesis: Past,
    Present and a Letter Through Time": extremization of restricted Weil
    form; primes < 13 give first 50 zeros to accuracies 2.6e-55 .. 1e-3;
    approximants exactly on the critical line; semilocal Weil positivity
    <=> RH; Section 6.4 heuristic asymptotic for the lowest eigenvalue.
    Survey + THEOREM (criticality of approximants) + HEURISTIC
    (convergence, 6.4). VERIFIED. DOI hazard: see FIREWALL 3.

3.9 Groskin, arXiv:2605.20224 (v2, 26 Jun 2026): first independent public
    implementation of the CvS Galerkin matrix, cutoffs c = 13..67 and 100;
    first-zero error shrinks monotonically ~2e-55 -> ~1.5e-168 across
    c = 13..67 at N = 100 (113 orders of magnitude); smallest even-sector
    eigenvalue ~1e-334 at c = 100, N = 250; gamma_1..gamma_10 recovered to
    307-329 digits; Aitken-Delta^2 extrapolation log10|lambda_inf^even| ~
    -536.8 / -533.7 approaching the Connes 6.4 target ~ -530.4.
    COMPUTATIONAL (no new unconditional theorem); convergence explicitly
    OPEN; self-described hypothesis-status caveat. VERIFIED.
    -> Precedent + external calibration for our certified-numerics track;
       CvS q_{m,n} unitarily equivalent to CCM tau_{i,j} (CCM Lemma 5.1).

3.10 Suzuki, arXiv:2606.09096 (8 Jun 2026): Weil's quadratic form via the
    screw function; unifies Yoshida/Bombieri/CC/CCM; conjecture: the
    self-adjoint operator with eigenvalues = imaginary parts of zeros as
    a->infinity limit of nonlocal realizations on [-a,a]. Framework:
    Suzuki, J. London Math. Soc. (2023), DOI 10.1112/jlms.12785;
    arXiv:2206.03682 (Thm 1.4: RH <=> nondegeneracy of the Hermitian form
    for every 0 < a < infinity). THEOREM (partial, unconditional) +
    CONJECTURE (limit operator). VERIFIED.

## DIRECTION 4 — Publication venues and AI-disclosure policy (2024–2026)

4.1 Venue map for this class of work:
    Selecta Math. (Connes–Consani 2021; Connes 1999); Commun. Math. Phys.
    (Connes–van Suijlekom 2025); Ann. Funct. Anal. (CCM 2024); Invent.
    Math. (Gonek 1984); J. Number Theory (Aryan 2022; Bombieri–Lagarias
    1999); J./Bull. LMS (Suzuki 2023; Bui 2024); Int. J. Number Theory /
    Math. Comp. (explicit-constant and computational work; Brent–Platt–
    Trudgian, Math. Comp. 90 (2021), 2923-2935). Norm: theorem-first for
    analytic cores; computation-first only for explicitly numerical papers.

4.2 AI-assisted mathematics disclosure (consensus across COPE, Elsevier,
    Springer Nature, Wiley, T&F, SAGE, ACM, IEEE, LMS, ICMJE):
    - AI cannot be an author. Universal.
    - Human author bears full responsibility for every proof and citation.
    - Substantive AI use MUST be disclosed (Methods or Acknowledgements);
      routine language polishing generally exempt.
    - Elsevier: separate AI-declaration template. Wiley/Science: name the
      software, provider, sometimes prompts. Springer Nature: Methods
      documentation; copy-editing exempt. LMS: explicit journal policy
      permitting responsible disclosed use (lms.ac.uk/publications/policies/AI).
    - UNVERIFIED: no proof-specific AI policy located for Annals /
      Inventiones / JAMS beyond general publisher stance — disclose
      conservatively.
    - Lean/machine-verified components: no uniform rule; deposit the
      formalization with a citable DOI, disclose separately from LLM use.

4.3 Recommended architecture: SPLIT.
    Paper A (theorem-first; Selecta / CMP / JNT class): unconditional
    analytic lemma package (Gonek-engine application, PSWF edge bounds,
    SmoothRemainderTail) + conditional equivalence theorem (alpha-Gate:
    positivity <=> RH, citing Weil/Yoshida/Connes–Consani) + precise
    statement of what remains open.
    Paper B (computational companion; Exp. Math. / Math. Comp.): certified
    high-precision verification, reproducible arbitrary-precision code,
    interval certificates, external cross-validation vs Groskin/CCM.
    Separate methodology paper (later, per Ылша): full multi-agent
    pipeline disclosure.

## FIVE-STAGE ACTION PLAN (from the research pass)

Stage 1 — Epistemic firewall in the manuscript: quarantine every
RH-conditional import (above all item 1.3). Restructure the
a_1 = 2 sum |K(gamma_j)|^2 usage to rely only on unconditional tools where
it feeds the concluding chain.
Stage 2 — Prove the two uncited derivations in-house: SmoothRemainderTail;
lambda^11 prefactor (+ verbatim BK identity re-check).
Stage 3 — Frame the headline claim precisely against the OPEN c->infinity
convergence problem (Connes 2026 / CCM / Groskin / Suzuki all state it
open); use CvS Thm 6.1 as the unconditional finite-c anchor.
Stage 4 — Pre-submission verification: BK identity verbatim;
2603.07407 exact theorem numbers; never the 2016 DOI on Connes 2026;
exact page numbers Gonek Contemp. Math. 143 and CGG Proc. LMS 76.
Stage 5 — Split publication per 4.3 + AI-methods disclosure naming the
pipeline roles + deposit Lean/interval artifacts with DOIs.

## CAVEATS

- Conditional-vs-unconditional is the dominant risk (see FIREWALL 1).
- Preprint freshness: 2605.20224, 2606.09096, 2601.06292, 2601.18025,
  2603.23832, 2603.07407 are recent preprints; re-check constants and
  theorem numbers at submission time.
- Program-specific quantities with no external citation: lambda^11
  prefactor; the exact d/dc log(lambda_n) normalization;
  SmoothRemainderTail.
- Numerical accuracy is evidence, never proof: Groskin's 113-307-digit
  agreements and Connes's 2.6e-55 do not close the c->infinity gap, by
  the authors' own statements.
