# REFERENCES — Q3 / Route B literature index

Master index of every external publication we USE. Rule: whenever a lemma, theorem,
gap, or verdict cites a source, add/append a row here with WHAT it is used for. This
is the citation ledger for the eventual publication (chain-of-evidence: every citation
claim must trace to a real source in `pdfs/`, per the CoE discipline we adopted).

Access legend: OA = open access (in `pdfs/`); PAYWALL = needs owner's Uni proxy →
owner fetches and drops the PDF in `pdfs/`, then we flip it to HAVE; SCAN = image PDF
(needs OCR); BOOK = physical/library.

## Sources used so far

| Key | Bibliographic identity | DOI / URL | Local PDF | Access | USED FOR (gap / lemma / theorem) |
|---|---|---|---|---|---|
| CCM-ZST-2025 | Connes, Consani, Moscovici, "Zeta Spectral Triples" | arXiv:2511.22755 | `pdfs/2511.22755.pdf` | OA ✓ | **Thm 5.10** = H2b real-zero bridge (`FiniteQWTheorem510RealZeroBridge`); **§8 missing steps** = H2a `SIMPLE_EVEN(QW_λ)` + C3-B `GroundStateToTrialSameFamilyBridge`; **Lemma 7.2** λ⁻² rate; **Lemma 7.3** trial→Ξ = C3-A (PAPER_PROVED) |
| CCM-ZZPWO-2023 | Connes, Consani, Moscovici, "Zeta Zeros and Prolate Wave Operators — Semilocal Adelic Operators" | arXiv:2310.18423 | `pdfs/2310.18423.pdf` | OA ✓ | whole-line prolate operator `W_λ = −S²+2πλ²(4N+1)−1/4` definition; grading N; even Hermite modes (context for H2a / prolate layer) |
| BK-PSWF-2016 | Bonami, Karoui, "Uniform approximation and explicit estimates for the prolate spheroidal wave functions", Constr. Approx. 43 (2016) 329–371 | arXiv:1405.3676 | `pdfs/1405.3676.pdf` | OA ✓ | **PSWF SL operator** `L_c`, orthonormal basis L²[-1,1], **simplicity**, **parity (-1)ⁿ**, **n zeros**, **commutation** with `Q_c` — PSWF dossier items 1,2,3,5,6,7,9 |
| PSWF-REVIEW-2024 | (review) "Prolate Spheroidal Wave Functions and the Accuracy and Dimensionality of Spectral Analysis" | arXiv:2409.16584 | `pdfs/2409.16584.pdf` | OA ✓ | secondary review (pointer; μ_n/λ_n structure) |
| SP-PSWF-I-1961 | Slepian, Pollak, "Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty — I", Bell Syst. Tech. J. 40 (1961) 43–63 | archive.org/details/bstj40-1-43 | `pdfs/bstj40-1-43_text.pdf` | HAVE ✓ (OCR) | **finite-Fourier commutation** (dossier item 9, ORIGINAL); **nonzero eigenvalues** — VERIFIED verbatim: eq (26)–(28), λ_n(c)=(2π/c)[R⁽¹⟩_{0n}(c,1)]², "kernel positive definite (Bochner) ⇒ quantities STRICTLY POSITIVE" + §VI "degeneracy does not occur" (simple). Item 10 CLOSED |
| OSIPOV-TR1450-2012 | Osipov, "Explicit upper bounds on the eigenvalues associated with prolate spheroidal wave functions", Yale YALEU/DCS/TR-1450 (2012) | engineering.yale.edu TR1450 | `pdfs/TR1450.pdf` | HAVE ✓ | ORX-lineage rigorous PSWF: SL eigenvalue theory + eigenvalue-decay bounds; substitutes for ORX book on dossier items 3,5 (numbered theorems) |
| ORX-PSWF0-2013 | Osipov, Rokhlin, Xiao, "Prolate Spheroidal Wave Functions of Order Zero", Springer AMS 187 (2013) | doi:10.1007/978-1-4614-8259-8 | — | BOOK (pointer) | canonical monograph; the statements are already covered by BK-PSWF-2016 + OSIPOV-TR1450-2012 |
| MS-MFSF-1954 | Meixner, Schäfke, "Mathieusche Funktionen und Sphäroidfunktionen", Springer 1954 (ISBN 978-3-662-00941-3) | — | `pdfs/978-3-662-00941-3.pdf` | HAVE ✓ (OCR, DE) | **§3.2 Satz 9** uniform eigenfunction estimate = dossier item 11 normalization + λ⁻² rate feeding C3 (exact Satz page-locate pending deep pass) |
| FLAMMER-1957 | Flammer, "Spheroidal Wave Functions", Stanford UP 1957 | — | — | BOOK 🔴 | spheroidal ODE, eigenvalue indexing, parity (pointer) |
| FUCHS-1964 | Fuchs, "On the eigenvalues of an integral equation arising in the theory of band-limited signals", J. Math. Anal. Appl. 9 (1964) 317–330 | doi:10.1016/0022-247X(64)90056-0 | — | PAYWALL 🔴 | eigenvalue asymptotics / nonvanishing (dossier item 10 support) |
| SIMON-MOMENT-1998 | Simon, "The classical moment problem as a self-adjoint finite difference operator", Adv. Math. 137 (1998) 82–203 | doi:10.1006/aima.1998.1728 | — | PAYWALL 🔴 | Jacobi-matrix self-adjointness (whole-line prolate realization) |
| MATHLIB-2019 | The mathlib Community, "The Lean mathematical library", CPP 2020 | arXiv:1910.09336 | — | OA (cite-only) | Lean/Mathlib API for every formalized theorem (T4a, PL1/PL2, suppliers) |

| CVS-QFRZ-2025 | Connes, van Suijlekom, "Quadratic Forms, Real Zeros and Echoes of the Spectral Action", Commun. Math. Phys. 406:12 (2025) | arXiv:2511.23257 | `pdfs/2511.23257.pdf` | HAVE ✓ | **THE H2b ENGINE (Theorem 6.1 / its main theorem)**: simple+even lowest eigenvalue ⇒ all zeros of the Fourier transform of ξ lie on the real (critical) line. PROOF via **Carathéodory–Fejér 1911 Toeplitz structure theorem** (Hermitian PSD Toeplitz rank n−1 + kernel vector ⇒ polynomial zeros on unit circle) — DIRECTLY Q3's Toeplitz/MatrixBridge/Szegő-Böttcher infrastructure. Both Connes-2026 and Groskin CITE this for H2b; neither reproves it. Candidate for FORMALIZATION. |

## Deep usage cards (per-theorem, verbatim, sub-agent extracted)

- `CCM_ZST_USAGE_CARDS.md` — CCM-ZST-2025 (2511.22755): Thm 5.10, Thm 3.6, Lemma 7.2,
  Lemma 7.3, §8 missing steps, prolate operator W_λ + trial k_λ — all 6 verbatim.
- `CONNES_RH2026_USAGE_CARDS.md` — CONNES-RH-2026 (2602.04022): 6 cards. NET (two-agent
  convergent): **H2a `SIMPLE_EVEN(QW_λ)` = OPEN** (Connes' "remaining step" §6.6 p.30;
  proved only for prolate PW_λ, Fact 6.3); **H2b = PROVED CONDITIONALLY** (Theorem 6.1
  via CVS-QFRZ-2025, conditional on H2a); **C3-B convergence c→∞ = OPEN** (Connes p.25
  "not proved"; only trial k_λ→Ξ proved, Fact 6.4; 2.6e-55 numerics = evidence only).
- `CVS_H2B_FORMALIZATION_BRIDGE.md` — CVS-QFRZ-2025 (2511.23257) → Q3 Lean bridge.
  KEY: CvS proves the CF corollary TWO ways — C*-algebraic (§2) and FINITE real-spectral
  (§5); **Q3 mirrors the §5 route, bypassing the C*-algebra**. Bridge tally over ~9 steps:
  HAVE=5 (rankOneCorrection_weightedSymmetric, _kills_vector, det_rankOneCorrection_* ×2,
  negative controls), PARTIAL=5, MISSING=5. **Keystone gap M1**: "self-adjoint w.r.t. a
  PosDef form Q ⇒ real spectrum" (congruence Q=SᵀS) — welds `weightedSymmetric` to
  `HermitianDeterminantRealZeros`. Then M2 (degenerate quotient + induced PosDef metric,
  where H2a is consumed), M3 (Lagrange/eq-18), M4 (Fourier/Hurwitz, infinite-dim Thm 6.1).
  Carathéodory–Fejér NOT in Mathlib, but NOT needed (§5 route); all primitives present
  (Matrix.PosDef, IsHermitian.spectrum, matrix-determinant lemma, Vandermonde, Lagrange).
  VERDICT: H2b finite-matrix layer FORMALIZABLE by extending the existing scaffold
  (M1→M2→M3, M4 separate); stays conditional on H2a (OPEN).
- `GROSKIN_TWF_USAGE_CARDS.md` — GROSKIN-TWF-2026 (2605.20224): 6 cards. Groskin proves
  NOTHING himself (§10) — experimental math; every theorem cited from CVS [9] or CCM.
  Truncated Weil form §2.1 eq(1)-(2) on L²([0,L]), L=log c, D=D_∞+D_pole+D_prime;
  exact archimedean multiplier h_+(τ) = −log π + Re Ψ(1/4+iτ/2) (useful for STEP34/A_arch);
  H2b cited from CVS Thm 6.1; C3-B open conjecture (numerics two-way ambiguous);
  STEP34 P_prime ⪯ A_arch NOT FOUND (only the arch+pole+prime decomposition).

## Newly acquired (2026-08-03 pass)

| Key | Bibliographic identity | DOI / URL | Local PDF | Access | USED FOR |
|---|---|---|---|---|---|
| CONNES-RH-2026 | A. Connes, "The Riemann Hypothesis: Past, Present and a Letter Through Time" | arXiv:2602.04022 (Feb 2026) | `pdfs/2602.04022.pdf` | HAVE ✓ | fresh primary Connes RH survey — likely updated statements of the QW/prolate program (H2a `SIMPLE_EVEN`, C3 trial→ground); FLAG for subagent extraction |
| COHN-ELKIES-2003 | Cohn, Elkies, "New upper bounds on sphere packings I", Ann. of Math. 157 (2003) 689–714 | arXiv:math/0110009 | `pdfs/math0110009.pdf` | HAVE ✓ | Astra Block A `WeilFourierSignDualCertificate` — primal/dual sign-constrained Fourier LP pattern (the representation-shift candidate for the PSD-pd / Step 34 wall) |
| SCIENTISTONE-2026 | Meng et al., "ScientistOne: Towards Human-Level Autonomous Research via Chain-of-Evidence" | arXiv:2605.26340 | (orig `/mnt/hdd01/Paper_to_read/`) | pointer | METHODOLOGY — the CoE (chain-of-evidence) discipline this litreview system implements; not a math source |
| GROSKIN-TWF-2026 | A. Groskin, "High-Precision Approximation of Riemann Zeros via the Truncated Weil Form" | arXiv:2605.20224 (v2, Jun 2026) | `pdfs/2605.20224.pdf` | HAVE ✓ | **DIRECTLY our object**: truncated Weil form on L²([0,log c]), even-sector ground state with Fourier–Mellin zeros on the critical line, c→∞ convergence question = **C3-B**; uses Fuchs prolate eigenvalue theorem. FLAG subagent |
| GROSKIN-GWD-2026 | A. Groskin, "A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form" | arXiv:2607.02828 (Jul 2026) | `pdfs/2607.02828.pdf` | HAVE ✓ | **Arch−prime / Step 34 wall**: finite Guinand–Weil dictionary + archimedean tail order — the exact `P_prime ⪯ A_arch` structure + Astra Block A dual territory. FLAG subagent |
| CC-WEILPOS-2020 | Connes, Consani, "Weil positivity and Trace formula: the archimedean place" | arXiv:2006.13771 (2020) | `pdfs/2006.13771.pdf` | HAVE ✓ | foundational Archimedean side of `A_arch` (Weil positivity at the archimedean place) |

## TO FETCH — status

- ✅ ORX residual → covered by OSIPOV-TR1450-2012 (owner fetched Yale TR-1450).
- ✅ MS-MFSF-1954 → owner fetched (pdfs/978-3-662-00941-3.pdf); Satz 9 page-locate = deep pass.
- ✅ SP-PSWF-I-1961 → owner fetched OCR scan; item 10 already VERIFIED verbatim.
- FUCHS-1964, SIMON-1998 — secondary, low priority (statements already covered).

All three PSWF-dossier residual pins are now CLOSED at the source level (files in `pdfs/`).

## Part 2 — acquired from Mythos enumeration (2026-08-03)

NOTE (Mythos corrections applied): 2605.20224 / 2607.02828 = Akiva GROSKIN (already
indexed as GROSKIN-*, correct). CvS 2511.23257 (Mythos №19) was ALREADY acquired the
prior pass → HAVE (row CVS-QFRZ-2025 above), not MISSING. Kulikov = Aleksei Kulikov
(the "Russian mathematician"). 2403.01247 actual title corrected below.

| Key | Bibliographic identity | ID | Local PDF | Access | USED FOR |
|---|---|---|---|---|---|
| SUZUKI-SCREW-2026 | Suzuki, "Weil's Quadratic Form via the Screw Function" | arXiv:2606.09096 (Jun 2026) | `pdfs/2606.09096.pdf` | HAVE ✓ | unified Yoshida/Bombieri/CC/CCM frame via screw function; nonlocal operators on [−a,a] limit — ROOF / canonical strip slots |
| CC-ZETACYCLES-2021 | Connes, Consani, "Spectral Triples and ζ-Cycles" | arXiv:2106.01715 (2021) | `pdfs/2106.01715.pdf` | HAVE ✓ | semilocal QW = QW⁺⊕QW⁻ split, η_n basis, positivity windows L∈[log2,log3) — our EVEN SECTOR |
| CCM-QSERIES-2024 | Connes, Consani, Moscovici, "On q-series and the moment problem associated to local factors" | arXiv:2403.01247 (2024) | `pdfs/2403.01247.pdf` | HAVE ✓ | moment-problem / Jacobi realization of the semilocal operator (CMV/Cayley context) |
| SUZUKI-CANONSYS-2012 | Suzuki, canonical system with E_h(z)=ξ(1/2+h−iz) | arXiv:1204.1827 (2012) | `pdfs/1204.1827.pdf` | HAVE ✓ | de Branges / canonical systems — D0.7e audit, canonical strip slots |
| CONNES-TRACE-1999 | Connes, "Trace formula in NCG and the zeros of ζ", Selecta 5 (1999) 29–106 | arXiv:math/9811068 | `pdfs/math_9811068.pdf` | HAVE ✓ | operator form of the Weil criterion (α-Gate equivalence) |
| KULIKOV-PLUNGE-2026 | A. Kulikov, "Sharp estimates for eigenvalues of localization operators before the plunge region" | arXiv:2603.07407 (Mar 2026) | `pdfs/2603.07407.pdf` | HAVE ✓ | −log(1−λ_n(c)) ≍ (c−n)/log(2c/(c−n)) up to plunge — our edge-tail regime |
| KULIKOV-LARSEN-2026 | Kulikov, Larsen, "Sharp estimates … with applications to area laws" | arXiv:2603.23832 (Mar 2026) | `pdfs/2603.23832.pdf` | HAVE ✓ | plunge counting function + trace estimates — two-level spectral ladder |
| KULIKOV-PREPLUNGE-2024 | Kulikov, pre-plunge eigenvalue bound, ACHA 71 (2024) 101639 | arXiv:2306.12430 | `pdfs/2306.12430.pdf` | HAVE ✓ | λ_n(c) > 1−δ^c at n=[(1−ε)c] (improves BJK) |
| BK-DECAY-2010 | Bonami, Karoui, spectral decay of the sinc operator | arXiv:1012.3881 (2010) | `pdfs/1012.3881.pdf` | HAVE ✓ | sinc-operator spectral decay |
| BK-ENDPOINT-2015 | Bonami, Karoui, "Spectral decay of the time-and-frequency limiting operator" | arXiv:1509.02646 (2015) | `pdfs/1509.02646.pdf` | HAVE ✓ | d/dc log λ_n = 2ψ_n(1)²/c endpoint identity — candidate "eq(43)" |
| KIM-NUMREAL-2026 | Kim et al. (VIDRAFT), "A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator…" | arXiv:2607.24830 (math.GM, Jul 2026) | `pdfs/2607.24830.pdf` | HAVE ⚠ QUARANTINE | NUMERIC/HEURISTIC (math.GM, AI lab) — import ONLY via K3/K7 audit; archimedean law A_k(a) to 30 digits |
| YAKABOYLU-2024 | Yakaboylu, "Hamiltonian for the Hilbert–Pólya conjecture", J.Phys.A 57:235204 | arXiv:2408.15135 | `pdfs/2408.15135.pdf` | HAVE ✓ | A-NEG: documented negative search D0.7e (not a consumer) |
| BELLISSARD-2017 | Bellissard, critique of BBM | arXiv:1704.02644 | `pdfs/1704.02644.pdf` | HAVE ✓ | A-NEG: negative search D0.7e |
| BCF-BNBD-2012 | Bettin, Conrey, Farmer, Beurling–Nyman–Báez-Duarte (d_N²) | arXiv:1211.5191 | `pdfs/1211.5191.pdf` | HAVE ✓ | A-NEG: negative search D0.7e |

## Owner-fetch (PAYWALL / print / book — Uni proxy; drop in pdfs/)

- Weil 1952 «Sur les "formules explicites"…» (print; easier via Изв. АН СССР 36, 1972) — the Q_W ⪰ 0 ⇔ RH criterion (α-Gate foundation).
- Yoshida 1992, ASPM 21 281–325 (PAYWALL) — psd Q_W ⇔ RH.
- Bombieri 2000, Rend. Lincei (9) 11 №3 183–233 (PAYWALL) — #neg eigenvalues = ½ off-line zeros (ZEO base).
- Landau–Widom 1980, JMAA 77 469–481, DOI 10.1016/0022-247X(80)90241-3 (PAYWALL) — plunge ≍ log c.
- Titchmarsh (Heath-Brown) 1986 (book) — ξ/zeros facts.
- de Branges 1968 (book) — Hilbert spaces of entire functions.
- Gonek 1993, Contemp. Math. (VERIFY vol/year before .bib) — Landau explicit formula.
- Lean4 CADE-28 (de Moura, Ullrich) DOI 10.1007/978-3-030-79876-5_37 — cite-only (B).
- Mathlib modules MellinTransform / RiemannZeta / Gamma — cite-only, no PDF (B).

## Deep usage cards — Part 2 (roof / tail, 2026-08-03)

- `SUZUKI_SCREW_USAGE_CARDS.md` — SUZUKI-SCREW-2026 (2606.09096): 6/6 verbatim.
  Unification of Yoshida/Bombieri/CC/CCM = a PROGRAM (re-derivation framework), NOT one
  proved theorem; apex a→∞ limit (Cor 1.6) is CONJECTURAL. **ROOF ASSET: Theorem 1.5 —
  entire approximants W(a,θ;z) have ALL ZEROS REAL, proved UNCONDITIONALLY** (= spectrum
  of a self-adjoint extension). **Thm 1.4: λ_a positive/simple/even proved for SMALL a**
  (H2a analogue, but small-a only). α-Gate: Weil criterion cited [15]; Yoshida localized
  positivity re-proved unconditionally (Thm 1.3). C3/roof a→∞ convergence = OPEN (Cor 1.6
  sufficient-condition only). de Branges realization cited [14], used only in §7 heuristic.
- `KULIKOV_PLUNGE_USAGE_CARDS.md` — KULIKOV-PLUNGE-2026 (2603.07407) + LARSEN (2603.23832)
  + PREPLUNGE (2306.12430): all targets verbatim, ALL UNCONDITIONAL (pure harmonic
  analysis, no RH/Q3 content — TAIL/LADDER TOOLS only). **Sharpest:**
  −log(1−λ_n(c)) ≍ (c−n)/log(2c/(c−n)) (Thm 1.6+1.7, two-sided). **Best H4-DetectorDecay
  tool: Lemma 1.8 (paper 2)** — scale-uniform singular-value decay σ_n ≤ C e^{−τn},
  constant independent of scale r → cleanest W_j→0. Maps: edge-tail → C3/two-level-ladder;
  λ_n≥1−δ^c + Lemma 1.8 → H4-DetectorDecay.

## Part 3 — promoted from Zotero master (2026-08-03)

Full owner Zotero library (55) recorded in `ZOTERO_MASTER.md`. Promoted here = maps to a
Q3 gap. ★-books/paywall/Zenodo → owner drops PDF in pdfs/ (owner HAS them in Zotero).

| Key | Bibliographic identity | ID | Local PDF | Access | USED FOR |
|---|---|---|---|---|---|
| MALAM-TWIN-2025 | Malamutmann, "Spectral positivity and twin prime coherence via Weil's criterion" | doi:10.5281/zenodo.17541763 | — | OWNER-Zotero | **TARGET manuscript** (owner's own claim set) |
| MALAM-OPGEOM-2025a | Malamutmann, "Operator–Geometric Proof of RH via Positivity of the Weil Functional" | doi:10.5281/zenodo.17538227 | — | OWNER-Zotero | **TARGET manuscript** |
| MALAM-OPGEOM-2025b | Malamutmann, "Operator–Geometric Proof of RH via Positivity of the Weil Functional" | doi:10.5281/zenodo.17527099 | — | OWNER-Zotero | **TARGET manuscript** |
| TOEPLITZ-1911 | O. Toeplitz, "Zur Theorie der quadratischen und bilinearen Formen…", Math. Ann. 70 (1911) 351–376 | doi:10.1007/BF01564502 | — | owner-fetch | Toeplitz-forms foundation — **M1/H2b** (CvS Carathéodory–Fejér lives here) |
| GRENANDER-SZEGO-1958 | Grenander, Szegő, "Toeplitz forms and their applications", UC Press 1958 | — | — | BOOK | Toeplitz/Szegő limit theory — **H2b / Szegő–Böttcher** |
| SZEGO-OP-1952 | Szegő, "Orthogonal polynomials", 2nd ed., AMS Colloq. 23, 1952 | — | — | BOOK | OPUC/Lagrange/Vandermonde — **M1/M3** primitives |
| BOTTCHER-SILBERMANN-1999 | Böttcher, Silbermann, "Introduction to large truncated Toeplitz matrices", Springer 1999 | doi:10.1007/978-1-4612-1426-7 | — | BOOK | our Szegő–Böttcher `C_SB`; truncated-Toeplitz spectra — **STEP34 / H2b** |
| HORN-JOHNSON-2013 | Horn, Johnson, "Matrix analysis", 2nd ed., CUP 2013 | — | — | BOOK | matrix-determinant lemma, Hermitian spectrum — **M1** primitives |
| GUINAND-1948 | Guinand, "A summation formula in the theory of prime numbers", Proc. LMS 50 (1948) 107–119 | doi:10.1112/plms/s2-50.2.107 | — | PAYWALL | Guinand summation = Guinand–Weil dictionary (Groskin) — **STEP34** |
| LI-CRITERION-1997 | Li, "The positivity of a sequence of numbers and the RH", JNT 65 (1997) 325–333 | doi:10.1006/jnth.1997.2137 | — | PAYWALL | Li's positivity criterion — **α-Gate family** |
| BOMBIERI-MILLENNIUM-2000 | Bombieri, "Problems of the Millennium: The Riemann Hypothesis", Clay 2000 | claymath.org | — | OA (owner) | RH criterion/survey — α-Gate context |
| GORZ-JENSEN-2019 | Griffin, Ono, Rolen, Zagier, "Jensen polynomials for the Riemann zeta function…", PNAS 116 (2019) | doi:10.1073/pnas.1902572116 | — | OA (owner) | hyperbolicity/Jensen criterion |
| ARONSZAJN-1950 | Aronszajn, "Theory of reproducing kernels", TAMS 68 (1950) 337–404 | doi:10.1090/S0002-9947-1950-0051437-7 | — | owner-fetch | RKHS foundation — **RKHS cap** |
| PAULSEN-RAGHU-2016 | Paulsen, Raghupathi, "Intro to the theory of RKHS", CUP 2016 | doi:10.1017/CBO9781316219232 | — | BOOK | RKHS reference — RKHS cap |
| RODGERS-TAO-DBN-2021 | Rodgers, Tao, "The de Bruijn–Newman constant is non-negative", Forum Math. Pi 8 (2020) e6 | arXiv:1801.05914 | `pdfs/1801.05914.pdf` | HAVE ✓ | heat-flow / ξ evolution — Q3 heat-kernel layer (A1' density) |
| POLYMATH-DBN-2019 | Polymath, "Effective approximation of heat flow evolution of the Riemann ξ…", Res. Math. Sci. 6 (2019) 31 | doi:10.1007/s40687-019-0193-1 | — | OA (owner) | heat-flow ξ approximation — heat layer |
| GUTH-MAYNARD-2024 | Guth, Maynard, "New large value estimates for Dirichlet polynomials", Ann. Math. 2024 | arXiv:2405.20552 | `pdfs/2405.20552.pdf` | HAVE ✓ | Dirichlet large values — RH_TRICK_ATLAS card 3 |

## Part 4 — collected book PDFs, HAVE + attached to Zotero (2026-08-03)

| Key | Bibliographic identity | Zotero | Local PDF | Access | USED FOR |
|---|---|---|---|---|---|
| HORN-JOHNSON-2013 | Horn, Johnson, Matrix analysis 2nd ed. 2013 | zot:4BVIQ9IL | `pdfs/horn_johnson_matrix_analysis_2013.pdf` | HAVE ✓ | M1 matrix-det lemma, Hermitian spectrum |
| CONNES-MARCOLLI-2008 | Connes, Marcolli, NCG quantum fields and motives 2008 | zot:4JEG5BAC | `pdfs/connes_marcolli_ncg.pdf` | HAVE ✓ | NCG/zeta background |
| TITCHMARSH-1986 | Titchmarsh (Heath-Brown), Theory of the Riemann zeta-function | zot:XLAGXGTZ | `pdfs/titchmarsh_zeta.pdf` | HAVE ✓ | xi/zeros ClassicalXiInterface |
| MATHLIB-PDF | mathlib, The Lean mathematical library | zot:P7BC5LDN | `pdfs/1910.09336.pdf` | HAVE ✓ | Lean/Mathlib API |
| TOEPLITZ-1911-PDF | Toeplitz 1911, quadratische und bilineare Formen | zot:MS8BZUH5 | `pdfs/toeplitz_1911.pdf` | HAVE ✓ | M1/H2b Toeplitz foundation |
| BOTTCHER-SILBERMANN-PDF | Böttcher, Silbermann, Large truncated Toeplitz 1999 | zot:NNPBIU32 | `pdfs/bottcher_silbermann_1999.pdf` | HAVE ✓ | C_SB truncated Toeplitz STEP34/H2b |
| ARONSZAJN-1950-PDF | Aronszajn, Theory of reproducing kernels 1950 | zot:PMKIIXRV | `pdfs/aronszajn_1950.pdf` | HAVE ✓ | RKHS foundation |
| BERLINET-2004-PDF | Berlinet, Thomas-Agnan, RKHS 2004 | zot:QEZAGXJ6 | `pdfs/berlinet_thomas_agnan_2004.pdf` | HAVE ✓ | RKHS |
| EDWARDS-1974 | Edwards, Riemann's Zeta Function 1974 | zot:74A9V2Z7 | `pdfs/edwards_1974.pdf` | HAVE ✓ | classic zeta reference |
| MONTGOMERY-VAUGHAN-2007 | Montgomery, Vaughan, Multiplicative NT I 2007 | zot:A22KDNUS | `pdfs/montgomery_vaughan_2007.pdf` | HAVE ✓ | classic analytic NT |
| VARGA-2004 | Varga, Gershgorin and his circles 2004 | zot:ENW9WZ8G | `pdfs/varga_2004.pdf` | HAVE ✓ | eigenvalue localization |
| INGHAM-1932 | Ingham, Distribution of Prime Numbers 1932 | zot:PAECCAFH | `pdfs/ingham_1932.pdf` | HAVE ✓ | classic prime distribution |
| IWANIEC-KOWALSKI-2004 | Iwaniec, Kowalski, Analytic Number Theory 2004 | zot:9LDLY24L | `pdfs/iwaniec_kowalski_2004.pdf` | HAVE ✓ | analytic NT reference |
| SZEGO-OP-1939 | Szegő, Orthogonal Polynomials AMS Coll.23 | zot:NAP5SMQF | `pdfs/szego_orthogonal_polynomials_1939.pdf` | HAVE ✓ | M1/M3 OPUC/Lagrange |
| PAULSEN-RAGHU-2016 | Paulsen, Raghupathi, Intro to the theory of RKHS 2016 | zot | `pdfs/paulsen_raghupathi_2016.pdf` | HAVE ✓ | RKHS cap |
| GRENANDER-SZEGO-1958 | Grenander, Szegő, Toeplitz Forms and Their Applications 1958 | zot | `pdfs/grenander_szego_1958.pdf` | HAVE ✓ | M1/H2b Toeplitz forms monograph |
| MALAM-FEJERHEAT-2025 | Malamutmann, Fejér–heat generators and Lipschitz control for the Weil quadratic functional, Dec 2025 | owner | `pdfs/malamutmann_fejer_heat_2025.pdf` | HAVE ✓ | **OWNER paper**: analytic properties of the Weil functional Q = A1'/A2/α-Gate |

## M1 formalization formula cards (2026-08-03)
- `M1_MATRIX_FORMULA_CARDS.md` — Horn-Johnson (6/6): Sylvester inertia Thm 4.5.8 p.282; matrix-det lemma eq(0.8.5.11) p.26 (adjugate, no invertibility side-cond); Hermitian=>real Thm 4.1.3(b); similarity Thm 1.3.3/Cor 1.3.4; Cholesky Cor 7.2.9 + symmetric sqrt Thm 7.2.6. **Complete 6-step M1 Lean chain** (S=Q^{1/2} => symmetric conjugation => real eigenvalues => transfer), Mathlib names attached (Matrix.PosSemidef.sqrt, IsHermitian.eigenvalues, mul_adjugate); prefer symmetric-sqrt over triangular Cholesky in Lean.
- `CF_TOEPLITZ_FORMULA_CARDS.md` — Grenander-Szego + Toeplitz 1911 (5/5): Toeplitz L-form def (T1911 p.351); associated forms f>=0<=>T_n PSD (§1.10); **Caratheodory rank-deficient PSD Toeplitz atomic rep, nodes on circle (§1.11 p.19)**; Fejer-Riesz factorization + reciprocal zero-symmetry (§1.12 p.20); Szego eigenvalue distribution (§5.2); OPUC/Toeplitz-det recursion (§2.1-2.2). FINDING: the exact CvS corollary (PSD Toeplitz rank n-1 => zeros on unit circle) is NOT one labelled theorem in G-S — it = §1.11 + §1.12 combined, or Caratheodory 1911 original (G-S bib p.243). NB: our M1 uses the FINITE §5 route which BYPASSES this Toeplitz corollary (see CVS_H2B bridge) — these cards arm the alternative/understanding, not the critical path.
| ANDREWS-CCM-REPRO-2026 | Andrews, Ronnie, Jr., "Independent Reproduction and Convergence Analysis of the Connes-Consani-Moscovici Zeta Spectral Triple" |  doi:10.5281/zenodo.20427500 | `pdfs/andrews_ccm_reproduction_2026.pdf` | HAVE ✓ | карточка: `ANDREWS_CCM_REPRO_USAGE_CARDS.md` |
| MASATOSHISUZUKI-2022 | Masatoshi Suzuki, "Aspects of the screw function corresponding to the Riemann zeta function" | arXiv:2206.03682 | `pdfs/2206.03682.pdf` | **HAVE** | `SUZUKI_ASPECTS_2206_USAGE_CARDS.md` — Thm 4.3 подтверждена дословно; для формы Вейля целевое утверждение — Yoshida [33, Lemma 3], не Thm 4.3 |
| YOSHIDA-HERMITIAN-1992 | Yoshida, Hiroyuki, "On Hermitian Forms attached to Zeta Functions", Adv. Stud. Pure Math. 21 (1992) 281–325 | doi:10.2969/aspm/02110281 | `pdfs/yoshida_hermitian_forms_1992.pdf` | **HAVE** | `YOSHIDA_HERMITIAN_1992_USAGE_CARDS.md` — **Lemma 3**: пол формы Вейля в честной `L²`-норме на `K_N(a)`, константы выписаны явно. Целевое утверждение для `Lock B` GLOWER |
| SIEGFREDALANCBALUYOTANDDANIELALANGOLDSTONANDADEIRMASURIAJAYAANDCAROLINELTURNAGEBUTTERBAUGH-2025 | Siegfred Alan C. Baluyot, "Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of Simple Zeros and Critical Zeros" | arXiv:2501.14545 | `pdfs/2501.14545.pdf` | **NEEDS_CARDS** | затянуто paper.sh 2026-08-11 — карточка не написана |
| DANIELALANGOLDSTONANDJUNGHUNLEEANDJORDANSCHETTLERANDADEIRMASURIAJAYA-2025 | Daniel Alan Goldston and, "Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I: Simple and Critical Zeros" | arXiv:2503.15449 | `pdfs/2503.15449.pdf` | **NEEDS_CARDS** | затянуто paper.sh 2026-08-11 — карточка не написана |
| DANIELAGOLDSTONANDADEIRMASURIAJAYA-2025 | Daniel A. Goldston and, "Zeta Zeros on the Critical Line" | arXiv:2511.20059 | `pdfs/2511.20059.pdf` | **NEEDS_CARDS** | затянуто paper.sh 2026-08-11 — карточка не написана |
| DANIELAGOLDSTONANDADEIRMASURIAJAYA-2026 | Daniel A. Goldston and, "Zeta Zeros in a Narrow Vertical Box" | arXiv:2603.28104 | `pdfs/2603.28104.pdf` | **NEEDS_CARDS** | затянуто paper.sh 2026-08-11 — карточка не написана |
| MONTGOMERY-PAIRCORR-1973 | Montgomery, H. L., "The pair correlation of zeros of the zeta function" |  doi:10.1090/pspum/024/9944 | `pdfs/montgomery_pair_correlation_1973.pdf` | **HAVE** | `MONTGOMERY_PAIR_CORRELATION_1973_USAGE_CARDS.md` — первоисточник константы 2/3 (при RH); prime-side второй момент безусловен |
| BOMBIERI-WEILQF-2000 | Bombieri, Enrico, "Remarks on Weil's quadratic functional in the theory of prime numbers, I" |  | `pdfs/bombieri_weil_quadratic_functional_2000.pdf` | **HAVE** | `BOMBIERI_WEIL_QF_2000_USAGE_CARDS.md` — **§7 резольвента, §8 Theorem 8 (число отрицательных собств. знач. конечной матрицы), §9 чётные/нечётные, §10 переход к пределу** — оглавление совпадает с нашей открытой задачей |
