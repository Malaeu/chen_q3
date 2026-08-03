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

## Deep usage cards (per-theorem, verbatim, sub-agent extracted)

- `CCM_ZST_USAGE_CARDS.md` — CCM-ZST-2025 (2511.22755): Thm 5.10, Thm 3.6, Lemma 7.2,
  Lemma 7.3, §8 missing steps, prolate operator W_λ + trial k_λ — all 6 verbatim with
  K7 tags and Q3-gap mapping. KEY: the paper itself (§8) marks BOTH `SIMPLE_EVEN(QW_λ)`
  (H2a) AND `k_λ ≈ ξ_λ` (C3-B) as UNPROVEN for the Weil form; Thm 5.10's real-zero
  conclusion is conditional on simple+even, proven only for the prolate PW_λ, never QW_λ.

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
