# Where the pillars came from (observer, 2026-10-29)

Owner's question: the pillars were built after reading publications, mainly Connes and Suzuki. Is that right, link by link?
Method: three read-only agents traced `docs/Codex/PAPER_CHAIN.md` links to our cards, ledgers and git history; the observer re-checked the key quotes (marked ✓).

## Short answer
- **Connes: yes.** The two open pillars G1 and G3 are the two "missing steps" that CCM name in §8 p.32 (verbatim ✓ `docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md:90-98`).
  Connes 2602.04022 §6.6 p.30 repeats them and says the simple-even property "is known for the prolate wave operator" (✓ `CONNES_RH2026_USAGE_CARDS.md:9-24`).
  G4 is CCM Lemma 7.3; G2/G2b rest on CCM Thm 5.10 and Prop 5.9 and on Connes–van Suijlekom 2511.23257; the matrix itself (G0) is CCM Lemma 5.1.
- **Suzuki: not as a pillar supplier.** No current link takes a statement from Suzuki. Suzuki shaped the roof idea and two side routes:
  - 2606.09096 Cor. 1.6 is a closure theorem of our roof's shape (real-zero entire bricks + locally uniform convergence ⇒ RH), stated as a conjecture; Thm 1.5 gives real zeros of W(a,θ;z) unconditionally; Thm 1.4 gives simple, even, positive bottom for small a (✓ `SUZUKI_SCREW_USAGE_CARDS.md:9,61-74,97-120`).
    Our 08.09 reading: Suzuki's bricks give real zeros for free (self-adjointness) and move the whole difficulty into convergence with normalization (✓ `docs/CHAT_DIGESTS.md:1626-1631`).
  - The 07.08 digest says the conditional theorem A∧B∧C ⇒ RH was assembled from CCM 2511.22755 and Suzuki 2606.09096 (✓ `docs/CHAT_DIGESTS.md:36-40`). This is the likely source of "Connes and Suzuki".
  - 2206.03682 led to Yoshida Lemma 3 (odd-floor supplier GLOWER, killed 30.08); 2301.00421 second-expression route killed 06.09, error confirmed by the author (`paper_weil/SUZUKI_CORRESPONDENCE_2026.md`).
  - The March paper's Suzuki/Yoshida bridge H1f..H4f (route ii) was never built and was replaced by Route B (`docs/GENEALOGY.md:229-249`).

## Link table (current PAPER_CHAIN numbering)
| Link | Taken from | Our own part | Card read? |
|---|---|---|---|
| G0 object, schedule | CCM Lemma 5.1 matrix τ_ij=(b_i−b_j)/(i−j), Prop 5.9 transform | m=N=k+2, s=−Lz/2π, c=2πm | CCM card, RECON 06–08.08 |
| G1 simple even ground | CCM §8 step 1; Thm 5.10 hypothesis | hfloorEv (killed 25.09), hratioEv, hoddEv, parity table 28.10, G1a reduction 28.10 | verbatim |
| G2 real zeros of row | Connes–van Suijlekom §5 (L5.1, L5.2, Thm 5.6, Prop 5.10); CCM Thm 5.10 | Lean proof (rank-one correction, quotient by radical) | CvS card with pages |
| G2b transfer to transform | CCM Prop 5.9 (5.25) | transfer lemma, Lean | Codex PDF check |
| hentire | CCM Prop 5.9, Thm 5.10(iii) | Lean proof | verbatim Thm 5.10 |
| G3 tracking | CCM §8 step 2 | the exact form "norm × kernelL2 × √ratio → 0"; still no formulation | verbatim |
| G3c projection tail | CCM (7.5), (7.9), Lemma 7.2(ii) as target | O(m^-1/4) rate, PAPER_OWN rev 06.10 | audit locators |
| G4 | CCM Lemma 7.3 p.31 | selected-shell crosswalk | verbatim |
| hmode / hχ / hθ | shape and rate from CCM Lemma 7.2 (via Meixner–Schäfke Satz 9, Fuchs Thm 1) | proof is Proshka's (25.09), re-checked by us; uses neither source | MS and Fuchs cards |
| G5 roof | classical Hurwitz; same shape as Suzuki Cor. 1.6 and CCM's two-limit plan | Lean | n/a |
| SP floor | no paper; Bombieri Thm 8 as background | ours, CONDITIONAL | partial |

## Renamings
H2a → G1, H2b → G2/G2b, C3-A → G4, C3-B → G3 (until 31.07); Mythos canvas G1–G7 (31.07, G7 = Hurwitz roof); Route 058 numbering G0–G5, G2b, G3c (12.08, `ROUTE058_GATE_CONTRACTS.md:34-42`); the G1–G6 of `CHAIN_GAP_DESIGN.md` (19.08) are different objects.

## Gaps found
- `PAPER_CHAIN.md` "Главное наблюдение" says itself that the G1/G3 ↔ CCM match is the reader's inference; no matrix crosswalk is written.
- No verbatim card for CCM Lemmas 5.1, 5.2, 5.4 and Prop 5.9 (only source locks and a Codex PDF check).
- Davis–Kahan locator for hratioEv not recorded. SP link to CCM Cor 3.8 not recorded. Mythos source of the 07.08 digest not on disk.
