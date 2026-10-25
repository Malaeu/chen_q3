# Note to the author of arXiv:2301.00421 — SENT 2026-09-06 (Gmail, on the owner's word; message id 1a0757fbffc2d59f)

Verification trail: judge (SECONDEXPR-B, b1efb9e1) → observer (verbatim PDF check, Progress_Log 2026-09-06) → blind agent re-derivation from the
paper's (3.3) (AGENT_REPORT_2026-09-06_SECONDEXPR_B_INDEPENDENT_CHECK.md). Person-name gates: name and e-mail from the paper itself (arXiv v3, last page:
msuzuki@math.sci.isct.ac.jp; Institute of Science Tokyo, 2-12-1 Ookayama, Meguro-ku); faculty page https://strdb.s.isct.ac.jp/html/100001253_en.html
(Professor, School of Science, updated 2025-11-12); active in the subfield (arXiv 2606.09096, 2026). Stance: not applicable (question about his own paper).

To: msuzuki@math.sci.isct.ac.jp
Subject: A question about the negative-time extension of S_t in "On the Hilbert space derived from the Weil distribution"

Dear Professor Suzuki,

I am writing about your paper "On the Hilbert space derived from the Weil distribution" (arXiv:2301.00421v3; Canadian Journal of Mathematics, 2025), which I have been using in a project on Weil positivity around Riemann's test function.

On page 3, after the definition (1.5) of S_t(z) for nonnegative t, the paper sets, for negative t, S_t(z) := S_{-t}(z), and after (3.2) likewise P_t(z) := P_{-t}(z). With this even extension the map t -> S_t^sharp(z) is even in t. The transform (1.7) applied to D psi = i psi' is then identically zero for every even psi in C_c^infinity(R), because psi' is odd. On the other hand, for a narrow even bump psi_L supported in an interval shorter than log 2 one has <psi_L, psi_L>_W > 0 (the classical short-support positivity; for very small L the value is at least 2 ||psi_L||^2). So the equality (1.9) of Theorem 1.4 cannot hold for such psi under the even extension, independently of the Riemann Hypothesis. A second symptom inside the paper: with the even extension, (4.4) would give G_g(t,t) = G_g(t,-t), i.e. g(2t) = 0, which is not the case.

It seems to me that the intended extension is the signed one, P_{-t}(z) = P_t(-z) for t > 0, equivalently the expansion (3.2) taken for all real t with the symmetry of Gamma under gamma -> -gamma. Under that extension (3.7)-(3.8) hold with the signed exponentials, and the arguments of Sections 3-4 go through as written. Could you confirm that this is the intended reading, or point out what I have misunderstood? If the signed extension is intended, a short erratum might help readers.

Two small remarks, in case they are useful: the estimate displayed before (4.5) seems to require the constant 4 pi rather than pi, since |e^{-i gamma t} - 1| <= 2; and since the dash in (1.3) denotes d/ds, readers translating to the variable z should note xi'(1/2 - iz) = i dX/dz for X(z) = xi(1/2 - iz).

I would be glad to be corrected if I am mistaken, and I thank you for the paper, which has been very useful to me.

With kind regards,

Eugen Malamutmann
University of Duisburg-Essen

---

## REPLY RECEIVED 2026-09-06 09:37 UTC (found 2026-10-22; the message sat UNREAD in Gmail for six weeks, Progress_Log said "unanswered")

From: Masatoshi Suzuki <msuzuki@math.titech.ac.jp>, Gmail message id 1a07614303ba0446, thread 1a0757fbffc2d59f.

> Thank you very much for your careful reading of my paper. You are right that a correction is needed.
> Equation (3.2) should define P_t(z) for all real t, rather than only for nonnegative t. To be consistent with this, the definition on p. 4, S_t(z):=S_{-t}(z), should be replaced by P_t(z):=\overline{P_{-t}(\bar z)}. In addition, I noticed that the i in (1.5) should be -i.
> Thank you again for pointing out these errors.

**Consequences to check (not yet checked):**
1. Suzuki's stated extension is `P_t(z) := conj(P_{-t}(conj z))`, NOT the letter's proposal `P_{-t}(z) = P_t(-z)`. The two coincide only where P has the relevant reflection symmetry; every place in paper_weil / Route B that imported "the signed extension" must be re-read against Suzuki's form.
2. New error not in the letter: sign of `i` in (1.5) is `-i`. SECONDEXPR-B re-derived c_A from (3.3) under the printed (1.5); re-derivation needed.
3. Status line of this file and Progress_Log entry 2026-09-06 ("sent/unanswered") are superseded by this reply.

## CHECK 2026-10-22 — the two extensions coincide (consequence 1 above is CLOSED)

With (3.2) P_t(z) = Σ m_γ (e^{-iγt}-1)/(γ(z-γ)) for t ≥ 0:
- letter's P_{-τ}(z) := P_τ(-z) equals "(3.2) at t = -τ" iff Γ is closed under γ ↦ -γ;
- Suzuki's P_{-τ}(z) := conj(P_τ(conj z)) equals "(3.2) at t = -τ" iff Γ is closed under γ ↦ conj γ;
- Γ has both symmetries with equal multiplicities (paper, §3.1), so all three agree unconditionally, no RH used.
Numerics (scripts/suzuki_extension_check_2026-10-22.py, fake off-line zeros): both symmetries → |A-B| = |A-C| = 0;
only γ→-γ → |B-C| = 3.9e-3; only γ→conj → |A-C| = 1.4e-2. The SECONDEXPR-B "signed unconditional expansion" is exactly C.

Consequence 2 (i → -i in (1.5)): a global factor -1 on 𝔖_t. Every object used downstream is quadratic in 𝔖 or in P̂
(⟨𝔖_t,𝔖_u⟩, (4.4)–(4.6), (1.9), Lemma 2, c_A, Volterra Gram), hence unchanged. Only a *linear* use of 𝔖_t or P̂_φ would flip sign;
paper_weil sections grep: see count below at time of writing. Status: no recomputation needed unless a linear use is found.

## 2026-10-25 — Zenodo status note POSTED
STATUS NOTE inserted as first paragraph of the description of 10.5281/zenodo.17527099, 17541763, 17956251 (metadata edit, no new version). Wording: "by an academic without formal training in mathematics". Verified via public API (updated 2026-10-25 10:23/10:24/10:25 UTC).

## 2026-10-25 — REPLY SENT (11:19 UTC, Gmail, thread 1a0757fbffc2d59f, message id 1a172c90ca8628fb, to msuzuki@math.titech.ac.jp)
Three paragraphs: apology for the six-week silence; the check that his extension, the letter's, and (3.2) for all real t coincide (zero set symmetric under γ→−γ and γ→γ̄), sign of i harmless since everything downstream is quadratic; "not a professor of mathematics, not my field by training", thanks without a request. Endorsement request and "surgeon" removed on the author's decision. Signature: University of Duisburg-Essen + ORCID link. Text: REPLY_TO_SUZUKI_DRAFT_2026-10-22.md. Status: awaiting nothing; thread closed unless he answers.
