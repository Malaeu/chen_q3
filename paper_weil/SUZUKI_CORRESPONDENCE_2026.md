# Correspondence with M. Suzuki on arXiv:2301.00421v3 (2026)

Paper: M. Suzuki, "On the Hilbert space derived from the Weil distribution", arXiv:2301.00421v3; Canadian Journal of Mathematics (2025).
Source: Gmail thread `1a0757fbffc2d59f` of nodp53@googlemail.com, exported 2026-10-28 via the Gmail connector.
Each message is given in full; quoted earlier messages inside replies are omitted.
Context: defect found 2026-09-06, see `docs/Progress_Log.md:5613`, `:5632`, `:5658`; draft `paper_weil/ERRATUM_NOTE_SUZUKI_DRAFT.md`.

## Outcome

The author confirmed the defect: "You are right that a correction is needed."
Correction stated by the author:
1. (3.2) defines P_t(z) for all real t, not only for nonnegative t.
2. The definition on p. 4, S_t(z) := S_{-t}(z), is replaced by P_t(z) := conj(P_{-t}(conj z)).
3. The i in (1.5) should be -i (found by the author).

Our check (message 3): the author's extension, our signed extension P_{-t}(z) = P_t(-z), and (3.2) for all real t coincide,
because the zero set is symmetric under γ → −γ and γ → γ̄. The sign of i in (1.5) changes S_t by a global factor −1;
our uses are quadratic in S_t, so nothing in the project needed recomputing.

---

## 1. 2026-09-06 06:55 UTC — sent

From: Eugen Malamutmann <nodp53@googlemail.com>
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

## 2. 2026-09-06 09:37 UTC — received

From: msuzuki@math.titech.ac.jp
To: nodp53@googlemail.com
Subject: RE: A question about the negative-time extension of S_t in "On the Hilbert space derived from the Weil distribution"

Dear Professor Malamutmann,

Thank you very much for your careful reading of my paper. You are right that a correction is needed.

Equation (3.2) should define P_t(z) for all real t, rather than only for nonnegative t. To be consistent with this, the definition on p. 4, S_t(z):=S_{-t}(z), should be replaced by P_t(z):=\overline{P_{-t}(\bar z)}. In addition, I noticed that the i in (1.5) should be -i.

Thank you again for pointing out these errors.

With kind regards,

Masatoshi Suzuki

## 3. 2026-10-25 11:19 UTC — sent

From: Eugen Malamutmann <nodp53@googlemail.com>
To: msuzuki@math.titech.ac.jp
Subject: RE: A question about the negative-time extension of S_t in "On the Hilbert space derived from the Weil distribution"

Dear Professor Suzuki,

Thank you for your reply, and please forgive the long silence: your message reached a mailbox I check too rarely, and I found it only recently.

Thank you also for the corrections. I have since checked that the extension you give, Pt(z) = conj(P−t(conj z)), the one I had proposed, P−t(z) = Pt(−z), and (3.2) taken for all real t all coincide, because the zero set is symmetric under both γ → −γ and γ → γ̄. The sign of i in (1.5) changes St only by a global factor −1, and everything I use is quadratic in St, so nothing on my side needed recomputing. I was glad to find that.

One correction on my side: I am not a professor of mathematics, and mathematics is not my field by training. I read your papers, frankly, the way other people read novels. What draws me to them is the depth and the fact that your point of view is not the usual one. I have learned more from the Weil-distribution paper and your work on screw functions and canonical systems than from almost anything else in the area. I wanted to say that without asking for anything in return.

With kind regards,

Eugen Malamutmann
University of Duisburg-Essen
ORCID: orcid.org/0000-0003-4624-5890

## 4. 2026-10-25 12:33 UTC — received

From: msuzuki@math.titech.ac.jp
To: nodp53@googlemail.com
Subject: RE: A question about the negative-time extension of S_t in "On the Hilbert space derived from the Weil distribution"

Dear Eugen,

Thank you for your kind words. I am very glad to hear that you enjoy reading my papers and find them interesting.

I wish you all the best in your continued mathematical explorations.

Best regards,

Masatoshi
