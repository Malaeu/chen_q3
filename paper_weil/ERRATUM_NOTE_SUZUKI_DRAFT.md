# Note to the author of arXiv:2301.00421 — FINAL DRAFT (not sent; owner sends or approves sending)

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
