# Zenodo status note — paste as the FIRST paragraph of the description of 10.5281/zenodo.17527099 (v1), 17541763 (v4), 17956251 (v5). Metadata edit, no new version. Drafted 2026-10-22. POSTED 2026-10-25 to all three records (metadata edit, verified via public API: updated 10:23/10:24/10:25 UTC).

STATUS NOTE (added 25 October 2026 by the author).

This record is an attempt, by an academic without formal training in mathematics and with substantial help from AI systems, to write and check a proof of the Riemann Hypothesis along Weil's positivity criterion. It is not a proof. The word "Proof" in the title of version 1 (4 November 2025) is withdrawn; the title was changed to "Operator Methods for the Weil Criterion: Q3" two days later for this reason.

What is wrong: the main theorem is stated on the wide cone of all even, nonnegative, compactly supported test functions. The argument only supports the narrow positive-definite cone of convolution squares Φ = ψ * ψ̃. This one gap decides everything: it is exactly the step that would have to be closed to obtain RH, and I have since shown (June 2026) that closing it is equivalent to RH itself, so no assembly of the remaining pieces can replace it.

What is correct and survives: the conditional theorem "positivity on the narrow cone implies RH" with its bridges, several of which are formalised in Lean 4; the explicit operator identities; the companion preprint on Fejér–heat generators (10.5281/zenodo.17853582).

What is open: positivity on the narrow cone, i.e. RH. Work continues; any further error found in these files will be added to this note.

The three versions share this description; the files differ. Readers of version 1 should use the latest version together with this note.
