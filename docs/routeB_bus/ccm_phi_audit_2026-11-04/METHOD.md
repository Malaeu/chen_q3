# Independent interval method and verification

The standalone numerical engine imports only python-flint and the Python standard library. It reads no input data at all. Source and tail formulas are fixed to the pinned verdict. No numerical zero routine is called.

The exact Gamma kernel sum is evaluated through Arb acb.digamma/acb.polygamma. The exponentially small subtracted part retains r=0,…,5; the omitted nonnegative part is enclosed by [0,1] times exp(−a_R L)/(a_R²(1−exp(−2L))). Each retained arithmetic prime-power term is evaluated directly with Arb sin/cos. The triangular source loop accumulates trace, Frobenius square and all six signed source decomposition terms. O(m²) entries are streamed, not stored.

Tail integrals I,J use256 positive terms and the verdict's explicit geometric remainder mass. Arb encloses elementary/special-function roundoff; analytic remainder envelopes enclose the actual omitted infinite sums. Sensitivity to another precision is not used as an error bound. At160bits the m300 source uncertainty is dominated by the explicitly allowed exponential remainder; the tail uncertainty is dominated by its explicit series remainder.

Rational candidate gates may initially be selected using approximate midpoints, but a candidate is accepted only after a strict Arb comparison against the complete enclosure. N₊ is accepted only if the real count envelope is <N₊+1. Integer lower bounds n are accepted only if the score interval is >n−1. The displayed percentages are ordinary decimal renderings; rational fraction columns are exact.

The explicit count theorem is inclusive in its usual N(T); the desired head count is strict atT. An inclusive upper bound also bounds the strict count. In the tail Stieltjes identity, all height-T atoms are paid using N(T−). No endpoint atom is lost.

Replay requires python-flint0.9.0. The bounded supporting algebra checks additionally use sympy/mpmath/numpy as indicated by their imports. They are separate from Arb certification. Original external PDFs/text are retained in local scratch and excluded from the commit; URLs, SHA256 hashes, verified statement locations and limits are in the audit reports and EXTERNAL_SOURCES.json.

Raw ARB receipts retain their execution-time PENDING_PAPER_AUDIT label. Final bounded audit disposition and the permission to interpret the finite cells under explicit theorem premises are recorded separately in GATES.json. This preserves the chronological meaning of the receipts without rewriting them as if the paper audit preceded execution.

`build_results.py` assembles metadata and integer refinement. Original execution used /workspace/second_moment/output for the inherited verdict and local external PDFs; packaged INPUT_INHERITED_DENSITY.md and EXTERNAL_SOURCES.json preserve the exact inputs for subsequent assembly. `verify.py` is the offline scalar-packet verifier. SHA256SUMS covers every committed artifact except itself and is verified after final assembly.
