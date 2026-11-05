# PROVE_RH_RESPONSE_IDENTITY_AUDIT — preregistration

DIAG only; no RH claim, no admission of (7.4). Base rh_clean
5a409f1e88439d12c5d84126e09d421781d24e26. Verdict commit
62f782316d2ba4f83d27db82d0b64e1e8361cad2, blob
2b5e02a0aa816da34c204f2a56a9033e6ac6b542.

Before any numerical run: Task A uses exactly t=0,.5,1,2,3,4,5,6,
mpmath dps60 then80; prime cutoff floor(exp(t+9)); all prime powers;
quad H with the literal j and c; gamma<=60 zetazero sum. Quartet is
added as the builder's bilinear form (complex squares, not modulus squares).
Gate abs(arithmetic-zero)<=1e-40*(abs(H)+abs(S)). Record every failure
as IDENTITY_FAILURE with values and responsible term; never retune.
Deliberately shift c by +1e-30 and report failure. Report cancellation
using zero-side full-response estimate, and also truncated arithmetic h.

Prediction from inspection, not a run: the specified prime cutoff at Gaussian
distance9 leaves an omitted tail much larger than 1e-40. Thus the prescribed
finite-sum gate is expected to fail even if the full-line identity is correct.
The c-shift should fail too, but may be masked by this baseline truncation.
A bound/omitted-term diagnosis must not silently extend the gate cutoff.
Zero tail above60 should be negligible. Zeta zero response is about1e-34.

Task B: literal (6.1), no graph normalization, m16,64,300,1000,3000;
source arithmetic matrices through300, function-level form thereafter,
crosscheck300. Report signed telescoping contributions from cutoff,
projection, e0 and e1 separately. Expect substantial finite-window error;
no growth fits. Derive explicit bounds if possible, distinguish bounds
from numerical estimates, and report any unavailable bound as such.

Task C: pure formula only. Report all DH off-line census rows and plant
using the fixed F and a clearly declared online envelope and return bound.
No finite matrix growth extrapolation. If the return bound is unavailable,
thresholds omitting it are only conditional lower benchmarks, not m*.

Delivery: one final commit on rh_clean, ordinary push. To reconcile the
required pre-run commit with one final delivered commit, first commit this
file alone, record its immutable object ID, then amend that same local commit
with scripts/results/report/checksums. Keep a bundle of the preregistration
commit as evidence. No other repository state or source formulas change.
