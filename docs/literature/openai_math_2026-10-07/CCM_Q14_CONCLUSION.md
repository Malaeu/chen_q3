# Q14 — complete signed contour audited; arithmetic remains open

2026-10-23. Natural completion 11:03 Europe/Berlin; retrieved 11:21.
Status: BOUNDED_PAPER_PASS_CONDITIONAL_ON_INHERITED_SOURCE_IDENTITIES.
Original P, N=m, L=log m, both temporal halves and mixed forms retained.
RH OPEN; PX_RH_CLAIM NOT_MADE. No Lean or new Arb run.

## Original and reproduction

Full original: PROSHKA_CCM_PROJECTED_SIGNED_REMAINDER_Q14_VERDICT_2026-10-23.md,
84411 bytes, 1274 LF, SHA256
9571fbd684ab3768d6241eb18dab65c1f7696f316cc07c9d1639d1beae6ed036.
Byte-identical to downloaded original, read in full. Request 178829 bytes,
SHA256 37fd32b43e7ced9adeb1e4dbc47636ce627b21acf50de47e1b42b742d7ef56bc;
all nine source bodies match local files and embedded request line ranges.
Scripts and source manifest extracted losslessly into q14_reproduction/.
105 exact SymPy1.14 controls and nine mpmath1.3/45-digit diagnostics rerun;
both JSON results byte-identical. Commands:
`uv run --offline --with sympy==1.14.0 python .../q14_reproduction/check_q14.py`
and `.venv/bin/python .../q14_reproduction/diagnostic_q14.py`.
Initial .venv SymPy import unavailable; cached uv environment succeeded.
Six rational contour controls are not xi; three xi points are normalization
checks only. They do not certify a global spectral estimate or locate poles.

## Accepted bounded result

Root review and one independent read-only audit (q14_verdict_audit) agree:
full September ++/+- formulas cancel the apparent 1-kappa denominators.
For F(z)=xi(1/2+z), Z=F/(F+Fprime), a genuine simple Z-pole lambda has
kappa(lambda)=1 and kappa(-lambda)=-1. Complete source filters cancel their
apparent free exponential poles p=+/-lambda. Remaining source dependence is
retained. The earlier generic projected exponential test is valid, but cannot
be read as an actual residue contribution or an asymptotic obstruction.

Finite clockwise contour gives Delta=I_sigma-I_0 = A_sigma,Y + T_sigma,Y.
A includes ALL actual signed residues AND both horizontal edges. Higher-order
poles require derivatives; conjugate pairs retain the full real part, not
positive independent atoms. No global residue-only expansion is admitted.

With sigma=1/2+1/log m and Y comparable to m^(1/2+epsilon+nu), vertical return
is O(m^(-2nu)/(log m)^2 + m^(-nu)/log m), uniformly on original P. The second
term retains the complete central jump. There is no extra dimension factor.
Horizontal edges and their mixed terms are NOT proved small. Q13 return is
not charged twice; the same Q needs no second archimedean charge.

External input checked against Sondow–Dumitrescu Theorem1 and its proof:
https://arxiv.org/pdf/1005.1104 . Only the unconditional Re(s)>1 region is
used, giving Re(Fprime/F)>=0 and |Z|<=1 for Re(z)>1/2. Nothing inside the
centered critical strip is declared zero-free. September and Q12/Q13
identities remain inherited, not independently re-proved in this cycle.

## Full budget and justified rollback

The actual one-sided A bound is still unpaid. Completed full defect remains
O(sqrt m), not eta(epsilon)->0; conditional 3/8/ZF78 is unchanged.
This stalls the separate positive Suzuki Gram route as a supplier of new
arithmetic power; it does not disprove joint cancellation or the CCM goal.

Rollback before splitting Gram and defect: N-Delta=2||psi||^2-I_sigma=Q.
The imaginary-axis term and auxiliary F+Fprime denominator cancel together.
Keep Q14 as an analytic checking tool, not another mandatory hard supplier.
Return to the original projected Q lower floor / signed prime operator.
Next bounded discriminator: inspect the existing signed Mobius decomposition
and test whether a proposed joint estimate improves its known 3/8 budget
with every boundary and cross term included, BEFORE constructing another
representation or asking Q15. No new mechanism or exponent is claimed here.
No Q15 sent, no author email, no pending Pro answer. Overall goal stays open.
