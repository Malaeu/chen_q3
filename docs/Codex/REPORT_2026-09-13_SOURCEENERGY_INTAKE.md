# SOURCEENERGY intake: positive heat energy has the wrong source output

STATUS: ACCEPTED_EXCLUDE_FIXED_COLLOCATED_CIRCLE_HEAT_PORT_ENERGY_ONLY_PAPER.
ACTUAL_V_SIGN: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean verification or canonical admission.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The exact circle heat model has a positive terminal energy, including its full dissipation, but its boundary output cannot equal the required source output for all finite rows. Only the specified fixed collocated class is excluded.

## 1. Received bytes and provenance

Raw response: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SOURCEENERGY_2026-09-13.md`.
69019 bytes / 825 LF / CR0 / final LF; SHA256
`cbba52e98cf7171d66d57ce695391319c6ddfb24ad9f82e1eab57a8f8743a396`.
Request commit: `c4cb2fa42e2583cd7744d6ee97d43aaa96098bf3`.
Source base: `fcfd09bdf18806664cd1b69f61e516cc35a70775`.

The living Pro task became idle; terminal observation at 16:32 UTC reported
`LOCAL_SAVED_WRITE_OPERATION_NOT_EXPOSED`, with the exact response SHA.
Pro did not create a Git commit. The named math branch still lacked the file.
The parent recovered the offered report through its browser download, checked
the downloaded bytes against that SHA, and copied them unchanged into the
isolated math worktree. This intake delivers those original bytes; it does not
retroactively describe Pro's local save as GitHub publication.

The parent read all 825 lines and appendices. Sole independent checker
`/root/sibling5_check` read the full exact response and returned
`ACCEPT_EXCLUDE_FIXED_COLLOCATED_CIRCLE_HEAT_PORT_ENERGY_ONLY`.
The checker explicitly replayed Appendix A byte-for-byte and found no
mathematical gap. Its retained message is a read-only review receipt, not an
external signed attestation or a canonical node acceptance.

## 2. What the positive construction actually proves

Keep the entire source f=Phi/A, A=||Phi||_2, with A distinct from Z.
For any finite real nodes and complex coefficients, retain the original
P_c(t)=sum c_j f(x_j+t), Q_c(t)=sum c_j(x_j+t)f(x_j+t), and
V[c]=2 Re integral_0^infinity conjugate(P_c) Q_c dt.

The circle has length and measure one. L=-(1/(4 pi)) d^2/dr^2 has eigenvalues
lambda_n=pi n^2, periodic operator domain H^2 and form domain H^1.
Its heat trace Theta(u)=1+2 sum_{n>=1} exp(-pi n^2 u) yields exactly
Phi(x)=exp(x/2)[2u^2 Theta''(u)+3u Theta'(u)], u=exp(2x).
The Poisson normalization agrees with [DLMF 20.7.32](https://dlmf.nist.gov/20.7.E32)
at z=0 and tau=iu: sqrt(u) Theta(u)=Theta(1/u).

Change time to u=exp(2t), using BOTH half-density ports
p_c(u)=P_c(log(u)/2)/sqrt(2u), q_c(u)=Q_c(log(u)/2)/sqrt(2u).
This preserves the integral pairing, including its Jacobian.
The tested class has a fixed b in H^{-1}, fixed d>=0, and terminal dynamics

    psi'=L psi-b q, psi(infinity)=0, p_tilde=b*psi+d q.

Here collocated means that the same b injects and reads out through its adjoint.
The modal solution is psi_n(u)=b_n integral_0^infinity exp(-lambda_n s)q(u+s)ds.
The full H^{-1} summability condition is
sum |b_n|^2/(1+lambda_n)<infinity. For each input row, bounds on q and q'
by M exp(-eta u) control the solution, form energy and all required limits.
Constants may depend on the row; no uniform-in-rank bound is claimed.

The nonnegative terminal energy is

    E(u)=||psi(u)||^2 + 2 integral_u^infinity (l[psi(v)]+d|q(v)|^2) dv,
    E'(u)=-2 Re(conjugate(p_tilde(u))q(u)), E(infinity)=0.

All mixed coefficient terms remain inside these squares. The accumulated
dissipation is essential: dropping it breaks the identity. The point port
b=delta_0-1 is admissible in H^{-1}, though not in L^2. Its mean-zero Green
function is 2 pi(r^2-r+1/6), with spatial derivative jump -4 pi. The full
Green balance includes both this port term and the mean correction.

This is a positive energy for the MODEL output p_tilde. It is not an energy
identity for the original V unless the original supply is reproduced.

## 3. Why the transfer fails on the complete source

For b=delta_0-1, d=0, one actual node x=-2, coefficient 1, physical time t=0,

    P_tilde(0) <= -exp(-2 pi-(pi/2)exp(4))/(2A) < 0 < P(0)=f(2).

The proof retains the whole positive tail. In heat time, the interval [2,3]
supplies a negative contribution of magnitude at least
N=A^{-1} exp(-2 pi-(pi/2)exp(4)); the remaining negative region is discarded
only in an upper bound. All positive contributions above u=exp(4) are bounded
by B with B/N<1/128<1/2. No numerical quadrature or first-mode substitution
establishes the sign. The actual derivative-supply residual is also strictly
negative, since Q(0)=-2f(2): it is at most -4f(2)^2-2f(2)N.
Meanwhile the original diagonal V(-2,-2)=2 integral_2^infinity v f(v)^2 dv
is positive. This is not a negative witness for V.

The report exhausts the stated fixed class. With no zero mode and d=0,
the least occupied positive eigenvalue makes the negative patch dominate
the entire positive tail for sufficiently large negative x. With a zero
mode, a positive term proportional to exp(R) dominates the remaining O(R)
bound at x=-R and gives a different, excessive output. For d>0, positive
x>max(1,1/d) gives P_tilde>=dx f(x)>f(x). The zero port with d=0 gives zero
output. Stronger singular ports outside H^{-1} have divergent output and
Dirichlet energy on a positive actual source input; unproved renormalizations
are not part of this ordinary positive-energy class.

The accepted exclusion therefore covers this fixed circle generator, exact
heat-time convention, fixed collocated H^{-1} ports and nonnegative d.
It does not exclude another generator, time-varying or noncollocated ports,
another positive metric, or every source-derived energy. None of those is
thereby supplied or recommended as a proved repair.

## 4. Parent reproduction and mathematical limits

The parent extracted the two Python blocks unchanged, materialized all seven
source files from their pinned Git objects, and ran both blocks with Python
3.14.7. Both exited zero with byte-identical stdout:

| Block | Script SHA256 | Reproduced stdout SHA256 |
|---|---|---|
| Appendix A | `210bc73644be358036d05bf70df78b6e62faad2d0d932a7230e1a603bec851cc` | `00e8071a67abd9dc9cbd68605aa118c69a389fedef9c8ad4522ba5a33c531aaf` |
| Appendix B | `030ee19f118375749890de0899271ed3d6b8557c288e8a09af210dfcd116afaa` | `0bd5b810ec61dae70c48452747538cf333c73d3c3eeb55c5e25d395a8a1923e2` |

Appendix C also matches its stated SHA256
`97ea70c007c8b45c83f71f9c9404823f21525027003d32018472f497cb5ad0d4`.
Appendix A is exact rational calibration and deliberately wrong test cases;
Appendix B is byte provenance. Neither substitutes for the analytic proof.
Ephemeral replay files are retained outside the repository under
`sourceenergy_parent_replay/` in the parent task's artifact directory.
No new theta evaluation, quadrature, rank sweep or Lean run was performed.

The complete source has a nonzero leading heat amplitude, while negative
Gaussian deformations lose it. This distinguishes the source from those
controls; it does not prove the required sign. Rewriting V as the positive
model energy plus an uncontrolled residual leaves the original sign problem.

## 5. Consequence for the active task

Accept the positive model/Green lemma and the named-class exclusion only.
Do not retry fixed positive spectral weights of this same model. Reopening
requires a proof error or an explicit model outside the class with a new
justified Green identity and matching of the original source supply.
The previous fixed two-channel RF remains excluded; no negative V witness,
full IC/ODD2 result, RH proof or refutation follows from this intake.

After this one completed intake, historical source-sign no-delta count is
8 (previously 7); completed attempts since the latest explicit owner resumption
are 2 (previously 1). Download, reproduction and publication are not separate
attempts. A new analogy does not reset those counts. The full RH goal remains
active, with the original three-repeat owner-brainstorm boundary preserved.
