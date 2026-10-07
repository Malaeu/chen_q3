# CCM Q1 own followup: full-credit return and spectral commutation

2026-10-07. Same full CCM family and SP consumer; no new Pro message.
Source: PROSHKA_VERDICT_FULL_CCM_COUPLED_MOMENT_DRIFT_Q01.md §§4–7.
This bounded algebra attempt supplies no new arithmetic estimate.

Let E=delta K=delta B-delta C, H_t=padK_m+tE,
G_t=(H_t)_-^(p-1), D_t=diag((-H_t,jj)_+^(p-1)),
T=integral_0^1(G_t+D_t)dt, Y=Tr(H_-^p)+sum_j(-H_jj)_+^p.
Keep eps=5000/(m logm), Xi=Tr(T delta C), Gamma=Tr(T(delta B+eps I)).
Then exactly

    Xi-Gamma = -Tr(T E)-eps Tr T
             = (Ynew-Yold)/p-eps Tr T
             = (Znew-Zold-2)/p-eps Tr T.

Thus evaluating the full background credit by substituting K returns the
original endpoint moment increment. It is a valid weaker sufficient
interface, but not an additional signed supplier. A proof of its bound
would still be useful; the identity alone does not prove it.

For any skew-Hermitian A_t, spectral commutation gives

    Tr(G_t [A_t,H_t])=0.

If E=[A_t,H_t]+R_t, the exact derivative consequently yields

    delta Y=-p integral Tr(G_t R_t+D_t E)dt.

The diagonal account cannot be silently included in that cancellation.
Exact real control at p=4:

    H=[[-1,1],[1,1]], A=[[0,1],[-1,0]], D=diag(1,0),
    [A,H]=[[2,2],[2,-2]], Tr(D[A,H])=2.

This control is not the actual CCM matrix. It discriminates between spectral
functional calculus and a fixed-basis diagonal account. In an eigenbasis
of H the diagonal of [A,H] is zero, so a unitary gauge cannot remove the
eigenvalue-changing diagonal of E. Degenerate eigenspaces likewise retain
their whole within-eigenspace compression. Those pieces remain in R_t.
No source-specific signed bound on their G_t-weighted contraction follows.

Read-only independent algebra check by moment_compensation_map: PASS on
full-credit sign/dimension return, commutator trace, and exact 2x2 control.
Root source crosswalk retains every endpoint and the original full path.
Shelf query ./ask.sh 'spectral shift trace commutator virial' returned
ASK_STATUS: INCOMPLETE (semantic-index freshness), not absence.

Next concrete question in the same Pro phase: derive a source-specific
bound on the eigenvalue-changing residual, or on the equivalent signed
adaptive prime-pole contraction, with all new-mode credits and interfaces.
No generic unitary invariance or full-credit substitution counts as a gain.
SP/RH OPEN. This does not kill the source family or a genuinely arithmetic
cancellation mechanism.
