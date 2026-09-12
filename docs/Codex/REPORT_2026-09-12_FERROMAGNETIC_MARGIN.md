# A necessary coupling condition for an actual-Phi spin construction

STATUS: ACCEPTED_PAPER_DIAGNOSTIC_WITH_EXPLICIT_EXTERNAL_THEOREM.
Independently reviewed by /root/sibling5_check and parent checked.
Production status: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated owner-authorized
PAPER audit, with no canonical theorem/consumer admission. This neither
constructs Phi nor provides the full source sign. Source-sign counter remains 2.
RH, global IC, global ODD2 and all-order Hankel positivity remain OPEN.
LYGSPHI was already generating; this diagnostic was not sent into the busy chat.

## External input and exact coordinate map

Brad Rodgers and Terence Tao, *The De Bruijn–Newman constant is non-negative*,
arXiv:1801.05914v5, 3 July 2021, https://arxiv.org/pdf/1801.05914.
Fetched PDF: 503405 bytes, SHA256
376bb2c1ab941cd5b035546835c5481f2d026767b8e830a48cd5565114a1ec91.
Read scope: first three PDF pages; equations (1)–(4) on p.2 visually checked.
Theorem 1, p.3: “One has Λ ≥ 0.” The threshold statement on p.2 says
H_t has only real zeros exactly for t>=Λ. This published theorem is an
explicit external input; its 61-page proof was not independently audited
or formalized here. This note verifies the source-specific deduction below.

Distinguish their kernel Phi_RT from ours. The theta series gives exactly

    Phi(x) = 2 Phi_RT(x/2).

For real a let Z_a=int_R exp(a x^2)Phi(x)dx>0 and
p_a(x)=exp(a x^2)Phi(x)/Z_a. All these integrals and their entire transforms
exist by the already proved actual-source super-exponential tails. With
the paper's H_t, evenness and x=2u give

    M_a(h) = int_R exp(hx)p_a(x)dx
           = H_(4a)(2ih)/H_(4a)(0).

In particular, for every epsilon>0, M_(-epsilon) has a zero off Re h=0:
H_(-4epsilon) cannot have only real zeros since -4epsilon<0<=Λ.
No numerical value of a positive upper bound for Λ is used.

## Claim: no fixed removable ferromagnetic pair component

Suppose P_N is a finite zero-field pair-Ising law proportional to
exp(sum_(i<j)J_(ij,N)sigma_i sigma_j), with J_(ij,N)>=0 and q_(i,N)>0.
Let X_N=sum_i q_(i,N)sigma_i, and suppose law(X_N) converges weakly to
our p=p_0. Then there cannot be an infinite subsequence with

    J_(ij,N) >= 2 epsilon q_(i,N)q_(j,N) for every i<j,       (R)

for any fixed epsilon>0. Define delta_N=0 for systems with fewer than two
spins, and otherwise delta_N=min_(i<j) J_(ij,N)/(2 q_(i,N)q_(j,N)). Then

    delta_N -> 0.

Missing edges count as J=0. Thus sparse or heterogeneous constructions
are not excluded; the claim forbids a fixed positive all-pair component,
not every ferromagnetic realization or every notion of physical stability.

## Proof

Assume (R) on an infinite subsequence, and restrict to it. Tilt P_N by
exp(-epsilon X_N^2), with normalizer c_N=E_N exp(-epsilon X_N^2)>0.
Since sigma_i^2=1, the new off-diagonal pair coefficients are precisely

    J'_(ij,N)=J_(ij,N)-2 epsilon q_(i,N)q_(j,N)>=0.

The diagonal term is a configuration-independent constant and cancels in
normalization. There are no added fields or higher-body interactions.
For Re h>0, the microscopic fields h q_i have strictly positive real part.
Finite multivariate Lee–Yang and spin-flip symmetry therefore make

    F_N(h)=E_N exp(-epsilon X_N^2+hX_N)/c_N

zero-free in both open half-planes.

Weak convergence alone suffices for the limit of these tilted transforms:
x -> exp(-epsilon x^2+hx) is bounded and continuous on R for each h in C,
and x -> exp(-epsilon x^2) is bounded and continuous. Thus
c_N->c=int exp(-epsilon x^2)p(x)dx>0 and F_N(h)->M_(-epsilon)(h).
For each fixed R, exp(-epsilon x^2+R|x|) and
|x|exp(-epsilon x^2+R|x|) are bounded uniformly over real x. These bounds
and eventually c_N>=c/2 give local uniform boundedness and equicontinuity
of F_N. A finite-net argument upgrades pointwise to uniform convergence
on every compact h-disk. No uniform exponential moments of the un-tilted
X_N are assumed in this particular argument.

Hurwitz on each open half-plane gives zero-freeness of the limit there;
the limit is nonzero on the real axis because its integral is positive.
This contradicts the external consequence for M_(-epsilon) above.
If delta_N did not tend to zero, some positive epsilon would satisfy (R)
along an infinite subsequence, proving the final assertion.

## Consequence for the construction search

Adding exp(a X_N^2), a>=0, changes pair coefficients to
J_(ij,N)+2a q_i q_j and preserves ferromagnetism. Going backward subtracts
this component and needs an entrywise bound. A model for p_a, a>0, with
exact removable component 2a q_i q_j could still lead to p_0; that boundary
case is not excluded. A fixed additional positive margin beyond it would
instead reach some p_(-epsilon) and is impossible under the same limiting
argument. Do not assume a robust margin merely because some couplings
are positive. This constraint does not produce the boundary construction.

Application is limited to the actual Phi and the stated class of weighted
pair-Ising approximations. It does not supply a full negative K/Hankel
witness, prove RH false, or change the open status of global IC/ODD2/RH.
Existing local source pin: REPORT_2026-09-12_PHYSICS_BROTHER_LEE_YANG.md,
SHA256 cbfa295fa3778dbf2375a5892b3caad0d4b381e3784727bcc187dd909764d5ed;
its exact normalization and theta series are the inputs to the coordinate map.

## Independent review and parent intake

The candidate (5,119 bytes / 103 LF) was reviewed at SHA256
ea74adec8156799cf65a92c649bac7016daa3518c12b46f1e48c69f4b36314ba.
Parent read the full candidate, full review receipt, the cited first three
Rodgers--Tao pages and the exact accepted source dictionary; the source formula
on PDF p.2 was visually checked. Parent verified the rescaling, coupling
subtraction, subsequence argument and compact convergence proof.
The only mathematical wording change on intake makes delta_N explicit for
systems with fewer than two spins, as requested by the reviewer.
Neither reviewer claims to have audited the entire Rodgers--Tao proof.

Receipt SHA256: d4588f53ad43129814e618639bd18c57dabe30687d929c08047ec8e85e100d40.
The complete receipt follows, quoted as review evidence:

> # Independent review receipt: ferromagnetic margin
>
> **Verdict:** `ACCEPTED_PAPER_DIAGNOSTIC`, contingent on the explicitly named
> external Rodgers--Tao theorem. It is not source-sign progress or a construction
> of the actual source.
>
> Reviewed candidate: `FERROMAGNETIC_MARGIN_CANDIDATE_20260912.md`, 5,119 bytes,
> 103 LF, final LF, no CR, SHA-256
> `ea74adec8156799cf65a92c649bac7016daa3518c12b46f1e48c69f4b36314ba`.
> The local Rodgers--Tao PDF hash is
> `376bb2c1ab941cd5b035546835c5481f2d026767b8e830a48cd5565114a1ec91`.
>
> The coordinate calculation is correct: \(\Phi(x)=2\Phi_{RT}(x/2)\), hence
> \(M_a(h)=H_{4a}(2ih)/H_{4a}(0)\), using evenness of \(H_t\). The external
> threshold theorem \(\Lambda\ge0\) consequently gives an off-imaginary-axis
> zero of \(M_{-\epsilon}\) for every \(\epsilon>0\). The all-order result is
> an external published input; its proof was not reverified here.
>
> The tilt calculation is exact: multiplication by \(e^{-\epsilon X_N^2}\)
> replaces every off-diagonal coefficient by
> \(J_{ij,N}-2\epsilon q_{i,N}q_{j,N}\); diagonal terms are constant. Under the
> fixed entrywise margin this remains a zero-field ferromagnetic pair-Ising
> law. Weak convergence alone suffices after the negative Gaussian tilt:
> \(e^{-\epsilon x^2+hx}\) and its first \(h\)-derivative are bounded on each
> compact \(h\)-disk. Thus pointwise weak convergence, compact equicontinuity,
> and Hurwitz on the two full half-planes yield the stated contradiction without
> un-tilted uniform exponential moments.
>
> The theta asymptotic is also correct: its leading \(n=1\) term is
> \(4\pi^2 e^{9x/2-\pi e^{2x}}(1+o(1))\), so the ready quartic construction is
> not the actual source. This does not exclude sparse, heterogeneous, or general
> Griffiths--Simon constructions, nor a sharp removable construction for
> \(p_a\to p_0\).
>
> Minor formulation boundary: define \(\delta_N\) only along indices with at
> least two spins (or explicitly set it to zero otherwise). The margin conclusion
> is exactly a no-fixed-positive-all-pair-component result, not a no-GS theorem.
> No counter, admission, or RH status changes.
