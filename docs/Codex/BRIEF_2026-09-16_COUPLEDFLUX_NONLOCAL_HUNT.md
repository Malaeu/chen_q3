# Bounded semantic return: nonlocal coupling and the physical flux

STATUS: SEARCH_BRIEF_ONLY; NO_NEW_SIGN_RESULT.
Source base: f1bf24224bda288181ece38ee0d32e26c21b5a4d.
One object: a nonlocal treatment of the exact coupled differential block
that accounts for the original norm, its k derivative and the X=0 boundary.
This is exploratory discovery, not a formal consumer admission or a new
Proshka dispatch. Canonical production HOLD remains untouched.

## Source pins and exact target

Full response: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_COUPLEDFLUX_2026-09-16.md
at 4a4575555554947d3db865819ee74652f9ec7639, SHA256
258fe6d40ab6b92b4c7a5645fb75ad5dadecd7848a7567e18c0553a65b28b0c4.
Accepted intake: docs/Codex/REPORT_2026-09-16_COUPLEDFLUX_INTAKE.md,
SHA256 79b56d8acadf8efcb4502cebd1d989d746c72b57aa0e57ed2f68c1a9ff0de45e.
Original ladder: docs/Codex/REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md
L11-L12, SHA256 feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21.

For every finite complex row c with x_i in I=(-log(2)/2,0), the unchanged
full source gives U_(alpha,k)=sum c_i exp[-2k(X+x_i)]Phi_alpha(X+x_i),
Phi_alpha(x)=exp(5x/2)r_alpha(exp(2x)), r_alpha=r_2^{*(alpha/2)}.
Here X>=0, k is a real parameter, and alpha=2,4 in the block.
The consumer is only

 A^2 V[c]=-E_c'(0)/2>=0,
 E_c(k)=int_0^infinity |U_(2,k)|^2 dX, A=||Phi_2||_2.

No positive fraction of an auxiliary energy, all-k dissipation, or simple
zeros are required. No operator is allowed to be defined using an assumed
positive square root of V.

With Y_(alpha,k)=exp((alpha+2k)X)U_(alpha,k), CF16 reads

 L_tilde (Y_(2,k),Y_(4,k))^T
 = (2pi(D-5/2)R_(2,k),
    20exp(-2X)Y_(6,k)+8pi(D-9/2)R_(4,k))^T,
 L_tilde=A_0 I_2-6exp(-2X)N,
 A_0=D^2-1/4, N=[[0,1],[0,0]], D=partial_X,
 R_(alpha,k)=exp((alpha+2k)X)U_(alpha,k+1).

Both forcing entries stay; Y6 is not a new independent sign target.
Physical norm: E_c(k)=int exp(-(4+4k)X)|Y_(2,k)|^2 dX.
Actual X=0 traces are fixed by the same finite row. All source fields and
their displayed derivatives have the full-source superexponential infinity
bound CF4. The parameter k also changes the row by diag(exp(-2kx_i)).

## What has been proved and must not be repeated

CF20-CF21: every C2 local Hermitian multiplication symmetrizer of L_tilde
is constant, must satisfy HN=N*H, and a positive semidefinite one is
diag(0,d). No positive definite such H exists. This is only a local formal
ansatz obstruction, not a no-go for integral operators or source-image forms.
CF12: the full differentiated Green balance is exact but all its signed
terms together are just the original V. CF29: one of its actual mixed
terms R24 has negative finite rows on every real open interval. Dropping
that term or assigning it a positive sign is therefore invalid.

## Explicit control outside the desired operator class

The finite-dimensional matrix N above, without D or the X-domain, cannot
be similar to a Hermitian matrix in any positive metric: HN=N*H forces
H11=0. Thus an abstract claim that every triangular coupling has a positive
symmetrizer fails already on this control. A useful infinite-dimensional
candidate must use the differential operator and its actual domain, not
ignore the Jordan obstruction. The uncoupled N=0 operator is a positive
control for formal symmetry, but is not the full source and not V.

## Two own rewrites used only as UNVERIFIED search hints

R1 — UNVERIFIED AS A CLOSED-OPERATOR / ENERGY MAP:
Try T=[[I,K],[0,I]] and the Sylvester commutator

 [A_0,K]=6exp(-2X),

which would give L_tilde T=T diag(A_0,A_0) at the differential-expression
level. Equal diagonal spectra mean a theorem requiring disjoint spectra
cannot be applied without an additional argument. Formal diagonalization
alone does not preserve a self-adjoint domain or the physical energy.

R2 — UNVERIFIED CANDIDATE FOR A DOMAIN-AND-FLUX TEST:

 (Kq)(X)=(3/2)exp(-X)int_X^infinity exp(-t)q(t)dt.

This explicit Volterra-type hint can be checked directly before any long
construction. The endpoint may change: do not impose Kq(0)=0, identify
boundary domains without proof, or discard the cross term in the first
component of T. No norm identity, dissipative evolution, or V-sign result
is claimed for this candidate. If it only diagonalizes the expression and
leaves the same unpaid physical flux, report that limit and stop this test.

## Three dictionaries and bounded evidence contract

1. Operator: operator Sylvester equation; triangular operator matrix;
   bounded nonlocal symmetrizer with coincident spectra.
2. Differential/integral: Volterra transmutation; Darboux intertwiner;
   Sturm-Liouville domain and boundary preservation.
3. Energy/control: boundary storage identity; source-image energy metric;
   port-Hamiltonian energy balance retaining observation norm.

Start with one registered shelf query per dictionary and inspect returned
exact local evidence. Reuse prior provider errors; no authentication,
subscription, index repair or unchanged retry. If shelf incompleteness
remains, distinguish it from absence. At most one focused external metadata
batch and one best primary theorem body may be inspected in this pass.

Each retained theorem needs a fetched full source/hash, short quote and exact
locator, domain/quantifier mapping, and a test against the Jordan control.
Especially check boundary domains, spectral-separation hypotheses, forcing,
and whether the theorem preserves THIS physical norm and local k-flux.

Stopping result: one applicable sufficient mechanism, one verified partial
analogue with exact unpaid interface, or an INCOMPLETE result with missing
evidence. Do not create another abstract dissipative model, ask for extra
alpha levels, or turn equivalence of auxiliary norms into V positivity.
No source-sign counter reset and no full-V/RH claim.
