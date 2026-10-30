# DIAGONAL: source moment bound and remaining signed comparison

Status: bounded PAPER identities and controls accepted; T and RH OPEN.
Original verdict byte-preserved. All 615 lines read by root.
GitHub delivery succeeded: f7a8ff0a, one authorized new verdict path only;
ordinary fast-forward from 4c32496c. This verifies present Proshka write ability.
Verdict SHA256: fc416d24e9c20fa27b0d5500dbfe6d789803aea2f6bafaae066a4d436e64f130.
Request SHA256: 7938daaaa4a0aa8e79bf4eb8113abc3df7eea5d47f37ec33947bcf0604bda4d8.
Appendix extracted verbatim to ../thetagrade_2026-10-28/diagonal_proshka_algebra.py;
SHA256 ecddacbb8d4cf027b5a97c1a45229e550b8c8b3934a8e4f5cfa1c5448d21110f matches.
`uv run --with sympy python .../diagonal_proshka_algebra.py` passed exactly.
Repository .venv lacks SymPy; existing uv environment replay succeeded without
changing repository dependencies. This algebra replay is not an analytic proof.
Independent read-only review of Lemmas5–9 found no algebraic, sign,
normalization or carrier defect, conditional on the pinned source identity
and accepted CONFINE density / BOUNDARY finite-record lemmas.

## Mathematical contribution and limits

The source diagonal identity retains endpoint cosine cancellation and both
Loewner and defect pieces. A positive damped source measure gives

    (Delta_r² delta(t))²+4pi²(Delta_r² beta_J(t))² <=4D(r)².

At r=t=1 the strict deficit is at least L²m^(-3/8)/288. Its proof uses two
archimedean intervals and nonnegative pair integrands, so adding positive
atoms preserves the bound. This is a source-moment constraint, NOT matrix PSD.
It does not apply automatically to signed eigenvector-weighted U,V.

The new competitor keeps the actual diagonal: for unit stationary c, choose
coordinate k and real resolvent z, y=R_z c, and write

    a=A_kk-lambda, b=d_k(F_k V-U)/(x_k-z), q=VU'-UV'.

If a>0 and aq-b²<0, w=b e_k-a y and g=w/||w|| satisfy
energy(g)-lambda=a(aq-b²)/||w||²<0 in the original even carrier.
Negative numerator ensures w is nonzero. No projection-return cost is hidden.
Other a=0/a<0 branches are retained in the verdict. Exact minimality requires
this Gram matrix to be PSD; stationarity alone merely supplies its formulas.
Trial corrections are r_k/(x_k-z) and sum c_i r_i/(x_i-z)². A small residual
does not pay a strict margin without comparison at that margin's scale.

Escape yields L^(3/2) V_ctr(-(alpha L/2pi)²)->0, alpha>0 fixed,
with V_ctr carrying (-1)^i. The uncentered boundary moment V cannot replace it.
No rate, sign, or positive mixed-response lower bound follows merely from this.
The missing input is an independently derived source separation in (7.1),
not the determinant's negative sign renamed as a new assumption.

Reciprocal positive-jump pairs change only the sampled diagonal. The explicit
large-weight deformation produces simple exact escaping bottoms, but changes
the arithmetic measure and destroys theta radicality. It restricts enlarged
positive-source arguments only; it neither refutes literal CCM nor NOESCAPE.

## Semantic hunt connection and continuation

NOESCAPE_THRESHOLD_ALIAS_HUNT records primary threshold-binding and higher-order
selection mechanisms. They reinforce the need to compare the complete signed
correction with every localization/return cost; no uniform gap is necessary.
CONFINE (5.1) already identifies exact radical leakage energy k[e_i,e_j], not
ordinary tail mass. A finite radical Ritz minimum is not the full-sector minimum.
Any proposed barrier must be centered at the finite-carrier lambda_m itself;
an ambient lower bound leaves a lambda_m-E excess even on an exact bottom.
Spatial retention additionally requires local compactness/jet observability.

Next bounded source task: compare the actual prime cosine channel and theta
radical leakage, testing either the mixed-response budget or a full-source
barrier against escaping radical controls. Other competitors and growing
moment estimates remain OPEN. No new Proshka question has been sent.

Independent review of Lemmas2,4 reproduced the strict disk constant,
100m² source norm budget, reciprocal diagonal perturbation, spectral gap
and fixed-jet escape. No substantive defect found. Wording qualification:
nu has infinite mass near zero, not an atom of infinite mass at zero.
Both reviews are bounded PAPER checks, not Lean or a completed RH proof.
