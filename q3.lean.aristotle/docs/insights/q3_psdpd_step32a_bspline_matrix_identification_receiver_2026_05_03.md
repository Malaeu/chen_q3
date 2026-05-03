# Step 32A — B-spline matrix identification receiver

## Goal

Instantiate the Step 31 matrix-to-Weil port at the level of B-spline packet
entry identities, without yet proving the special-function / integral formulas.

Step 31 supplied:

\[
\texttt{FinitePenaltyCert}
+
\texttt{FiniteWeilMatrixModel}
\Rightarrow
\text{finite analytic Weil positivity}.
\]

Step 32A supplies the receiver that turns concrete B-spline entry hypotheses
into a `FiniteWeilMatrixModel`.

## Local search synthesis

Queries against `q3_docs`:

- `B-spline packet matrix identification WeilForm`
- `packet-Rayleigh-pd finite quadratic form identity`
- `boundary rows H(1/2) H(-1/2) spline packet`
- `Arch matrix prime matrix A P B-spline packet`

Relevant hits:

- `PROJECT_ORCHESTRATOR.md`: the corrected route is
  `A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`.
- `full/sections/Weil_pack.tex`: `packet-Rayleigh-pd` is the exact Toeplitz
  quadratic-form identity on autocorrelation packets, and `PSD-pd` is the
  positive-semidefinite packet-kernel theorem feeding the corrected cone.
- `full/sections/Main_closure.tex`: the live task is PSD of the packet kernel
  on the exact dense autocorrelation packet family, not the overlarge naive
  Rayleigh family.
- `full/sections/A3/rayleigh_bridge.tex`: Toeplitz/Rayleigh identities are
  already handled as finite quadratic-form receivers; Step 32A should mirror
  this pattern for the B-spline packet matrix block.

External sanity check only confirmed standard background:

- centered/cardinal B-splines have sinc-power Fourier transforms;
- Toeplitz quadratic forms are represented by finite Fourier-coefficient
  matrices;
- Weil positivity is naturally phrased via positive-definite test functions.

No external result changes the local theorem shape.

## Receiver contract

For a finite B-spline packet model, assume:

\[
h_v=\sum_j v_j\psi_j.
\]

Entry hypotheses:

\[
\mathcal A(h_v)=v^TAv,
\]

\[
\mathcal P(h_v)=v^TPv,
\]

\[
\mathcal W(h_v)=\mathcal A(h_v)-\mathcal P(h_v),
\]

and boundary rows:

\[
H_v(1/2)=0,\ H_v(-1/2)=0
\Rightarrow
Qv=0.
\]

Then with

\[
C=A-P
\]

the B-spline packet data instantiate `FiniteWeilMatrixModel C Q`.

## Lean target

Create:

`Q3/Proofs/PSD_BSplineMatrixIdentification.lean`

Expected objects:

- `BSplinePacketEntryData`
- `BSplinePacketMatrixIdent`
- constructor theorem to produce `FiniteWeilMatrixModel`
- optional packaged constructor for `CertifiedFiniteWeilModel`

Implemented objects:

- `BSplinePacketEntryData`
- `BSplinePacketEntryData.weil_ident`
- `BSplinePacketEntryData.toFiniteWeilMatrixModel`
- `CertifiedBSplinePacketBlock`
- `CertifiedBSplinePacketBlock.toCertifiedFiniteWeilModel`
- `CertifiedBSplinePacketBlock.weil_nonneg_on_analyticBoundary`
- `CertifiedBSplinePacketBlock.weil_ge_theta_R_on_analyticBoundary`

Verification:

- `lake env lean Q3/Proofs/PSD_BSplineMatrixIdentification.lean`
- no matches for `sorry|admit|exact?`
- `python3 scripts/check_links.py --root .`

## Meaning

Step 32A does not prove:

- the B-spline transform formula;
- the autocorrelation formula;
- Arch integral entries;
- prime-shift entries.

It creates the exact receiver where those facts must land.

## Next blocker

Step 32B should prove the concrete B-spline formula layer:

\[
H_j(z)=\sqrt{\ell}\,e^{zu_j}E_{\ell,k}(z),
\]

\[
\langle\psi_j,S_a\psi_i\rangle
=
r_k((u_j-u_i-a)/\ell),
\]

and then derive the actual Arch/Prime/Boundary matrix entries.
