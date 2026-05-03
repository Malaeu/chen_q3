# Step 31 — Matrix identification shell

## Goal

Bridge the interval-backed finite matrix certificates to the analytic Weil/PSD
form.

Steps 18--22 certify finite matrices. Steps 24--30 provide the penalty
certificate receiver and boundary-null exhaustion. Step 31 supplies the missing
theorem-facing port:

\[
\text{finite matrices}
\Rightarrow
\text{analytic Weil positivity on synthesized finite tests}.
\]

## Lean file

`Q3/Proofs/PSD_MatrixIdentification.lean`

## New objects

- `FiniteWeilMatrixModel`
- `CertifiedFiniteWeilModel`

## Main contract

For a finite coefficient vector \(v\), a synthesis map produces an analytic
test:

\[
h_v=\operatorname{synth}(v).
\]

The concrete finite block must eventually prove:

\[
\operatorname{WeilForm}(h_v)=v^T C v
\]

and analytic boundary vanishing implies the matrix boundary constraint:

\[
H_v(1/2)=H_v(-1/2)=0
\Rightarrow
Qv=0.
\]

## Main theorem payload

Given:

- `FinitePenaltyCert D R Q`;
- the split identity

\[
v^T C v = v^T D v + \theta v^T R v;
\]

- `FiniteWeilMatrixModel C Q`;

the file proves:

\[
\operatorname{WeilForm}(h_v)\ge0
\]

for synthesized analytic boundary-null vectors.

It also exposes the strengthened form:

\[
\theta\,v^T Rv\le \operatorname{WeilForm}(h_v).
\]

## Meaning

Step 31 does not prove the concrete B-spline integral formulas. It creates the
exact Lean port where those formulas must land.

This is the missing bridge between:

\[
\text{interval-backed matrix certificate}
\]

and

\[
\text{analytic finite-packet Weil positivity}.
\]

## Remaining blocker

Step 32 should instantiate `FiniteWeilMatrixModel` for the actual B-spline
packet block:

- synthesis \(v\mapsto \sum_j v_j\psi_j\);
- Arch matrix \(A\);
- prime matrix \(P\);
- boundary matrix \(Q\);
- identity \(C=A-P\) represents the Weil/PSD form.

## Verdict

Step 31 closes the abstract matrix-to-Weil consumer. The next work is no longer
finite certificate algebra, but concrete formula identification for the chosen
B-spline packet model.
