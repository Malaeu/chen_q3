# PSD-pd operator plan alignment with Q3

## Purpose

This note records the conceptual bridge behind the PSD-pd route, so future
sessions can return to one stable explanation of:

- where the old operator plan went;
- where the finite interval certificates live;
- how the block is intended to connect back to `Q3.Main`.

## The old operator idea

The original working picture was:

\[
\text{Arch operator} - \text{Prime operator}.
\]

In the finite PSD-pd certificate engine this is now:

\[
C=A-P.
\]

Here:

- \(A\) is the Arch matrix, the finite matrix for the Gamma/Archimedean
  contribution;
- \(P\) is the Prime matrix, the finite matrix for the prime-side contribution;
- \(C=A-P\) is the finite Weil matrix to be proved positive on the
  boundary-null finite packet space.

The better-conditioned version is the kappa split:

\[
C=(A-\kappa P_0)-(P-\kappa P_0).
\]

That is:

\[
R_\kappa=A-\kappa P_0,
\qquad
D_\theta=C-\theta R_\kappa.
\]

The finite proof target is:

\[
D_\theta+\tau Q^TQ\succ0,
\qquad
R_\kappa+\tau Q^TQ\succ0.
\]

This is the penalty guard. It proves positivity on \(\ker Q\) without
certifying a numerical nullspace basis.

## The old "one line" geometry

The earlier geometric idea was that the right function space should force the
zero-detecting geometry onto the critical line.

In the current architecture this appears as two layers:

1. the corrected positive-definite cone;
2. the boundary-null packet space.

The corrected positive-definite cone is the Hermitian-square / autocorrelation
side of the Weil criterion. On the critical line, transforms appear as

\[
|H(i\gamma)|^2.
\]

The boundary-null packet space imposes:

\[
H(1/2)=H(-1/2)=0.
\]

At finite level this is:

\[
Qv=0.
\]

Thus the finite certificate proves:

\[
Qv=0
\Rightarrow
v^T(A-P)v\ge0.
\]

The exhaustion layer then explains how finite boundary-null packet tests can
approximate all boundary-null tests in the selected analytic class.

## Full Q3 route

The full public corrected-cone route is:

```text
T0 / normalization
→ T0.1 target-cone audit
→ T0-pd corrected positive-definite cone
→ A1-pd density of the packet/autocorrelation family
→ packet-Rayleigh-pd finite quadratic-form identity
→ PSD-pd finite certificate engine
→ A2 closure on the corrected local cone
→ LF-pd lift from local cones to the global cone
→ G6 / Weil linkage
→ RH
```

The current work is inside the central node:

```text
PSD-pd finite certificate engine
```

It is not the beginning of the proof. It sits after normalization,
target-cone selection, density, and packet-Rayleigh identification, and before
closure and global RH linkage.

## What is already closed

### Finite interval block

Steps 18--22 produced a finite interval-backed block:

\[
A,\ P,\ P_0,\ Q.
\]

Each matrix is represented by a midpoint/radius contract.

### Finite penalty certificate

Steps 24--26 produced the Lean-facing finite certificate layer:

```text
FinitePenaltyCert D R Q
```

This proves finite coordinate positivity on `ker Q`.

### Directed-family and exhaustion skeleton

Steps 27--30 produced:

- `DirectedCertFamily`;
- algebraic boundary-null correction;
- convergence of corrected approximants;
- boundary-null sequential exhaustion from ordinary density plus correction
  stability.

### Matrix-to-Weil receiver

Step 31 produced:

```text
FiniteWeilMatrixModel
CertifiedFiniteWeilModel
```

This proves:

\[
\texttt{FinitePenaltyCert}
+
\texttt{matrix identification}
\Rightarrow
\text{finite analytic Weil positivity}.
\]

Concretely:

\[
\operatorname{WeilForm}(\operatorname{synth}(v))=v^TCv
\]

and analytic boundary vanishing implies:

\[
Qv=0.
\]

Then:

\[
0\le \operatorname{WeilForm}(\operatorname{synth}(v)).
\]

The strengthened form is also exposed:

\[
\theta\,v^T Rv
\le
\operatorname{WeilForm}(\operatorname{synth}(v)).
\]

## What is not yet closed

The concrete B-spline matrix identification is still open.

Step 32 must prove that the actual spline-packet matrices are the analytic
entries:

\[
h_v=\sum_j v_j\psi_j,
\]

\[
\mathcal W(h_v)=v^T(A-P)v,
\]

\[
Qv=(H_v(1/2),H_v(-1/2)).
\]

This is the point where the interval-backed CSV/matrix block becomes a real
finite analytic Weil positivity theorem.

## How this will connect to `Q3.Main`

Current `Q3.Main` still exports the older compiled broad route:

```text
Q_nonneg_t_critical
→ CompatibilityReduction
→ PaperMainlineAtomRoute
→ RH_of_Weil_and_Q3
→ RH
```

That route still depends on project-side positivity input.

The PSD-pd block is intended to replace the positivity source, not to be
inserted prematurely into `Q3.Main`.

The future integration shape should be:

```text
PSD-pd finite analytic positivity
→ directed family / boundary-null exhaustion
→ positivity on the corrected positive-definite Weil cone
→ G6 / Weil linkage
→ RH
```

Only after that route is theorem-complete should `Q3.Main` be rewired from the
old broad positivity source to the PSD-pd corrected-cone positivity source.

## Current exact location

As of Step 31, the project is here:

```text
interval-backed matrices          closed
FinitePenaltyCert                 closed
boundary-null correction          closed
boundary-null exhaustion shell     closed
matrix-to-Weil receiver            closed
B-spline matrix identification     next
directed family instantiation      later
global corrected-cone positivity   later
Q3.Main rewiring                   later
```

## Short operational rule

Do not jump directly into `Q3.Main`.

First close:

```text
Step 32:
  concrete B-spline matrix identification.

Step 33:
  connect finite analytic positivity to directed family and Step 30 exhaustion.

Step 34:
  produce global boundary-null / corrected-cone Weil positivity.

Step 35:
  rewire `Q3.Main` through the PSD-pd route.
```

## Summary

The old operator plan was not lost. It has been compressed into the finite
certificate architecture:

\[
\text{Arch} - \text{Prime}
\quad\leadsto\quad
C=A-P.
\]

The old "one line" geometry is represented by:

\[
\text{corrected positive-definite cone}
+
\text{boundary-null packet exhaustion}.
\]

The PSD-pd block is the central constructive positivity engine in the Q3
corrected-cone route. Once Step 32 and the family/exhaustion instantiations are
closed, this block can replace the current broad-route positivity source in
`Q3.Main`.
