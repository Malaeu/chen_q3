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

## Layer-by-layer explanation

### 0. T0 / normalization

This is the entrance layer. It fixes:

```text
Guinand-Weil normalization
sign conventions
boundary terms
tau=0 / centered conventions
```

This matters because a PSD certificate is meaningful only for the exact
quadratic form it certifies. A wrong sign or normalization in the explicit
formula would certify the wrong object.

PSD-pd does not redo T0. It consumes the normalization already selected by the
corrected-cone route.

### 1. T0.1 / target-cone audit

The old broad pointwise cone was too wide for honest Weil positivity.

The route therefore pivots to the corrected positive-definite cone:

```text
W_K^pd / W^pd
```

This is the first structural reason the PSD-pd lane is not merely another
numerical experiment. It is attached to the corrected public target cone.

### 2. T0-pd / corrected positive-definite cone

This layer is the formal version of the earlier "one line" geometric idea.

The cone is built from Hermitian-square / autocorrelation tests. On the
critical line, the transform has the square-modulus shape:

\[
F(i\gamma)=|H(i\gamma)|^2.
\]

Off-critical zeros create the wrong-sign directions; global positivity on the
correct cone forbids those directions.

The boundary-null condition removes endpoint terms:

\[
H(1/2)=H(-1/2)=0.
\]

At finite level this becomes:

\[
Qv=0.
\]

### 3. A1-pd / density

A1-pd says that it is enough to work on a dense packet/autocorrelation family
inside the corrected cone.

Operationally:

```text
prove positivity on a dense finite-packet family
then extend it by closure.
```

This is why the finite PSD-pd certificate engine can be useful for the full
proof: it supplies positivity on the dense family that A1-pd selects.

### 4. packet-Rayleigh-pd / finite form identification

This layer turns analytic packet tests into finite quadratic forms.

At packet level the target shape is:

\[
\mathcal W(h_v)=v^T C v.
\]

With boundary rows:

\[
Qv=(H_v(1/2),H_v(-1/2)).
\]

Step 31 created the abstract Lean receiver for this layer:

```text
FiniteWeilMatrixModel
CertifiedFiniteWeilModel
```

Step 32 must instantiate it for the actual B-spline packet formulas.

### 5. PSD-pd / finite certificate engine

This is the central engine being built now.

Internal chain:

```text
finite B-spline packet basis
→ matrices A, P, P0, Q
→ C = A - P
→ kappa split:
   Rkappa = A - kappa P0
   Dtheta = C - theta Rkappa
→ penalty guard:
   Dtheta + tau Q^TQ > 0
   Rkappa + tau Q^TQ > 0
→ FinitePenaltyCert
→ finite matrix positivity on boundary-null packet coordinates
→ matrix identification
→ finite analytic Weil positivity
```

This is where the old operator picture lands:

```text
Arch operator - Prime operator
```

becomes:

\[
C=A-P.
\]

The better-conditioned proof object is not a naive square root. It is the
kappa-split certificate:

\[
C=(A-\kappa P_0)-(P-\kappa P_0).
\]

### 6. A2 closure

A2 closure is the first upper consumer after PSD-pd.

It does not prove finite positivity. It transfers already-proved positivity
from the dense packet family to the full local corrected cone:

\[
h_n\to h,\qquad \mathcal W(h_n)\ge0
\Rightarrow
\mathcal W(h)\ge0.
\]

Therefore PSD-pd must sit before A2:

```text
PSD-pd proves positivity on packets.
A2 extends it to the local corrected cone.
```

### 7. LF-pd

LF-pd is the local-to-global lift.

It consumes local positivity on every compact window:

\[
\forall K,\quad \mathcal W\ge0\text{ on }W_K^{pd}
\]

and produces:

\[
\mathcal W\ge0\text{ on }W^{pd}.
\]

It should not recompute matrices. It consumes the A2 output.

### 8. G6 / Weil linkage

G6 is the endpoint bridge:

```text
global corrected Weil positivity
→ RH
```

It is an upper consumer, not the current bottleneck of the PSD-pd block.

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

The intended future route-export shape is:

```text
Q3/Proofs/PSDpd_GlobalRoute.lean
```

with theorem-level payloads like:

```text
PSDpd_global_positivity :
  GlobalCorrectedWeilPositivity

RH_of_PSDpd_route :
  RH
```

Then `Q3.Main` can either expose both routes temporarily:

```text
RH_of_old_atom_route
RH_of_PSDpd_route
```

or switch:

```text
theorem RH_of_Weil_and_Q3 : RH :=
  RH_of_PSDpd_route
```

The key point is that the future `Q3.Main` change should be a route switch, not
a rewrite of the whole project.

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

The current mathematical bottleneck is:

```text
Step 32:
  B-spline matrix identification instance.
```

That means proving, for the actual packet basis,

\[
h_v=\sum_j v_j\psi_j,
\]

\[
\mathcal W(h_v)=v^T(A-P)v,
\]

\[
Qv=(H_v(1/2),H_v(-1/2)).
\]

Once Step 32 is closed, the finite interval certificate becomes a finite
analytic Weil positivity theorem.

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
