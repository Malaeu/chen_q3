# Step 28 -- Boundary-null correction lemma

## Goal

Close the algebraic core needed for boundary-null exhaustion.

Given two boundary functionals

\[
E_+(h)=H(1/2),
\qquad
E_-(h)=H(-1/2),
\]

and two corrector bumps \(b_+,b_-\), if

\[
\det
\begin{pmatrix}
E_+(b_+) & E_+(b_-)\\
E_-(b_+) & E_-(b_-)
\end{pmatrix}
\ne0,
\]

then every approximant \(g\) can be corrected to

\[
g^\circ=g-a_+b_+-a_-b_-
\]

with

\[
E_+(g^\circ)=E_-(g^\circ)=0.
\]

## Lean file

```text
Q3/Proofs/PSD_BoundaryNullCorrection.lean
```

## Main theorem

```text
boundary_correction_exists
```

It proves the algebraic determinant condition:

\[
\det M\ne0
\Rightarrow
\exists a_+,a_-:\ E_+(g-a_+b_+-a_-b_-)=0,\quad
E_-(g-a_+b_+-a_-b_-)=0.
\]

## Why this matters

Step 23 requires density inside the boundary-null test class.  Ordinary
finite-space density does not preserve \(H(\pm1/2)=0\).

This lemma gives the exact correction mechanism.  It is purely linear algebra:
the analytic construction of the corrector bumps is deliberately postponed.

## What remains

The analytic exhaustion layer must prove:

1. existence of compactly supported smooth correctors \(b_+,b_-\);
2. continuity of \(E_\pm\) in the selected topology;
3. if \(g_n\to h\) and \(h\) is boundary-null, then the correction coefficients
   go to zero;
4. the corrected sequence stays in the directed finite-family closure.

## Verdict

Step 28 closes the algebraic boundary-null correction core.

Step 29 should prove the small-coefficient convergence version.
