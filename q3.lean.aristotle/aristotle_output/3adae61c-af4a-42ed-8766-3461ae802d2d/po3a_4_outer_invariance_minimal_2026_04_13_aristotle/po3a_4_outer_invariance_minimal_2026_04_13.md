# PO3a.4 — outer-invariance minimal bridge

## Address

- Main address: `PO3a.4`
- Related: `PO3a.3`, `PO3a.5`, `PO3a-A`, `H-bridge.11`

## Exact task

We work in a Hilbert-space style sign-split setting

\[
\mathcal H = \mathcal H_+ \oplus \mathcal H_- .
\]

We have vectors

\[
h_+, x_+ \in \mathcal H_+,
\qquad
h_-, x_- \in \mathcal H_-,
\]

with

\[
h_+ \neq 0,
\qquad
h_- \neq 0.
\]

We also have outer operators \(U,V\) and a mixed `2 \times 2` receiver

\[
\mathcal K=
\begin{bmatrix}
|U^* h_+\rangle & |U^* x_+\rangle
\end{bmatrix}
\begin{bmatrix}
-1 & c \\
0  & -1
\end{bmatrix}
\begin{bmatrix}
\langle V^* x_-| \\
\langle V^* h_-|
\end{bmatrix}.
\]

The middle matrix is invertible.

## Preferred theorem target

Prove a clean theorem of the following kind.

Assume:

1. local sign preservation:
   \(U^*(\operatorname{span}\{h_+,x_+\}) \subset \mathcal H_+\) and
   \(V^*(\operatorname{span}\{h_-,x_-\}) \subset \mathcal H_-\);
2. local injectivity:
   \(U^*\) is injective on \(\operatorname{span}\{h_+,x_+\}\) and
   \(V^*\) is injective on \(\operatorname{span}\{h_-,x_-\}\).

Then

\[
\mathcal K = 0
\]

forces the same scalar rigidity as in the identity-outer case:

\[
x_+ = \lambda h_+,
\qquad
x_- = \mu h_-,
\qquad
\lambda + \mu = c
\]

for some scalars \(\lambda,\mu\).

## Allowed simplifications

- If the theorem above is slightly too strong, prove the strongest fully
  correct version you can.
- If one of the hypotheses is unnecessary, remove it.
- If one of the hypotheses is insufficient, replace it by the minimal correct
  one.
- If it is cleaner to state the result first for abstract vector spaces plus
  linear maps and then specialize to Hilbert spaces, that is fine.

## Important constraint

Do not assume \(U = V = I\).

The whole point is to show that the real outer-factor case collapses back to
the already known identity-outer rigidity once the outer operators are locally
harmless.

## Desired output

Please provide:

1. a precise theorem statement,
2. a proof sketch,
3. if possible, Lean 4 code for the abstract theorem.
