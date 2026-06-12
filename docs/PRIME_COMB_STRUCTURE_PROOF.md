# Prime-Comb Structure Proof Note

Date: 2026-06-12

Status: `PC-001`, theorem-shaped research note.  This is not a proof of RH, not
a Step33 route mutation, and not a Lean proof file.

## Question

What modular or special structure plays for the prime comb the role that
modular forms played for the E8 lattice?

## Answer

The first correct structure is the Guinand-Weil explicit-formula distribution,
best viewed through Tate-Iwasawa adelic harmonic analysis.  The prime comb is
not an arbitrary discrete measure.  It is the non-archimedean local term in a
global Fourier/trace identity whose other side is the zero distribution plus
the archimedean gamma term.

In Q3 notation, the working prime comb is:

```text
mu_P = sum_n 2 Lambda(n) / sqrt(n) * delta_{log n / 2pi}.
```

The special structure is:

```text
Euler product
  -> logarithmic derivative
  -> prime-power comb
  -> centered Weil normalization
  -> Guinand-Weil distribution
  -> zero side + archimedean gamma side.
```

This is the analogue of the E8 move in one precise sense: it replaces an
unstructured infinite family of pointwise prime checks by one global dual
identity with fixed transform normalization.

## Proof Claim

For every admissible Q3 test function `Phi`, the prime-comb functional

```text
P(Phi) = sum_n 2 Lambda(n) / sqrt(n) * Phi(log n / 2pi)
```

is the prime/non-archimedean local term in the Guinand-Weil explicit formula.
Equivalently, Q3's formal split

```text
Q(Phi) = arch_term(Phi) - prime_term(Phi)
```

is not an arbitrary decomposition: it is the finite/Q3 normalization of the
classical explicit-formula distribution.

Therefore the candidate "modular/special structure" for the prime comb is:

```text
Guinand-Weil explicit formula + adelic local-to-global harmonic analysis,
with Connes-style trace formula as the geometric interpretation.
```

## Proof Sketch

1. The Euler product gives the arithmetic source of the comb:

   ```text
   -zeta'(s) / zeta(s) = sum_n Lambda(n) n^(-s).
   ```

   After centering at the critical line and writing
   `xi_n = log n / 2pi`, the test-function pairing becomes a weighted sum at
   the logarithmic nodes `xi_n`; Q3 uses the symmetric Weil weight
   `2 Lambda(n) / sqrt(n)`.

2. Weil's 1952 explicit formula states, in distributional language, that
   sums over nontrivial zeros are linked to sums over prime powers.  Weil
   emphasizes that the relevant Fourier transform is a distribution, not just a
   function, and then formulates the general setting through Hecke characters,
   ideles, and local completions.

3. Q3 already exposes this split syntactically:

   ```lean
   axiom explicit_formula :
     forall Phi in Weil_cone, Q Phi = arch_term Phi - prime_term Phi
   ```

   and the concrete prime side is:

   ```lean
   def prime_term (Phi : R -> R) : R :=
     sum' n, w_Q n * Phi (xi_n n)
   ```

   with `w_Q(n)` and `xi_n` matching the centered prime-comb convention.

4. Connes' trace-formula interpretation gives the geometric reading: the
   explicit formulas become a trace formula on the noncommutative space of
   adele classes.  Connes-Consani then identify Weil positivity as a trace
   formula problem in a semi-local Hilbert-space framework.

5. Hence the prime comb's special structure is not "more interval arithmetic".
   It is the local term of a global self-dual distribution.  The right proof
   move is to preserve that distributional identity and seek finite receivers
   that compress prime-side checks back into this explicit-formula structure.

## What This Proves

- The prime comb has a canonical structural origin: Euler product plus
  Guinand-Weil/Tate-Iwasawa local-to-global harmonic analysis.
- In Q3, `prime_term` should be treated as a structured non-archimedean local
  term, not as a free scalar table.
- A valid Track B experiment should try to turn finite prime-side pain into a
  theorem-shaped explicit-formula or trace-formula receiver.

## What This Does Not Prove

- It does not prove RH.
- It does not prove Weil positivity.
- It does not close Step33, L3, or any active Lean gate.
- It does not justify replacing the current PSD route.
- It does not allow normalization drift: gamma terms, boundary/cap terms,
  square-root weights, and Haar/Fourier normalization must all be preserved.

## Minimal Experiment

Create a route-local experiment card only after extracting one finite-window
identity of the form:

```text
finite prime comb on window
  =
explicit-formula local term
  =
arch/gamma piece - zero-side piece + named boundary/cap error.
```

Success criterion:

- the identity returns to the exact Q3 `prime_term`/`arch_term` normalization;
- every gamma, cap, boundary, and sign term is named;
- the result gives a theorem-shaped receiver, not just an analogy.

Failure criterion:

- the formula explains a nearby transformed model but cannot return to Q3's
  exact `2 Lambda(n) / sqrt(n)` and `log n / 2pi` convention.

## Sources

- Weil, `Sur les "formules explicites" de la theorie des nombres premiers`,
  1952, Commun. Sem. Math. Univ. Lund Suppl., 252-265.
  Bibliographic record:
  https://cds.cern.ch/record/471308.
- Guinand, `A summation formula in the theory of prime numbers`, Proc. London
  Math. Soc. (2) 50 (1948), 107-119.
- Tate, `Fourier analysis in number fields, and Hecke's zeta-functions`,
  Algebraic Number Theory, 1967, 305-347.
- Connes, `Trace formula in noncommutative geometry and the zeros of the
  Riemann zeta function`, Selecta Math. 5 (1999), 29-106.
  arXiv:
  https://arxiv.org/abs/math/9811068.
- Connes-Consani, `Weil positivity and Trace formula, the archimedean place`,
  arXiv:2006.13771.
  https://arxiv.org/abs/2006.13771.
