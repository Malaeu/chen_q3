# Canonical Signed Boundary-Null PSD Sanity

Date: 2026-06-04

Route:

```text
Step33A.1-A canonical signed finite-Weil A direct boundary-null PSD sanity
```

## Setup

Matrices used for the sanity check:

```text
A = current Step22 positive Arch midpoint table
P = current finite prime midpoint table
Q = current boundary midpoint table
```

Canonical signed route under test:

```text
C_signed = -A - P
```

Positive finite route comparator:

```text
C_positive = A - P
```

This is a midpoint sanity check, not a Lean proof payload.  Its purpose is to
decide whether a generator for:

```lean
primaryK11CanonicalSignedBoundaryNullPSDCert_of_penalty_lower_bound
controlK9CanonicalSignedBoundaryNullPSDCert_of_penalty_lower_bound
```

is arithmetically plausible.

## Results

Primary k=11:

```text
Q singular values: [9.68757799, 6.87835225]
rank(Q): 2
dim ker(Q): 21

A-P:
  min eig on ker(Q): +0.000190283604334
  negative eigenvalues: 0
  max eig on ker(Q): +2.61738467644

-A-P:
  min eig on ker(Q): -1.418250308269634
  negative eigenvalues: 13
  max eig on ker(Q): +2.1904510543433995
```

Control k=9:

```text
Q singular values: [9.68757799, 6.87835225]
rank(Q): 2
dim ker(Q): 21

A-P:
  min eig on ker(Q): +0.0000190759278019
  negative eigenvalues: 0
  max eig on ker(Q): +2.58293999017

-A-P:
  min eig on ker(Q): -1.367079180010388
  negative eigenvalues: 12
  max eig on ker(Q): +2.6023871159713385
```

Other sign variants:

```text
primary:
  A+P   min -2.19045105434, neg  8
  -A+P  min -2.61738467644, neg 21
  P-A   min -2.61738467644, neg 21

control:
  A+P   min -2.60238711597, neg  9
  -A+P  min -2.58293999017, neg 21
  P-A   min -2.58293999017, neg 21
```

Penalty note:

```text
Adding tau * Q^T Q cannot fix the negative eigenvalues for -A-P,
because Qv = 0 on the target boundary-null space.
```

## Verdict

Do not generate a direct `-A-P` signed PSD payload.

Current finite PSD truth points to:

```text
A - P
```

not:

```text
-A - P
```

This is now a semantic sign-location fork, not a generator-size problem.
