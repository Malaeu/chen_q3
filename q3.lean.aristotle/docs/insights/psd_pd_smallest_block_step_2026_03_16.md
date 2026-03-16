# `PSD-pd` smallest-block step (2026-03-16)

## Status

Day 5 active artifact for the `Q_\zeta`-core short-circuit sprint.

This note is not the whole fallback route. It is only the first explicit
certificate receiver after `A4`.

## Purpose

Keep lane `B` alive in the narrowest possible way:

- one smallest explicit admissible finite dictionary;
- one exact finite symbol;
- one honest positivity/certificate target;
- one explicit error budget.

## Frozen `B1` target

The first certificate target should be:

```tex
S_{J_{\min}}(\theta)=A_{J_{\min}}(\theta)-P_{J_{\min}}(\theta)\ge 0,
```

for one smallest explicit admissible finite dictionary `J_{\min}`.

This must be a theorem-relevant finite object, not an exploratory family scan.

## Input already frozen by the project

The certificate backend already has the right ingredients:

- exact packet-Rayleigh on autocorrelation packets;
- finite admissible dictionary reduction;
- finite symbol `S_J(\theta)=A_J(\theta)-P_J(\theta)`;
- coefficient bounds on `\alpha_m,\beta_m`;
- Poisson-regularized finite verification;
- explicit error budget.

So `B1` should not invent a new certificate language. It should only freeze the
smallest usable instance.

## Required outputs

`B1` lands only if it fixes all four items:

1. one explicit admissible dictionary `J_{\min}`;
2. one exact symbol `S_{J_{\min}}(\theta)`;
3. one certificate route:
   coefficient bounds + Poisson regularization + error budget;
4. one binary verdict:
   certificate looks viable or the smallest block already exposes a scaling
   obstruction.

## Selection rule for `J_{\min}`

Choose the smallest nontrivial admissible finite packet dictionary already
compatible with the frozen packet-Rayleigh / finite-P7 language.

Do **not**:

- enlarge the dictionary for prettier numerics;
- switch to a new packet family;
- ask lane `B` to prove dense-kernel positivity already at `B1`.

## Certificate checklist

The minimal `B1` package should answer:

- what is `J_{\min}` exactly;
- what is the resulting exact finite symbol;
- which coefficient bounds on `\alpha_m,\beta_m` are actually needed;
- what Poisson-regularized step closes the finite verification;
- what error budget is left over.

## Relation to lane `A`

Lane `B` is not allowed to rewrite the `H1` theorem shape.

Its role is narrower:

- keep a constructive fallback alive;
- generate strict finite certificates;
- generate an early obstruction if even the smallest explicit block behaves
  badly.

So `B1` complements `A4`; it does not compete with it.

## Success criterion

This note lands only if the next lane-`B` move is no longer “work on PSD-pd”,
but a single explicit finite certificate task.

## Non-goals

- no new RH architecture;
- no dense dictionary theorem;
- no large family sweep;
- no interference with `PO1 -> PO3` on the `H1` side.
