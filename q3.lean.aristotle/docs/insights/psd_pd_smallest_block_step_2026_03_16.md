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

## Canonical choice of `J_{\min}`

The project already contains a canonical smallest nontrivial pilot:

```tex
K=0.2,
\qquad
J_{\min}=\{0,1\},
\qquad
\Delta=0.15,
```

with the canonical packet `g_{\delta,t_0,0}`.

For this choice,

```tex
D(J_{\min})=\{-1,0,1\},
```

so the symbol is degree `1`:

```tex
S_{J_{\min}}(\theta)
=
\kappa_0+\kappa_1e^{-i\theta}+\kappa_{-1}e^{i\theta}
=
(\alpha_0-\beta_0)+2(\alpha_1-\beta_1)\cos\theta.
```

This is the right `B1` receiver because it is already frozen inside
`Main_closure.tex` as the pilot compact for the canonical half-atom.

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

For the canonical pilot above, the current manuscript already records:

- active positive nodes in `[0,K]` are exactly `\xi_2,\xi_3`;
- `\operatorname{dist}(0.15,\Xi_K)\approx 0.02485`;
- if `\delta<0.0124`, then `\beta_0=\beta_1=0`;
- hence
  ```tex
  S_{J_{\min}}(\theta)\ge \alpha_0-2|\alpha_1|;
  ```
- and the numerical gap
  ```tex
  a^*(0)-2a^*(0.15)\approx 7.13>0
  ```
  gives a viable Archimedean margin once the modulus error is kept below it.

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

Use the canonical two-packet dictionary above unless a contradiction appears.

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

For the canonical pilot, the checklist already sharpens to:

1. `J_{\min}=\{0,1\}`, `K=0.2`, `\Delta=0.15`;
2. exact symbol
   ```tex
   S_{J_{\min}}(\theta)
   =
   (\alpha_0-\beta_0)+2(\alpha_1-\beta_1)\cos\theta;
   ```
3. prime-side certificate:
   use `\delta<0.0124` to force `\beta_0=\beta_1=0`;
4. Archimedean certificate:
   prove `\alpha_0>2|\alpha_1|` via the modulus bound and the gap
   `a^*(0)-2a^*(0.15)>0`;
5. optional regularized wrapper:
   route the same block through `P7.5/P7.6` if we want one explicit Poisson
   error budget rather than the direct pilot inequality.

## Relation to lane `A`

Lane `B` is not allowed to rewrite the `H1` theorem shape.

Its role is narrower:

- keep a constructive fallback alive;
- generate strict finite certificates;
- generate an early obstruction if even the smallest explicit block behaves
  badly.

So `B1` complements `A4`; it does not compete with it.

## Current binary verdict

For the canonical pilot block, the certificate story currently looks viable,
not obstructed:

- the exact symbol is explicit;
- the prime coefficients vanish on the stated small-` \delta ` regime;
- the Archimedean margin is numerically positive;
- the resulting positivity statement is already written in theorem form for
  `c\in\mathbb C^2`.

So the right local reading is:

```text
B1 is not a vague fallback anymore; it already has one canonical smallest block
that looks certificate-viable.
```

## Success criterion

This note lands only if the next lane-`B` move is no longer “work on PSD-pd”,
but a single explicit finite certificate task.

## Non-goals

- no new RH architecture;
- no dense dictionary theorem;
- no large family sweep;
- no interference with `PO1 -> PO3` on the `H1` side.
