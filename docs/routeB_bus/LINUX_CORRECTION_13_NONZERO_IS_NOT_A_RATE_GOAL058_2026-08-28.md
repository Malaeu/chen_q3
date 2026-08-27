---
TASK_ID: LINUX_SELF_CORRECTION_13
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: 0acfef97, sections 4, 6, 7 and 9
ACCEPTS_VERDICT: 60df219b
RH_CLAIM: false
---

# Correction 13 — exact non-annihilation is not a rate, and four smaller repairs

## 1. The central error

Report `0acfef97` proved the exact criterion: `z -> T(a)` is identically zero iff
`Q Phi(a) = 0`. That stands. I then concluded that failure of the criterion makes
the zero **detected at consumer strength**, and from there that the required rate
implies a zero-free region.

The inference is invalid, and the judge's falsifier is decisive: a sequence with
`Q_m Phi_m != 0` may have norm `exp(-m)`. The exact criterion then fails at every
cell while every polynomial amplification still tends to zero. **Exact
non-annihilation supplies no lower envelope in `m`.** I converted an algebraic
statement into a quantitative one without an envelope, which is the same move I
have been corrected for three times tonight.

Withdrawn: `SIGNED_ORIENTED_STIELTJES_RATE_IS_ZERO_FREE_REGION_STRENGTH`, the
FAIL discriminator, and the conclusion that the arithmetic gate is closed. What
survives is narrower and was already ratified: the **exact-annihilation shortcut**
is closed in the negative — endpoint vanishing and `Q`-orthogonality do not by
themselves annihilate the transfer.

## 2. `||y||` is not bounded below by the graph solve

Withdrawn. Positivity and the complement floor bound `||C^{-1} v||` from **above**;
that is what a floor does. A lower bound needs an upper envelope for `C` together
with a lower envelope for the observed row, and invertibility supplies neither.
The judge's plant settles it: on `q^perp` take `C_m = m^{2 sigma} I`, positive,
invertible, `Q`-preserving, with `||C_m^{-1} v|| = m^{-2 sigma} ||v||`. The graph
solve can suppress the transfer despite exact span and exact non-annihilation.

## 3. "Ranges over all of `q^perp`" is wrong

The correct statement is that the **linear span** of `{ y(z) }` is `q^perp`. A
curve in one complex parameter need not be set-theoretically surjective onto a
higher-dimensional space. Span suffices for the exact identically-zero criterion,
which is all I was entitled to use it for, and does not suffice for any uniform
lower bound.

## 4. The compact quantifier was dropped

Locally uniform tracking is tested on **one fixed compact** `K`. My span argument
used the whole spectral plane, in particular evaluation at the poles `p_j`. That
proves injectivity per finite cell; it says nothing about how the associated
observability constant behaves as the cell grows. The two are different
quantifiers and I conflated them.

## 5. The quartet criterion is not yet exact

I wrote that the two growing quartet terms vanish identically only under the same
criterion `Q Phi(a) = 0`. On a real spectral slice the growing pair is governed by
the real part of `exp(2 pi a) Phi(a)`, and that condition is generally **weaker**
than `Phi(a)` lying on the `q`-line. The exact criterion must be derived in the
real/complex source category and has not been.

## 6. Circularity semantics

Repaired, and the repair matters for how such results are reported. Proving a
rate that implies a zero-free region is **not**, by itself, a circular proof. It
classifies the strength of a theorem. Circularity is a property of the proof's
**inputs** and requires an audit of them. Route-kill on that basis is justified
only after a quantitative converse or a lower envelope is proved, and I had
neither.

## 7. Ledger

Nineteenth forbidden move: **an exact algebraic non-vanishing is not a
quantitative lower bound.** Before converting "not identically zero" into "large
enough to matter", produce the envelope in the growing parameter.

Twentieth: **"no supplier found" and "no reason to hold" are not mathematical
evidence.** I used both in `0acfef97` section 4 to argue that the selected row
fails the eigenvector criterion. The catalogue's silence bounds what we can cite,
not what is true. The judge has now made this explicit in the required outputs,
and it is recorded here as a standing rule rather than a one-off.
