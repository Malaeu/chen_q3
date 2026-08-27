---
TASK_ID: LINUX_SELF_CORRECTION_12
MODE: PAPER_AND_SOURCE_READ_ONLY plus declared numeric test
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: 39773de8 and 15bc50f6
ACCEPTS_VERDICT: 87e5ea2f
RH_CLAIM: false
---

# Correction 12 — Q-projection makes two of my points moot, and a hypothesis I tested and killed

## 1. Withdrawn: "the Euler-Mascheroni head survives and must be carried"

Report `15bc50f6` section 1 made much of the fact that, unlike the center column,
the archimedean head does not vanish on the diagonal: `ccmQKernel L n n 0 = 2`,
so the head is `gamma + log(4 pi tanh(L/2))`, present and `O(1)`.

True about `M_nn`, and irrelevant to the consumer. Verdict `87e5ea2f` shows the
minimal object is `Q`-projected: with `y = Q x = C^{-1} Q kappa`,

    Psi = <x, r> = <y, r>        because <q, r> = 0,
    Psi = <y, (M - aI) q> = <y, M q>   because <y, q> = 0.

Consequently every `n`-**independent** diagonal term pairs to zero, since it acts
as `c I` and `<y, c q> = c <y,q> = 0`. The head is exactly such a term. So are the
Rayleigh shift `-a I` and the constant subtraction `ccmQKernel L n n 0 = 2` inside
the `WR` integrand. All three vanish from the consumer without any estimate.

I read the head off the source correctly and then failed to ask whether the
consumer sees it.

## 2. Withdrawn: "the diagonal can never be absorbed"

Report `39773de8` proved that the full Volterra kernel is aperiodic, hence not
reflection-odd, hence the diagonal cannot enter **the same odd reflection
functional**. That much is ratified. I then wrote "no representation shift will
remove it", which is a claim about all possible representations and is not what
the witness proves. Section 1 above is itself a counterexample in miniature: a
`Q`-projection removed three diagonal terms outright. Withdrawn, and the
corrected statement is the narrow one the verdict ratified.

## 3. A hypothesis formed, tested, and killed the same hour

Working from `M_nn = psi'(n)` — the diagonal of a divided-difference matrix is
the derivative of its source — I formed the hypothesis that the diagonal is the
**cosine** transform of the *same* completed measure that gives
`beta_n = integral sin(n t) d mu(t)`, namely

    M_nn  =?  integral t cos(n t) d mu(t).

Tested against the literal definitions before reporting it. **Refuted**, and not
marginally: at `m = 10^3, n = 0` the literal value is `0.0162` and the transform
gives `126.38`.

The reason is a weight, not a sign. Ledger by ledger, from closed form,

    W02_nn   = integral t (cos n t) d mu_{W02}(t)          — weight t,
    Prime_nn = integral (2 pi - t) (cos n t) d mu_prime(t) — weight 2 pi - t,

so the two ledgers carry **different weights in the same variable**, and no single
cosine transform represents the diagonal. The `W02` identity is exact:
`integral_0^infty t cos(n t) e^{-a t} dt = (a^2-n^2)/(a^2+n^2)^2` with
`a = L/(4 pi)` and the prefactor `2 L sinh^2(L/4)/pi^2` reproduces
`32 L sinh^2(L/4)(L^2 - 16 pi^2 n^2)/(L^2 + 16 pi^2 n^2)^2` verbatim. The prime
identity is exact in the reflected variable, since
`2 pi - theta_k = 2 pi (L - log k)/L`.

Recorded as a **named dead end with its reason**, because the reason is
informative: the diagonal weights of the pole and prime ledgers are reflections of
each other, exactly as their densities are. Any unification must be attempted in
the reflected variable, after folding, not in the raw one.

## 4. Ledger

Seventeenth forbidden move: **before carrying a source feature into a report, ask
whether the consumer sees it.** An `n`-independent term is invisible to a
`q`-orthogonal pairing; three of them were.

Eighteenth: **a witness against one representation is not a theorem against all
representations.** Say which representation the witness kills.
