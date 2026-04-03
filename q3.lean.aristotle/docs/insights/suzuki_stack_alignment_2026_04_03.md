# Suzuki stack alignment (2026-04-03)

## Purpose

This note records the exact synergy between the current Q3 `H-bridge` route and
the Suzuki operator stack (2012 / 2019 / 2023), and just as importantly, where
that synergy does **not** justify an operator-pivot that skips the active
`PO2` blocker.

## Executive summary

The Suzuki material is strongly aligned with the **upper backend** of our
current route:

```tex
T0\text{-}pd \to H1^f \to H2^f \to H3^f \to H4^f \to RH,
\qquad
H4^f:\ 0\notin \sigma_p(G_g[a])\ \forall a>0.
```

But it does **not** remove the current lower blocker inside `H1^f`, namely the
filtered mixed-block adapter theorem `PO2`.

So the right conclusion is:

```tex
\textbf{Suzuki is a structural backend for our live route, not a shortcut around PO2.}
```

## Layer-by-layer alignment

### Suzuki 2023: screw function / Hermitian kernel / operator criterion

This is the closest direct match to the top of our route.

The 2023 layer gives a screw function `g`, a Hermitian kernel `G_g(t,u)`, and
an operator criterion of RH via nondegeneracy / positivity on windows
`(-a,a)`. In our language, this matches the endpoint:

```tex
H4^f:\quad 0\notin \sigma_p(G_g[a])\ \forall a>0 \Longrightarrow RH.
```

This is already frozen in the project control-plane:

- `PROJECT_ORCHESTRATOR.md` treats `H4` as Suzuki Theorem 1.4 endpoint.
- `PHASE_MONITOR.md` keeps the whole `H-bridge` aimed at that criterion.

So Suzuki-2023 does **not** introduce a new destination. It validates the
destination we already chose.

### Suzuki 2019: Fredholm determinants and eigenvalue control

The 2019 layer is most useful as a backend for the passage

```tex
H2^f/H3^f \rightsquigarrow H4^f.
```

Its real value is not conceptual glamour but mechanism:

- trace-class control,
- Fredholm determinants,
- a way to track whether an eigenvalue can cross zero.

This is exactly the sort of rigorous backend one would want **after** the
bridge has identified the correct finite-section comparison object and moved
all uncontrolled mass into named boundary/cap channels.

So Suzuki-2019 is naturally downstream of the current local proof attack.

### Suzuki 2012: canonical systems and Hamiltonians

The 2012 layer is the deepest structural package:

- `\Theta_\omega`,
- meromorphic inner functions,
- canonical systems,
- positive semidefinite Hamiltonians.

This is powerful, but it is the farthest from our current blocker. It is best
understood as a structural explanation of why the endpoint criterion should be
true, not as the next execution step.

If we ever reach a clean global operator positivity / nondegeneracy statement,
then this layer becomes valuable for packaging and interpretation.

Right now it is too far upstream to help with the mixed-block adapter itself.

## Exact contact point with the current project

The current proof-critical gate is still:

```tex
PO2:\quad \text{cross-sign bulk exactness inside } H1^\infty.
```

And after all recent reductions, its minimal receiver is now:

```tex
P,Q\in\mathcal C_a,\qquad
P(m)=Q(m+1)\ \forall m>N
\Longrightarrow
P(z)=Q(z+1),
```

equivalently the structured Cauchy-tail injectivity problem on

```tex
Y_a=\{x_\gamma,\ x_\gamma-1\}.
```

This is lower in the stack than Suzuki's final operator criterion. In other
words:

- Suzuki explains what we want the **finished bridge** to hand off to;
- `PO2` is still the first unresolved brick that decides whether we even reach
  that operator world honestly.

## Real synergies

### 1. Endpoint confirmation

Suzuki confirms that the project is aimed at a legitimate RH-equivalent
operator criterion, not at an ad hoc numerical experiment.

### 2. Correct positivity object

Suzuki strongly supports the rule that we must not attack raw convolution
positivity. The meaningful object is the modified Hermitian kernel / operator
pair, not an overly strong positive-definite demand on the bare screw function.

This is fully aligned with our own route-kills:

- no raw Toeplitz-vs-Weil identity,
- no basis/rank hunt as theorem content,
- no fake positive-definiteness shortcut.

### 3. Spectral backend for later phases

If `H1^f -> H2^f -> H3^f` ever lands cleanly, Suzuki-2019 gives the right
language for rigorous no-zero-eigenvalue propagation:

- determinants,
- trace-class continuity,
- spectral crossing control.

### 4. Counterexample shape intuition

Suzuki's “if RH fails, then there is a local annihilator / null direction”
matches the genre of obstruction we are already seeing in the mixed-block wall:
the route lives or dies on whether a structured hidden null direction can
survive inside the filtered receiver.

This is not a proof transfer, but it is a real conceptual rhyme.

## What Suzuki does **not** let us do

### 1. No operator-pivot around PO2

The current live blocker is still the lower adapter theorem, not the global
operator endpoint.

So we should **not** pivot to:

- raw discretizations of `G_g[a]`,
- finite-section PSD numerics,
- or canonical-system packaging,

as if those already replaced the mixed-block proof.

They do not.

### 2. No self-adjoint glamour shortcut

The self-adjoint / Hamiltonian side is downstream of the positivity brick, not
a replacement for it.

So “construct the nice operator” is not the next proof step. It is packaging
after the hard work, not instead of it.

## Operational conclusion

The correct use of Suzuki in the current phase is:

1. keep `PO2` as the active proof-critical gate;
2. continue reducing `PO2` at the minimal receiver level;
3. treat Suzuki-2023 as the endpoint acceptance target;
4. treat Suzuki-2019 as the future determinant backend once the bridge is
   closed;
5. treat Suzuki-2012 as structural packaging, not as the next executable move.

So the synthesis is:

```tex
\textbf{
Suzuki does not change the route.
It explains why the current route is the right one.
}
```

## Sources used

- Masatoshi Suzuki, *A canonical system of differential equations arising from
  the Riemann zeta-function* (2012), arXiv:1204.1827.
- Enrico De Micheli, Giovanni Alberto Viano, *The interpolation formula for a
  class of meromorphic functions* (2013), J. Approx. Theory 168, 33–68.
- Enrico De Micheli, Giovanni Alberto Viano, *Numerical recovery of location
  and residue of poles of meromorphic functions* (arXiv:1409.1145).
- Project control files:
  `PROJECT_ORCHESTRATOR.md`, `ACTIVE/PHASE_MONITOR.md`,
  `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`.
