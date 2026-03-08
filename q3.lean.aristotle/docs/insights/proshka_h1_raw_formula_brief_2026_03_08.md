# Proshka Context Pack
Generated: 2026-03-08T20:28:12
Repo: /Users/emalam/Documents/GitHub/rh_lean_01_2026
Branch: rh_clean
HEAD: b89a43b9
Commits: last 10

## Executive Summary

This pack is targeted at the missing raw-entry brick for the Suzuki bridge.
The key point is that the current draft already fixes the correct filtered
geometry, but the exact raw Section 8 entry formula is still only implicit in
the older A3 files.

What Proshka needs from our side is not a new architecture, but the exact
normalization and matrix-entry data hidden in the following files:

1. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A3/rayleigh_bridge.tex`
   gives the model space `\mathcal P_M`, the normalized prime vectors
   `v_n^{(M)}`, the compression identity
   `\iota_M^* T_P^{Ray}(t)\iota_M = (2M+1) T_P^{Ray}(t,M)`, and the exact
   quadratic Rayleigh pairing.
2. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A3/calibration.tex`
   fixes the A3 normalization and explicitly states `\kappa_{A3}=1`.
3. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/RKHS/core.tex`
   records the RKHS energy / Gram language that explains why the finite block is
   the strongest reusable operator object in Q3.
4. `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
   contains the new H1 raw-entry target
   `w_{rs}(a)=\kappa(a) q_{rs}` and the filtered consequence layer.

Crucially:

- `w_{rs}(a)` comes from the Suzuki/Weil side.
- the exact normalized Section 8 raw entry formula is
  `q_{rs}^{(L)}=\langle Q_L e_s,e_r\rangle=a_{r-s}-p_{r-s}^{(L)}`
  with
  `p_k^{(L)}=(2L+1)^{-1}\sum w(n)\Phi_{B,t}(\xi_n)e^{-2\pi i k\xi_n}`;
- in the filtered bridge one writes `q_{rs}=q_{rs}^{(M+1)}` for the ambient
  finite block;
- the equality `w_{rs}(a)=\kappa(a)q_{rs}` is **not** an already proved Q3
  theorem. It remains the exact bulk target for `H1`.

So if Proshka asks for “the formula”, what he really needs is the exact raw
Section 8 entry convention and its normalization, because the old A3 files
spelled out the quadratic-form/compression machinery but not this `L`-local raw
entry formula as one explicit line.

## Working tree
```text
## rh_clean...origin/rh_clean
```

## Commit list (oneline)
```text
b89a43b9 [MacOS][rh_clean][Docs] Narrow H1 bulk to raw entry match
08ad4926 [MacOS][rh_clean][Docs] Freeze H1 four-block bulk stack
5f6a30c8 [MacOS][rh_clean][Docs] Freeze two-sided filtered H1 bridge
baa961bc [MacOS][rh_clean][Docs] Freeze filtered H1 finite section
a9b6ff14 [MacOS][rh_clean][Docs] Freeze filtered Volterra H1 bridge
2470f20a [MacOS][rh_clean][Docs] Freeze semilocal H1 engineering layer
0f4557e9 [MacOS][rh_clean][Docs] Freeze H1 Gram candidate construction
21c4e525 [MacOS][rh_clean][Docs] Promote Suzuki bridge and rebuild PDF
0d5f7357 [MacOS][rh_clean][Docs] Freeze Suzuki bridge candidate
2ed67150 [MacOS][rh_clean][Docs] Advance scalar compact queue
```

## Range diff summary
```text
IMPLEMENTATION_PLAN.md                             |   6 +-
 full/RH_Q3.pdf                                     |   4 +-
 full/sections/Main_closure.tex                     | 655 ++++++++++++++++++---
 full/sections/Notation/qstar_contract.tex          |  13 +-
 full/sections/Weil_linkage.tex                     |   4 +-
 full/sections/Weil_pack.tex                        |  21 +-
 full/sections/abstract.tex                         |  10 +-
 full/sections/introduction.tex                     |  92 ++-
 full/sections/scope_notation.tex                   |  30 +-
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          |  96 ++-
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 166 ++++--
 q3.lean.aristotle/docs/INSIGHTS.md                 | 290 +++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   | 104 +++-
 .../h1_candidate_gram_construction_2026_03_08.md   |  82 +++
 .../h1_filtered_finite_section_2026_03_08.md       |  49 ++
 .../h1_filtered_volterra_bridge_2026_03_08.md      |  58 ++
 .../docs/insights/h1_four_block_bulk_2026_03_08.md |  71 +++
 .../insights/h1_raw_entry_reduction_2026_03_08.md  |  63 ++
 .../insights/h1_semilocal_engine_2026_03_08.md     |  67 +++
 .../h1_two_sided_filtered_bridge_2026_03_08.md     | 117 ++++
 .../insights/suzuki_form_pair_bridge_2026_03_08.md |  66 +++
 21 files changed, 1863 insertions(+), 201 deletions(-)
```

## Per-commit stats
```text
b89a43b9 [MacOS][rh_clean][Docs] Narrow H1 bulk to raw entry match
 IMPLEMENTATION_PLAN.md                             |   2 +-
 full/RH_Q3.pdf                                     |   4 +-
 full/sections/Main_closure.tex                     | 238 +++++++++++++++++----
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          |  43 +++-
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          |  39 ++--
 q3.lean.aristotle/docs/INSIGHTS.md                 |  51 ++++-
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   |  19 +-
 .../docs/insights/h1_four_block_bulk_2026_03_08.md |   8 +-
 .../insights/h1_raw_entry_reduction_2026_03_08.md  |  63 ++++++
 .../h1_two_sided_filtered_bridge_2026_03_08.md     |   6 +-
 10 files changed, 394 insertions(+), 79 deletions(-)
```
```text
08ad4926 [MacOS][rh_clean][Docs] Freeze H1 four-block bulk stack
 IMPLEMENTATION_PLAN.md                             |  4 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 84 ++++++++++++++++++++++
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          |  6 +-
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 17 +++--
 q3.lean.aristotle/docs/INSIGHTS.md                 | 28 ++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   | 15 ++--
 .../docs/insights/h1_four_block_bulk_2026_03_08.md | 67 +++++++++++++++++
 .../h1_two_sided_filtered_bridge_2026_03_08.md     |  3 +
 9 files changed, 210 insertions(+), 18 deletions(-)
```
```text
5f6a30c8 [MacOS][rh_clean][Docs] Freeze two-sided filtered H1 bridge
 IMPLEMENTATION_PLAN.md                             |   4 +-
 full/RH_Q3.pdf                                     |   4 +-
 full/sections/Main_closure.tex                     | 408 +++++++++++----------
 full/sections/introduction.tex                     |  42 ++-
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          |  57 +--
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 119 +++---
 q3.lean.aristotle/docs/INSIGHTS.md                 |  44 ++-
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   |  74 ++--
 .../h1_two_sided_filtered_bridge_2026_03_08.md     | 112 ++++++
 9 files changed, 519 insertions(+), 345 deletions(-)
```
```text
baa961bc [MacOS][rh_clean][Docs] Freeze filtered H1 finite section
 IMPLEMENTATION_PLAN.md                             |  2 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 36 ++++++++++++----
 full/sections/introduction.tex                     | 19 +++++++--
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          | 11 +++--
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 11 +++--
 q3.lean.aristotle/docs/INSIGHTS.md                 | 28 +++++++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   |  9 ++--
 .../h1_filtered_finite_section_2026_03_08.md       | 49 ++++++++++++++++++++++
 9 files changed, 143 insertions(+), 26 deletions(-)
```
```text
a9b6ff14 [MacOS][rh_clean][Docs] Freeze filtered Volterra H1 bridge
 IMPLEMENTATION_PLAN.md                             |  2 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 73 ++++++++++++++++++----
 full/sections/introduction.tex                     |  9 ++-
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          | 19 ++++--
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          |  9 +++
 q3.lean.aristotle/docs/INSIGHTS.md                 | 27 ++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   |  8 +++
 .../h1_filtered_volterra_bridge_2026_03_08.md      | 58 +++++++++++++++++
 9 files changed, 186 insertions(+), 23 deletions(-)
```
```text
2470f20a [MacOS][rh_clean][Docs] Freeze semilocal H1 engineering layer
 IMPLEMENTATION_PLAN.md                             |  4 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 43 ++++++++++++++
 full/sections/introduction.tex                     |  3 +
 full/sections/scope_notation.tex                   |  3 +
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          |  9 ++-
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          |  9 ++-
 q3.lean.aristotle/docs/INSIGHTS.md                 | 29 ++++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   |  9 +++
 .../insights/h1_semilocal_engine_2026_03_08.md     | 67 ++++++++++++++++++++++
 10 files changed, 173 insertions(+), 7 deletions(-)
```
```text
0f4557e9 [MacOS][rh_clean][Docs] Freeze H1 Gram candidate construction
 IMPLEMENTATION_PLAN.md                             |  4 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 57 +++++++++++++++
 full/sections/introduction.tex                     |  5 +-
 full/sections/scope_notation.tex                   |  6 +-
 q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md          | 33 +++++----
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 33 ++++++---
 q3.lean.aristotle/docs/INSIGHTS.md                 | 30 ++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   | 17 +++--
 .../h1_candidate_gram_construction_2026_03_08.md   | 82 ++++++++++++++++++++++
 10 files changed, 238 insertions(+), 33 deletions(-)
```
```text
21c4e525 [MacOS][rh_clean][Docs] Promote Suzuki bridge and rebuild PDF
 IMPLEMENTATION_PLAN.md                           |   6 +-
 full/RH_Q3.pdf                                   |   4 +-
 full/sections/Main_closure.tex                   | 114 ++++++++++++++---------
 full/sections/Notation/qstar_contract.tex        |  13 ++-
 full/sections/Weil_linkage.tex                   |   4 +-
 full/sections/Weil_pack.tex                      |  21 ++++-
 full/sections/abstract.tex                       |  10 +-
 full/sections/introduction.tex                   |  66 ++++++++++---
 full/sections/scope_notation.tex                 |  21 ++---
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md        |  99 +++++++++++---------
 q3.lean.aristotle/docs/INSIGHTS.md               |  28 +++++-
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md |  28 +++---
 12 files changed, 266 insertions(+), 148 deletions(-)
```
```text
0d5f7357 [MacOS][rh_clean][Docs] Freeze Suzuki bridge candidate
 IMPLEMENTATION_PLAN.md                             |  4 +-
 full/RH_Q3.pdf                                     |  4 +-
 full/sections/Main_closure.tex                     | 44 +++++++++++++++
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md          | 26 ++++++++-
 q3.lean.aristotle/docs/INSIGHTS.md                 | 29 ++++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md   | 37 +++++++-----
 .../insights/suzuki_form_pair_bridge_2026_03_08.md | 66 ++++++++++++++++++++++
 7 files changed, 190 insertions(+), 20 deletions(-)
```
```text
2ed67150 [MacOS][rh_clean][Docs] Advance scalar compact queue
 IMPLEMENTATION_PLAN.md                           |  4 +---
 full/RH_Q3.pdf                                   |  4 ++--
 full/sections/Main_closure.tex                   | 12 +++++++++++-
 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md        | 16 ++++++++++++----
 q3.lean.aristotle/docs/INSIGHTS.md               | 24 ++++++++++++++++++++++++
 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md | 22 ++++++++++++----------
 6 files changed, 62 insertions(+), 20 deletions(-)
```

## File snapshots

### /Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A3/rayleigh_bridge.tex
```text
% Analytic rewrite: Rayleigh identification for the Toeplitz bridge
% Phase 1 (Brick A3.1) – derived from docs/lemmas/A3_bridge_outline.md

\subsection{Rayleigh Identification for the Toeplitz Bridge}\label{subsec:a3-rayleigh}
Throughout we fix a single heat scale $t>0$ and a Fej\'er$\times$heat window
\[
  \Phi_{B,t}(\xi)\ :=\ \Bigl(1-\frac{|\xi|}{B}\Bigr)_{+}\,e^{-4\pi^2 t\,\xi^2},
\]
and write $P_A$ for the associated Archimedean symbol obtained by smoothing the
T0 density $a(\xi)=\log\pi-\Re\psi(\tfrac14+i\pi\xi)$ with the Fej\'er and heat kernels
on $[-B,B]$.  The prime weights are $w(n)=\frac{2\Lambda(n)}{\sqrt n}$ located at the
nodes $\xi_n=\frac{\log n}{2\pi}$, as fixed in Section~\ref{sec:T0}.
The corresponding Weil functional is denoted $Q^\star(t;\Phi_{B,t})$.

Let $\mathcal P_M:=\{p(\theta)=\sum_{|k|\le M}c_k e^{2\pi i k\theta}\}$ denote the trigonometric
polynomials of degree at most $M$, equipped with the $L^2(\TT)$ inner product, and let
$\iota_M:\mathcal P_M\hookrightarrow L^2(\TT)$ be the canonical inclusion with adjoint
$\iota_M^\ast$ equal to the orthogonal projection onto $\mathcal P_M$.

\begin{lemma}[Model--space restriction]\label{lem:a3-model-space}
The Toeplitz operator $T_M[P_A]$ acts on $\mathcal P_M$, is self-adjoint and satisfies
\[
  \left\langle T_M[P_A]\,p,\,p\right\rangle_{L^2(\TT)}
  = \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,|p(\theta)|^2\,d\theta,
  \qquad p\in\mathcal P_M.
\]
Moreover, the symmetrised Rayleigh prime operator
\[
  T_P^{\mathrm{Ray}}(t,M)\ :=\ \sum_{\substack{n\ge2\\ |\xi_n|\le B}}
     w(n)\,\Phi_{B,t}(\xi_n)\,|v_n^{(M)}\rangle\!\langle v_n^{(M)}|,
  \qquad
  v_n^{(M)}(\theta)\ :=\ \frac{1}{\sqrt{2M+1}}\sum_{|k|\le M} e^{2\pi i k(\theta-\xi_n)},
\]
is the \emph{normalized} compression of the global Rayleigh operator
\[
  T_P^{\mathrm{Ray}}(t)\ :=\ \sum_{n\ge2} w(n)\,\Phi_{B,t}(\xi_n)\,
  |e^{2\pi i(\cdot)\xi_n}\rangle\!\langle e^{2\pi i(\cdot)\xi_n}|
\]
to $\mathcal P_M$, in the sense that
\[
  \iota_M^\ast T_P^{\mathrm{Ray}}(t) \iota_M\ =\ (2M+1)\,T_P^{\mathrm{Ray}}(t,M).
\]
Equivalently, in the legacy shorthand $T_P^{(M)}:=T_P^{\mathrm{Ray}}(t,M)$, this is
$(2M+1)\,T_P^{(M)}$ with the scaling attached to the prime block.
It is positive semidefinite with
\[
  \|T_P^{\mathrm{Ray}}(t,M)\| \ \le\ \sum_{\substack{n\ge2\\ |\xi_n|\le B}} w(n)\,\Phi_{B,t}(\xi_n).
\]
\end{lemma}

\begin{proof}
The Toeplitz matrix $T_M[P_A]$ is the compression of the Fourier multiplier with
symbol $P_A$ to $\mathcal P_M$; the stated quadratic form is the standard representation
of Toeplitz forms (see, e.g., \cite[Chapter~1]{GrenanderSzego1958}).  For the prime
operator note that $T_P^{\mathrm{Ray}}(t)$ is a finite-rank positive operator on $L^2(\TT)$,
hence $\iota_M^\ast T_P^{\mathrm{Ray}}(t) \iota_M$ is self-adjoint and positive semidefinite. Since
$\iota_M^\ast e^{2\pi i(\cdot)\xi_n}=\sum_{|k|\le M}e^{2\pi i k(\cdot-\xi_n)}=\sqrt{2M+1}\,v_n^{(M)}$,
the displayed identity $\iota_M^\ast T_P^{\mathrm{Ray}}(t) \iota_M=(2M+1)\,T_P^{\mathrm{Ray}}(t,M)$ follows.
The displayed norm bound is immediate from the triangle inequality applied to
the sum of rank-one projections $|v_n^{(M)}\rangle\!\langle v_n^{(M)}|$.
\end{proof}

\begin{lemma}[Rayleigh pairing]\label{lem:a3-rayleigh-quotient}
For every $p\in\mathcal P_M$ one has
\begin{align*}
  \left\langle (T_M[P_A]-T_P^{\mathrm{Ray}}(t,M))\,p,\,p\right\rangle_{L^2(\TT)}
  &= \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,|p(\theta)|^2\,d\theta
    - \sum_{\substack{n\ge2\\ |\xi_n|\le B}} w(n)\,\Phi_{B,t}(\xi_n)\,|\langle p,v_n^{(M)}\rangle|^2 \\
  &= \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,|p(\theta)|^2\,d\theta
    - \frac{1}{2M+1}\sum_{\substack{n\ge2\\ |\xi_n|\le B}} w(n)\,\Phi_{B,t}(\xi_n)\,|p(\xi_n)|^2.
\end{align*}
\end{lemma}

\begin{proof}
Combine Lemma~\ref{lem:a3-model-space} with the definition of $T_P^{\mathrm{Ray}}(t,M)$ and the identities
$p(\xi_n)=\sqrt{2M+1}\,\langle p,v_n^{(M)}\rangle$ and $\|v_n^{(M)}\|=1$.
\end{proof}

\begin{theorem}[Rayleigh identification for the Fej\'er$\times$heat window]\label{thm:a3-rayleigh-identification}
Let $\Phi_{B,t}$ and $P_A$ be as above, and let $p\equiv1$ be the constant polynomial.
Then
\[
\begin{aligned}
  &\left\langle T_M[P_A]\,1,\,1\right\rangle_{L^2(\TT)}
  - (2M+1)\left\langle T_P^{\mathrm{Ray}}(t,M)\,1,\,1\right\rangle_{L^2(\TT)} \\
  &= \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta
     - \sum_{\substack{n\ge2\\ |\xi_n|\le B}} w(n)\,\Phi_{B,t}(\xi_n) \\
  &= Q^\star(t;\Phi_{B,t}),
\end{aligned}
\]
where $Q^\star$ is the Weil functional in the T0 normalization (Lemma~\ref{t0:lem:T0}).  The factor
$(2M{+}1)$ arises because $|\langle 1,v_n^{(M)}\rangle|^2 = 1/(2M{+}1)$ while
$|1(\xi_n)|^2 = 1$.  Equivalently, one may use unnormalized vectors
$\tilde v_n := \sqrt{2M{+}1}\,v_n^{(M)}$ and write the Rayleigh identity without the scaling
factor.  In particular, $Q^\star(t;\Phi_{B,t})\ge0$ if and only if
\[
  \left\langle \bigl(T_M[P_A]-(2M+1)T_P^{\mathrm{Ray}}(t,M)\bigr)\,1,\,1\right\rangle_{L^2(\TT)}\ \ge\ 0.
\]
\end{theorem}

\begin{proof}
Applying Lemma~\ref{lem:a3-rayleigh-quotient} with $p\equiv1$ yields
\[
  \left\langle T_P^{\mathrm{Ray}}(t,M)\,1,\,1\right\rangle_{L^2(\TT)}
  = \frac{1}{2M+1}\sum_{n\ge2} w(n)\,\Phi_{B,t}(\xi_n),
\]
where the prime sum is finite because $\Phi_{B,t}$ is supported in $[-B,B]$.
By definition of $P_A$ and the normalization fixed in Section~\ref{sec:T0} one has
\[
  \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta
  = \int_{\RR} a_*(\xi)\,\Phi_{B,t}(\xi)\,d\xi,
\]
and Lemma~\ref{t0:lem:T0} gives
$Q^\star(t;\Phi_{B,t}) = \int_{-\tfrac12}^{\tfrac12}P_A(\theta)\,d\theta
       - \sum_{n\ge2}w(n)\,\Phi_{B,t}(\xi_n)$.
Multiplying the displayed identity for $\langle T_P^{\mathrm{Ray}}(t,M)1,1\rangle$ by $(2M+1)$ yields
the prime sum, proving the claim.
\end{proof}
```

### /Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A3/calibration.tex
```text
% A3 Calibration: explicit value of \kappa_{A3}
\input{sections/Notation/qstar_contract}
\subsection{A3 Calibration: The Constant \texorpdfstring{$\kappa_{\mathrm{A3}}(t)$}{κ\_A3(t)}}
\label{a3:sec:A3-calibration}
\SeeAlso{Normalization T0 Lemma~\ref{t0:lem:T0}, Toeplitz bridge A3 Theorem~\ref{thm:A3}.}

\begin{lemma}[Period-1 normalization audit]\label{lem:a3-period1-audit}
Let $g\in L^1(\RR)$ be even and define the period-$1$ symbol
\[
  P_A(\theta)\ :=\ 2\pi\sum_{m\in\ZZ} g(\theta+m),\qquad \theta\in[-\tfrac12,\tfrac12].
\]
Then
\[
  \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta
  \ =\ 2\pi\int_{\RR} g(\xi)\,d\xi,
\]
and the Fourier coefficients with respect to the basis $e^{2\pi i k\theta}$ satisfy
\[
  A_k\ =\ 2\pi\int_{\RR} g(\xi)\,e^{-2\pi i k\xi}\,d\xi,
  \qquad
  P_A(\theta)=A_0+2\sum_{k\ge1}A_k\cos(2\pi k\theta).
\]
In particular, with $g=a\,\Phi$ and $a_*(\xi)=2\pi a(\xi)$, the Rayleigh pairing matches
the T0-normalized Weil functional $Q^\star$ without further rescaling.
\end{lemma}
\begin{proof}
By Fubini and the change of variables $\xi=\theta+m$,
\[
  \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta
  = 2\pi\sum_{m\in\ZZ}\int_{-\tfrac12}^{\tfrac12} g(\theta+m)\,d\theta
  = 2\pi\int_{\RR} g(\xi)\,d\xi.
\]
The Fourier coefficient computation is identical, yielding the stated $A_k$ and cosine series.
\end{proof}

\begin{lemma}[Calibration of $\kappa_{\mathrm{A3}}$]\label{a3:lem:A3-kappa}
Let $\Phi(\xi)=(1-|\xi|/B)_+\,e^{-4\pi^2 t\,\xi^2}$ be an even Fej\'er$\times$heat window. Define the Arch coefficients
\begin{equation}\label{eq:A3_calibration_kappa-formula}
  A_k\ :=\ 2\pi\int_{\RR} a(\xi)\,\Phi(\xi)\,\cos(2\pi k\xi)\,d\xi,\quad
  P_A(\theta)\ :=\ A_0+2\sum_{k\ge1}A_k\cos(2\pi k\theta),
\end{equation}
with $a(\xi)=\log\pi-\Re\psi\big(\tfrac14+i\pi\xi\big)$, and let $T_P^{\mathrm{Ray}}(t)$ be the even prime sampling operator with weights $w(n)=\tfrac{2\Lambda(n)}{\sqrt n}$ at nodes $\xi_n=\tfrac{\log n}{2\pi}$. Then, in the Rayleigh identification of Theorem~\ref{thm:A3}, at the constant test $p\equiv1$ one has
\begin{equation}\label{eq:A3_calibration_kappa-formula-3}
  \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta\ -\ \sum_{n\ge2}\frac{2\,\Lambda(n)}{\sqrt n}\,\Phi(\xi_n)
  \ =\ \underbrace{\int_{\RR} a_*(\xi)\,\Phi(\xi)\,d\xi}_{\;=\ A_0}\ -\ \sum_{n\ge2}\frac{2\,\Lambda(n)}{\sqrt n}\,\Phi(\xi_n).
\end{equation}
By the T0 normalization (Lemma~\ref{t0:lem:T0}), the Weil functional on our axis is
\begin{equation}\label{eq:A3_calibration_kappa-q-functional-1}
  Q^\star(t;\Phi)\ =\ \int_{\RR} a_*(\xi)\,\Phi(\xi)\,d\xi\ -\ \sum_{n\ge2}\frac{2\,\Lambda(n)}{\sqrt n}\,\Phi(\xi_n),\qquad a_*(\xi):=2\pi\,a(\xi).
\end{equation}
Therefore
\begin{equation}\label{eq:A3_calibration_kappa-q-functional}
  Q^\star(t;\Phi)\ =\ \int_{-\tfrac12}^{\tfrac12} P_A(\theta)\,d\theta\ -\ \sum_{n\ge2}\frac{2\,\Lambda(n)}{\sqrt n}\,\Phi(\xi_n),
\end{equation}
and the bridge A3 introduces the fixed scale factor
\begin{equation}\label{eq:A3_calibration_kappa-formula-2}
\boxed{\ \kappa_{\mathrm{A3}}(t)\ =\ 1\ }\qquad\text{(independent of $t$)}.
\end{equation}
Equivalently, the normalization in \eqref{eq:A3_calibration_kappa-formula} absorbs the Jacobian $2\pi$ into the symbol coefficients, so $\kappa_{\mathrm{A3}}\equiv1$.
\end{lemma}
\phantomsection\label{a3:lem:rayleigh_sampling_id}

\begin{lemma}[Rayleigh identification (infinite-dimensional)]\label{lem:rayleigh-sampling}
For every even Fej\'er$\times$heat window $\Phi$ the operator form and the Weil functional satisfy
\[
  \Big\langle \bigl(T_M[P_A]-T_P^{\mathrm{Ray}}(t)\bigr) p,\,p\Big\rangle \;=\; Q^\star(t;\Phi)
\]
whenever $p$ corresponds to $\Phi$ via the standard Dirichlet sampling operator.
\emph{Note:} This is the infinite-dimensional idealization.  For the finite-dimensional
compression to $\mathcal P_M$, see Theorem~\ref{thm:a3-rayleigh-identification} where
the normalization of vectors introduces a factor $(2M{+}1)$.
\end{lemma}

\begin{proof}
Write the Fej\'er$\times$heat window as
\[
  \Phi(\xi)\ =\ \sum_{k\in\ZZ} \widehat \Phi(k)\,e^{2\pi i k\xi},\qquad
  \widehat \Phi(k) = \int_{\RR}\Phi(\xi)e^{-2\pi i k\xi}\,d\xi.
\]
The Dirichlet sampling operator maps $p(\theta)=\sum_{k\in\ZZ} \widehat \Phi(k)\,e^{2\pi i k\theta}$ to $\Phi$; hence
\[
  \Big\langle T_M[P_A]p,\,p\Big\rangle
  = \sum_{k\in\ZZ} A_k\,|\widehat \Phi(k)|^2
  = A_0\,|\widehat \Phi(0)|^2 + 2\sum_{k\ge1}A_k\,|\widehat \Phi(k)|^2,
\]
where $A_k$ are the Arch coefficients from \eqref{eq:A3_calibration_kappa-formula}.  Likewise, the
prime operator contributes
\[
  \Big\langle T_P^{\mathrm{Ray}}(t) p,\,p\Big\rangle
  = \sum_{n\ge2} \frac{2\,\Lambda(n)}{\sqrt{n}}\,\Phi(\xi_n)\,\overline{\Phi(\xi_n)}.
\]
Subtracting and recalling $Q^\star(t;\Phi)$ from \eqref{eq:A3_calibration_kappa-q-functional-1} gives
\[
  \Big\langle (T_M[P_A]-T_P^{\mathrm{Ray}}(t))p,\,p\Big\rangle
  = Q^\star(t;\Phi),
\]
which is the desired identity.
\end{proof}

\begin{proposition}[Bridge margin calibration]\label{prop:a3-calib}
Under the uniform floor $c_*>0$ from Lemma~\ref{lem:uniform-arch-floor} and the prime cap $\rho(t)\le c_*/4$, the mixed Toeplitz block satisfies
\[
  \lammin\!\bigl(T_M[\Pa]-T_P^{\mathrm{Ray}}(t)\bigr)\ \ge\ \frac{c_*}{4}
\]
for every $M\ge M_0^{\mathrm{unif}}$ in Theorem~\ref{thm:A3}.
\end{proposition}

\begin{proof}
Theorem~\ref{thm:A3} yields $\lammin(T_M[\Pa]-T_P^{\mathrm{Ray}}(t))\ge c_*-C_{\mathrm{SB}}\omega_{\Pa}(1/(2M))-\|T_P^{\mathrm{Ray}}(t)\|_{\op}$.
For $M\ge M_0^{\mathrm{unif}}$, Corollary~\ref{cor:uniform-discretisation} ensures $C_{\mathrm{SB}}\omega_{\Pa}(1/(2M))\le c_*/2$.
Corollary~\ref{cor:uniform-prime-cap} gives $\|T_P^{\mathrm{RKHS}}(t)\|_{\op}\le \rho(t) \le c_*/4$.
Thus $\lammin \ge c_* - c_*/2 - c_*/4 = c_*/4$.
\end{proof}

\begin{remark}[Evenization does not increase $C_0$]
In the T0 normalization we already place symmetric prime weights at $\pm\xi_n$ and integrate the zero counting measure $dN(\gamma)$ over the full real line. The diagonal constant on the zero side is therefore $C_0=\tfrac{1}{2\pi}$, not $\tfrac{1}{\pi}$. Passing to an evenized basis (replacing $\{+\tau,-\tau\}$ by a single cosine packet) redistributes mass within each pair but does not create an additional factor~2: the same symmetry is already built into T0 and into the A3 calibration. Consequently, with $\kappa_{\mathrm{A3}}=1$ the asymptotic PG--LS slope in Road~A is $1-\Lambda_0\nearrow1^-$ as $\Lambda_0\downarrow0$.
\end{remark}

\begin{remark}[Consequence for the PG--LS slope]
Let the zero-side packet Gram lower bound be normalized as
\(\sum_{\rho}\big|\sum_j c_j\,\widehat g_{\tau_j}(\gamma_\rho)\big|^2\ \ge\ \big(\tfrac{1}{2\pi}-\Lambda_0\big)\,\log(1{+}K)\,\sum_j|c_j|^2\ -\ C_{\mathrm{edge}}\sum_j|c_j|^2\).
Under A3 and T0 the prime-side gain is
\begin{equation}\label{eq:A3_calibration_kappa-formula-1}
 \Gamma(K)\ \ge\ \kappa_{\mathrm{A3}}\,\Big(\tfrac{1}{2\pi}-\Lambda_0\Big)\,\log(1{+}K)\ -\ \kappa_{\mathrm{A3}}\,C_{\mathrm{edge}}\ =\ \Big(\tfrac{1}{2\pi}-\Lambda_0\Big)\,\log(1{+}K)\ -\ C_{\mathrm{edge}},
\end{equation}
so the asymptotic slope approaches $1^{-}$ as $\Lambda_0\to0$. Hence a strict $>1$ cannot be achieved within Road A by only shrinking $\Lambda_0$; one needs an amplifier (e.g. Road B/C) or a different normalization.
\end{remark}
```

### /Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/RKHS/core.tex
```text
\input{sections/Notation/qstar_contract}
\subsection{RKHS Core}\label{sec:rkhs-core}

Our RKHS setup follows the classical foundation laid by Aronszajn~\cite{Aronszajn1950} and the modern expositions of Berlinet--Thomas-Agnan and Paulsen--Raghupathi~\cite{BerlinetThomasAgnan2004,PaulsenRaghupathi2016,Berlinet2004,Paulsen2016}.

Let $(\mathcal X,\mu)$ be a measure space and let $k\colon \mathcal X\times\mathcal X\to \RR$ be a positive definite kernel with reproducing kernel Hilbert space $(\mathcal H_k,\langle\cdot,\cdot\rangle_{\mathcal H_k})$. Denote by $T_k\colon L^2(\mu)\to L^2(\mu)$ the integral operator
\[
  (T_k f)(x)\ :=\ \int_{\mathcal X} k(x,y)\,f(y)\,d\mu(y).
\]
If $\mathcal X$ is represented discretely by nodes $\{x_i\}_{i=1}^N$ we write $K=[k(x_i,x_j)]_{i,j=1}^N$ for the Gram matrix.

\begin{lemma}[Energy identity]\label{lem:rkhs-energy}
For $f\in\mathcal H_k$ supported on the closure of $\mathrm{span}\{k(\cdot,x)\colon x\in\mathcal X\}$ one has
\[
  \|f\|_{\mathcal H_k}^2\ =\ \langle f,\,T_k^\dagger f\rangle_{L^2(\mu)},
\]
where $T_k^\dagger$ is the pseudoinverse on the image of $T_k$. In particular, if $f(x)=\sum_{i=1}^N a_i\,k(x,x_i)$ for a finite sample, then
\[
  \|f\|_{\mathcal H_k}^2\ =\ a^\top K a.
\]
\end{lemma}

\begin{lemma}[Spectral floor for Gram matrices]\label{lem:gram-min-eig-lb}
Assume the diagonal of $K$ obeys $k(x_i,x_i)\ge \czero$ and the off-diagonal mass satisfies
\[
  \sum_{j\neq i} \bigl|k(x_i,x_j)\bigr| \;\le\; \rhok
  \qquad\text{for every } i\in\{1,\dots,N\}.
\]
Then
\[
  \lammin(K) \;\ge\; \czero - \rhok.
\]
\end{lemma}

\begin{proof}
Gershgorin's circle theorem states that every eigenvalue $\lambda$ of $K$ belongs to at least one disc
\[
  D_i \ =\ \Bigl\{ z\in\CC : \bigl|z-k(x_i,x_i)\bigr| \le \sum_{j\neq i} |k(x_i,x_j)| \Bigr\}.
\]
The hypothesis guarantees $\inf D_i \ge \czero-\rhok$, hence every eigenvalue lies in $[\czero-\rhok,\infty)$.
\end{proof}

\begin{proposition}[Operator sandwich]\label{prop:operator-sandwich}
Let $T_k$ be positive on $\mathcal H_k$ with spectral bottom at least $\czero$, and suppose a discretisation or truncation $K$ satisfies the off-diagonal bound of Lemma~\ref{lem:gram-min-eig-lb}. For $f=\sum_i a_i k(\cdot,x_i)$ we have
\[
  \|f\|_{L^2(\mu)}^2 \;\le\; \frac{1}{\czero-\rhok}\,\|f\|_{\mathcal H_k}^2,
  \qquad
  \lammin(K) \;\ge\; \czero-\rhok.
\]
In particular, whenever $\rhok\le \czero/2$ the bridge margin $\tfrac12(\czero-\rhok)$ of Theorem~\ref{thm:A3} is available.
\end{proposition}
\phantomsection\label{a3:lem:weyl_rayleigh_diff}

\begin{proof}
Lemma~\ref{lem:gram-min-eig-lb} yields the spectral bound. Any $g=\sum_i a_i k(\cdot,x_i)$ satisfies $g^\top K g = \|g\|_{\mathcal H_k}^2$ by Lemma~\ref{lem:rkhs-energy}. Since $K\succeq (\czero-\rhok) I$, Rayleigh quotients yield $\|g\|_{L^2(\mu)}^2 \le (\czero-\rhok)^{-1}\|g\|_{\mathcal H_k}^2$.
\end{proof}

These statements provide the structural ingredients cited in Assumption~(A3.1) and in the proof of Theorem~\ref{thm:A3}: the diagonal floor produces $\czero$, the RKHS contraction supplies $\rhok$, and Lemma~\ref{lem:gram-min-eig-lb} transfers the margin to the finite Toeplitz block.

\begin{lemma}[Rayleigh sampling identification]\label{lem:rkhs-rayleigh-sampling-id}
For any Fej\'er$\times$heat window $\Phi=\Phi_{B,t}$ with Dirichlet sampling polynomial $p(\theta)=\sum_{k\in\ZZ}\widehat\Phi(k)e^{2\pi i k\theta}$, one has
\[
  \big\langle T_M[P_A]\,p,\,p\big\rangle_{L^2(\TT)}
  \;-\; (2M+1)\big\langle T_P^{\mathrm{Ray}}(t,M)\,p,\,p\big\rangle_{L^2(\TT)}
  \;=\; Q^\star(t;\Phi)
\]
whenever $M$ is large enough that the Dirichlet coefficients of $\Phi$ lie in the span $\{|k_\tau\rangle\}$. In particular, any estimate on the two quadratic forms
$\langle T_M[P_A]p,p\rangle$ and $\langle T_P^{\mathrm{Ray}}(t,M)p,p\rangle$ transfers directly to $Q^\star(t;\Phi)$ via the displayed identity.
\end{lemma}

\begin{remark}[Finite support and the threshold $M$]
A Fej\'er window of bandwidth $B$ has Fourier support contained in $\{|k|\le B\}$, and the subsequent heat factor $e^{-t k^2}$ only rescales these coefficients. Thus the Dirichlet polynomial $p$ is already finite, and it suffices to choose $M\ge B$ to meet the span condition used in Lemma~\ref{lem:rkhs-rayleigh-sampling-id}. The detailed identification is spelt out in Lemma~\ref{lem:a3-model-space}.
\end{remark}
```

### /Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex
```text
\input{sections/Notation/qstar_contract}
\subsection{Main closure: from centered packets to Weil positivity}\label{sec:Main-closure}

\subsection*{Standing contract}
For each compact window $[-K,K]$ we distinguish:
\[
  R_K := C^+_{\mathrm{even}}([-K,K]),
  \qquad
  B_K := \{\Phi\in C_c(\mathbb R): \operatorname{supp}\Phi\subset[-K,K],\ \Phi\ \text{even}\},
\]
and the corrected local Weil-positive cone
\[
  \widetilde{\psi}(x):=\overline{\psi(-x)},
  \qquad
  \mathcal W_{K,0}^{\mathrm{pd}}
  := \bigl\{\psi * \widetilde{\psi}:\ \psi\in C_c^\infty(\mathbb R),\ \operatorname{supp}\psi\subset[-K/2,K/2]\bigr\},
  \qquad
  \mathcal W_K^{\mathrm{pd}}
  := \overline{\operatorname{cone}\!\bigl(\mathcal W_{K,0}^{\mathrm{pd}}\bigr)}^{\|\cdot\|_\infty},
  \qquad
  \mathcal G_K^{\mathrm{pd}}
  := \operatorname{cone}\!\bigl\{\Phi_\Psi=\Psi*\widetilde{\Psi}:\ \Psi\in \mathcal P_K(t_0)\bigr\},
  \qquad
  \mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}
  := \operatorname{cone}\!\bigl\{\Phi_{B,t,p}=\Phi_{B,t}\,|p|^2:\ \Phi_{B,t}\ \text{centered Fej\'er$\times$heat},\ p\in\mathcal P_M\bigr\},
  \qquad
  J\subset\mathbb Z\ \text{finite admissible dictionary},
  \qquad
  D(J):=\{i-j:\ i,j\in J\},
  \qquad
  \Psi_c(x):=\sum_{j\in J} c_j\,g(x-j\Delta),
  \qquad
  h:=g*\widetilde g,
  \qquad
  \kappa_m:=\mathcal Q(h(\cdot-m\Delta)),
  \qquad
  A_J(\theta):=\sum_{m\in D(J)}\alpha_m e^{-im\theta},
  \qquad
  P_J(\theta):=\sum_{m\in D(J)}\beta_m e^{-im\theta},
  \qquad
  S_J(\theta):=A_J(\theta)-P_J(\theta),
  \qquad
  S_{g,\Delta}(\theta):=\sum_{m\in\mathbb Z}\kappa_m e^{-im\theta},
  \qquad
  A_{J,r}:=P_r*A_J,
  \qquad
  P_{J,r}:=P_r*P_J,
  \qquad
  S_{J,r}:=P_r*S_J,
  \qquad
  K_Q(g_i,g_j):=\mathcal Q(g_i * \widetilde{g_j}),
  \qquad
  \mathcal W^{\mathrm{pd}}:=\varinjlim_{K\to\infty}\mathcal W_K^{\mathrm{pd}}.
\]
The current draft already supplies:
\begin{itemize}
  \item \textbf{(T0)} the Guinand--Weil crosswalk, cf.\ Proposition~\ref{prop:T0-GW};
  \item \textbf{(A1$'$)} auxiliary density of shifted evenized Fej\'er$\times$heat atoms on the broad restriction cone $R_K$, cf.\ Theorem~\ref{a1:thm:A1-local-density};
  \item \textbf{(A2)} continuity of $Q^\star(t;\cdot)$ on the ambient compact-support class $B_K$, cf.\ Section~\ref{sec:A2};
  \item \textbf{(A3)+(RKHS)} the centered positivity mechanism at the critical scale.
\end{itemize}

What remains unresolved in the corrected route is now sharply localized:
\begin{itemize}
  \item \textbf{(compact spectral route, diagnostic package)} The scalar spectral package
  \[
    \textup{S1 exact compact spectral identity}
    \Longrightarrow
    \textup{S2 spectral positivity criterion}
    \Longrightarrow
    \textup{S3 corrected compact positivity from }W_K(u)\ge0.
  \]
  This route attacks one scalar spectral weight per compact,
  \[
    W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}\frac{2\Lambda(n)}{\sqrt n}\cos(u\xi_n),
  \]
  and is therefore the primary constructive theorem shape.
  \item \textbf{(A1-pd)} The centered density family $\mathcal G_K^{\mathrm{pd}}$ is the corrected local dense family.
  \item \textbf{(packet-Rayleigh-naive, background candidate)} The naive family $\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}$ is mathematically natural, but it is too large to serve as the closure family.
  \item \textbf{(packet-Rayleigh-pd)} Exact Toeplitz quadratic-form identification on autocorrelation packets $\Psi_c * \widetilde{\Psi_c}$ is the honest bridge on the corrected cone.
  \item \textbf{(A3-pd, rejected theorem shape)} A uniform packet-symbol floor on the whole dense packet dictionary is too strong to be the live theorem.
  \item \textbf{(PSD-pd)} The remaining hard theorem is positive semidefiniteness of the packet kernel
  $K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})$ on a dense
  translation-compatible packet subspace feeding the corrected cone.
  \item \textbf{(finite P7, fallback discretization route)} For a fixed finite admissible packet dictionary, the fallback constructive target is the finite symbol
  $S_J(\theta)=A_J(\theta)-P_J(\theta)$ together with a Poisson-regularized
  verification step and explicit error budget. This route is now retained as a dictionary-level approximation / stress-test package for the scalar spectral route.
  \item \textbf{(bound package)} The immediate quantitative task is now a packet-level analogue of the old centered bridge:
  diagonal Archimedean core mass, off-diagonal Archimedean leakage, local prime
  collision mass, and the resulting explicit finite-dictionary inequalities
  \textup{(C1)} and \textup{(C1$'$)}.
  \item \textbf{(LF-pd)} Once local positivity on every $\mathcal W_K^{\mathrm{pd}}$ is available, lift it to the global cone $\mathcal W^{\mathrm{pd}}$.
\end{itemize}

\begin{lemma}[Naive packet-Rayleigh candidate]\label{lem:packet-rayleigh-identification}
For every compact window $[-K,K]$, every centered Fej\'er$\times$heat window $\Phi_{B,t}$, and every trigonometric polynomial $p\in\mathcal P_M$, define
\[
  \Phi_{B,t,p}(\xi):=\Phi_{B,t}(\xi)\,|p(\xi)|^2.
\]
Then
\[
  Q^\star(t;\Phi_{B,t,p})
  =
  2\pi\,
  \bigl\langle (T_M[P_A]-T_P^{\mathrm{Ray}}(t,M))\,p,\ p\bigr\rangle_{L^2(\mathbb T)}.
\]
Equivalently, positivity of the centered Toeplitz/RKHS quadratic form on the packet span yields
\[
  Q^\star(t;\Phi)\ge 0\qquad\text{for every }\Phi\in\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}.
\]
\end{lemma}

\begin{remark}[Why the naive candidate is too large]
The present draft already points toward Lemma~\ref{lem:packet-rayleigh-identification}:
Lemma~\ref{lem:a3-rayleigh-quotient} gives the quadratic Rayleigh pairing for arbitrary
trigonometric polynomials, while Theorem~\ref{thm:a3-rayleigh-identification} is the
special case $p\equiv1$ for a single centered Fej\'er$\times$heat window. What is
mathematically natural here is the family $\Phi_{B,t}|p|^2$. But on compact windows
$K<\pi$, a fixed centered window $\Phi_{B,t}$ with $B>K$ is strictly positive on
$[-K,K]$, and even real trigonometric polynomials are uniformly dense on that
interval. Hence $\Phi_{B,t}r^2$ is already dense in the broad local cone of even
nonnegative bumps. Combined with the full quadratic-form meaning of
Lemma~\ref{lem:packet-rayleigh-identification} and the centered A3 positivity
engine, this would force false broad local positivity. Therefore
$\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}$ is background-only. The live task is not
to salvage that overlarge family, but to prove PSD of the packet kernel on the
exact dense autocorrelation packet family from A1-pd.
\end{remark}

\begin{definition}[Symmetric packet extension of the compact Weil functional]\label{def:Q-symmetric-extension}
For a compactly supported test $F\in C_c(\mathbb R)$, define
\[
  \mathcal Q(F)
  :=
  \int_{\mathbb R} a^*(\xi)\,F(\xi)\,d\xi
  -
  \frac12\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}\bigl(F(\xi_n)+F(-\xi_n)\bigr).
\]
If $F$ is even, then $\mathcal Q(F)=Q^\star(t;F)$.
\end{definition}

\begin{lemma}[P1: exact packet sesquilinear identity]\label{lem:packet-sesquilinear}
Fix $K>0$ and let $\Psi,\Phi\in C_c([-K/2,K/2])$. Set
\[
  \widetilde{\Phi}(x):=\overline{\Phi(-x)},
  \qquad
  K_Q(\Psi,\Phi):=\mathcal Q(\Psi * \widetilde{\Phi}).
\]
Then
\[
  K_Q(\Psi,\Phi)
  =
  \iint_{\mathbb R^2} a^*(x-y)\Psi(x)\overline{\Phi(y)}\,dx\,dy
  -
  \frac12\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}
  \Bigl(
    \langle \Psi,T_{\xi_n}\Phi\rangle
    +
    \langle \Psi,T_{-\xi_n}\Phi\rangle
  \Bigr),
\]
where the prime sum is finite on the fixed compact window.
\end{lemma}

\begin{proof}
By definition,
\[
  (\Psi * \widetilde{\Phi})(\xi)
  =
  \int_{\mathbb R}\Psi(x)\overline{\Phi(x-\xi)}\,dx.
\]
Substituting this into the compact-window formula for $\mathcal Q(\cdot)$ and
interchanging integrals gives the Archimedean term. On the fixed compact only
finitely many prime nodes $\pm\xi_n$ are active, so the prime term is finite
and the same substitution yields the displayed identity.
\end{proof}

\begin{theorem}[P2: Toeplitz reduction on a finite translation packet dictionary]\label{thm:packet-rayleigh-pd}
Let $g\in C_c(\mathbb R)$, let $\Delta>0$, let $J\subset\mathbb Z$ be finite, and let
\[
  g_j(x):=g(x-j\Delta),
  \qquad
  \Psi_c(x):=\sum_{j\in J} c_j\,g_j(x),
  \qquad
  h:=g*\widetilde g,
  \qquad
  D(J):=\{i-j:\ i,j\in J\}.
\]
Set
\[
  \kappa_m:=\mathcal Q(h(\cdot-m\Delta))
  \qquad (m\in D(J)).
\]
Then
\[
  \mathcal Q(\Psi_c * \widetilde{\Psi_c})
  =
  \sum_{i,j\in J} \kappa_{i-j} c_i\overline{c_j}.
\]
\end{theorem}

\begin{proof}
Expand
\[
  \Psi_c * \widetilde{\Psi_c}
  =
  \sum_{i,j\in J} c_i\overline{c_j}\,
  g_i*\widetilde{g_j}
  =
  \sum_{i,j\in J} c_i\overline{c_j}\,
  h(\cdot-(i-j)\Delta).
\]
Applying linearity of $\mathcal Q(\cdot)$ gives
\[
  \mathcal Q(\Psi_c * \widetilde{\Psi_c})
  =
  \sum_{i,j\in J} c_i\overline{c_j}\,\kappa_{i-j}.
\]
\end{proof}

\begin{proposition}[P3: desired PSD factorization of the packet prime block]\label{prop:desired-prime-factorization}
Fix a dense packet space $\mathcal P_K\subset C_c([-K/2,K/2])$ and define
\[
  K_P(\Psi,\Phi)
  :=
  \frac12\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}
  \bigl((\Psi * \widetilde{\Phi})(\xi_n)+(\Psi * \widetilde{\Phi})(-\xi_n)\bigr).
\]
If there exist a Hilbert space $\mathcal H_{P,K}$ and a map
$J_K:\mathcal P_K\to\mathcal H_{P,K}$ such that
\[
  K_P(\Psi,\Phi)=\langle J_K\Psi,J_K\Phi\rangle_{\mathcal H_{P,K}}
\]
for all $\Psi,\Phi\in\mathcal P_K$, then the packet prime block is positive
semidefinite on $\mathcal P_K$.
\end{proposition}

\begin{proof}
This is immediate from the Hilbert-space representation: every finite matrix
$[K_P(\Psi_i,\Psi_j)]$ is then a Gram matrix.
\end{proof}

\begin{lemma}[P5: decomposition of the full packet Toeplitz sequence]\label{lem:packet-symbol-decomposition}
Writing
\[
  \alpha_m:=\int_{\mathbb R} a^*(\xi)\,h(\xi-m\Delta)\,d\xi,
  \qquad
  \beta_m:=\frac12\sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}
  \Bigl(h(\xi_n-m\Delta)+h(\xi_n+m\Delta)\Bigr),
\]
one has $\kappa_m=\alpha_m-\beta_m$, and
the packet symbol splits as
\[
  S_{g,\Delta}(\theta)=A_{g,\Delta}(\theta)-P_{g,\Delta}(\theta),
\]
where
\[
  A_{g,\Delta}(\theta)
  :=
  \sum_{m\in\mathbb Z} \alpha_m e^{-im\theta},

[truncated after 260 lines]
```

### /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md
```text
# Session Entry (2026-03-08)

Это главный session-entry файл для Q3. Начинать новую сессию надо с чтения
именно его.

## Кто мы и что делаем

Мы ведём один проект:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026`

Цель сейчас не “заявить доказательство RH”, а максимально быстро двигать
вперёд **правдоподобный и математически честный route** внутри Q3:
текст, Lean, control-plane и embeddings должны оставаться синхронными.

## Обязательный read order

1. `SESSION_ENTRY.md`
2. `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
3. `IMPLEMENTATION_PLAN.md`
4. `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
5. `q3.lean.aristotle/docs/INSIGHTS.md`

Если работаешь с embeddings / incoming notes, потом ещё:

6. `q3.lean.aristotle/docs/EMBEDDING_INGEST_WORKFLOW.md`

Если работаешь с Aristotle:

6. `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md`
7. `q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`

## Текущий public mainline

Текущий публичный маршрут проекта:

`T0-pd -> H-bridge -> H4 -> RH`

Где

- `H-bridge` = Suzuki/Yoshida generalized form-pair bridge
  `H1^f -> H2^f -> H3^f -> H4^f`;
- `H1^f` = exact filtered bulk intertwining on the symmetric two-sided tail
  package, so that strongest finite Q3 block is compared not to raw `Q_M`, but
  to the filtered tail section `\widetilde Q_{M,N}`;
- preferred first-pass candidate for `H1^f`:
  two-sided filtered Volterra bridge with
  `J_a=(I_0^{(a)})^*I_0^{(a)}`,
  tail model space `\mathcal P_{M,N}`,
  symmetric filtered shift `\Delta_{M,N}`,
  packet states `\phi_n^\pm[a]`,
  synthesis `S_{a,M,N}`,
  exact pullback metric
  `B_{M,N}=S_{a,M,N}^*J_aS_{a,M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  and preferred filtered bridge-object
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- semilocal cyclic/Jacobi machinery stays useful, but only as a secondary
  finite-prime basis/Gram supplier for `H1^f`, not as a new RH endgame.

Точный theorem stack, который сейчас заморожен как primary live route:

- `H1^f` exact filtered bulk intertwining
- `H2^f` Suzuki tail/cap reduction
- `H3^f` filtered gap transfer
- `H4^f` RH via Suzuki Theorem 1.4

Что сейчас не является public mainline:

- `S1/S2/S3/S4` — правильный, но diagnostic-only compact-truncation package;
- `PSD-pd` — честный fallback Weil-side route, если `H1` stalled.

## Текущий практический next step

Если нет нового user redirect, текущий честный frontier такой:

- symmetric two-sided filtered H-bridge:
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`,
  `B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- next exact blocker:
  raw bulk identity
  `w_{rs}(a)=\kappa(a)q_{rs}`
  on the two raw families `(+,+)` and `(+,-)`,
  where `q_{rs}=\langle Q e_s,e_r\rangle` on the Section 8 side and
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})` on the Suzuki side;
- derived filtered consequence:
  the four bulk blocks
  `M^{++}, M^{+-}, M^{-+}, M^{--}`
  versus the corresponding blocks of `\kappa(a)\widetilde Q_{M,N}`,
  with `(--),(-+)` obtained from `(++),(+-)` by
  conjugation/self-adjoint symmetry;
- after the raw bulk match:
  separate finite-dimensional Suzuki cap positivity;
- semilocal-assisted refinement after that:
  finite-prime packet states `\eta_m^{(S,a)}`, Gram matrix
  `\Gamma_{a,M}^{(S)}`, and normalized synthesis
  `\widetilde S_{a,M}^{(S)}` only as engineering support for the same `H1^f`.

## Самые важные правила мышления

1. Не чинить то, что уже переведено в background-only.
2. Не возвращать broad-cone `W_K / W` как публичный RH-contract.
3. Не притворяться, что проект уже замкнут.
4. Не открывать новый архитектурный pivot без явного theorem memo и sync в control docs.
5. Самый быстрый путь — тот, который:
   - математически честен,
   - повторно использует уже доказанные модули,
   - не плодит новые необязательные слои.

## Что сейчас source of truth

При конфликте файлов порядок такой:

1. `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
2. `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
3. `IMPLEMENTATION_PLAN.md`
4. `q3.lean.aristotle/docs/INSIGHTS.md`

Коротко:

- orchestrator решает frontier и gate-state;
- tracker решает paper typing / theorem map;
- implementation plan решает ровно текущую очередь;
- insights ничего не переопределяет.

## Как работать по сессии

### Если задача математическая / theorem-level

1. Прочитать `PROJECT_ORCHESTRATOR.md`.
2. Найти active gate в `IMPLEMENTATION_PLAN.md`.
3. Проверить, не решён ли уже этот кусок в `docs/INSIGHTS.md` или `docs/insights/`.
4. Только потом писать новый theorem note / manuscript patch / Lean patch.
5. После значимого шага:
   - `lake env lean Q3/Main.lean`
   - `#print axioms Q3.Main.RH_of_Weil_and_Q3`
   - если менялся paper: `latexmk -pdf full/RH_Q3.tex`

### Если задача про incoming notes / embeddings

Сначала проверь статус inbox:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/ingest_incoming_notes.py status
```

Если inbox пуст:
- ничего не инжестить;
- это значит, что raw inbox уже разобран или заархивирован;
- ждём новый материал.

Если inbox не пуст, canonical loop такой:

```bash
./scripts/ingest_incoming_notes.py prepare docs/incoming_notes/<file-or-zip>
python3 -u ./scripts/refresh_q3_docs.py
python3 -u ./scripts/research_oracle.py query "<query>" -c q3_docs -n 5
```

Но важно:

- raw никогда не идёт в embeddings напрямую;
- только reviewed note с
  - `review status: reviewed`
  - `safe for embeddings: yes`
- после review raw уходит в archive, не удаляется.

Для этого есть локальный skill:

- `/Users/emalam/.codex/skills/q3-note-ingest/SKILL.md`

## Repo map (только живой минимум)

### Control plane

- `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `IMPLEMENTATION_PLAN.md`
- `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
- `q3.lean.aristotle/docs/INSIGHTS.md`

### Manuscript

- `full/RH_Q3.tex`
- `full/sections/Main_closure.tex`
- `full/sections/Weil_pack.tex`
- `full/sections/Weil_linkage.tex`
- `full/sections/Notation/qstar_contract.tex`
- `full/sections/A1prime.tex`

### Lean entry

- `q3.lean.aristotle/Q3/Main.lean`

### Active pipeline / KB

- `q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md`
- `q3.lean.aristotle/docs/EMBEDDING_INGEST_WORKFLOW.md`
- `q3.lean.aristotle/scripts/ingest_incoming_notes.py`
- `q3.lean.aristotle/scripts/refresh_q3_docs.py`
- `q3.lean.aristotle/scripts/research_oracle.py`

## Проверки, которые надо помнить

### Lean

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
lake env lean Q3/Main.lean
printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin
```

Ожидаемый current profile:

- `propext`
- `Classical.choice`
- `Quot.sound`
- `Q3.Weil_criterion`
- `Q3.prime_term_le_at_t_critical_axiom`

### TeX

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/full
latexmk -pdf RH_Q3.tex
```

### Embeddings

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/ingest_incoming_notes.py status
python3 -u ./scripts/refresh_q3_docs.py
python3 -u ./scripts/research_oracle.py query "<query>" -c q3_docs -n 5
```

## Что не делать

- Не опираться на старый broad-cone route как на public RH contract.
- Не возвращать в mainline T5/Acceptance/legacy status narratives.
- Не засовывать raw chats или zip extracts напрямую в `q3_docs`.
- Не создавать новый архитектурный pivot без sync в manuscript + control plane.
- Не коммитить skill-файлы из `~/.codex/skills` в repo.

## Текущий практический next step

Если нет нового user redirect, текущий честный frontier такой:

- symmetric two-sided filtered H-bridge:
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`,
  `B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`;
- next exact blocker:
  raw bulk identity
  `w_{rs}(a)=\kappa(a)q_{rs}`
  on the two raw families `(+,+)` and `(+,-)`,
  where `q_{rs}=\langle Q e_s,e_r\rangle` on the Section 8 side and
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})` on the Suzuki side;
- derived filtered consequence:
  the four bulk blocks

[truncated after 260 lines]
```
