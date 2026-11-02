# Capacity conditioning: definitions and theorem boundary

Read-only normalization/interface review. No new numerical computation,
cofinal theorem, or Git operation.

## 1. Raw evaluation map and active complement

Keep the literal unit physical even basis

`φ_n(x)=d_n(−1)^n cos(2πnx/L)/√L`, `|x|≤L/2`,
`d_0=1`, `d_n=√2` for n>0, zero outside; `L=log m`, `d=m+1`.
Let `Ω_m=2πm/L`. E has one raw Fourier-evaluation row at every retained
positive ordinate `γ_k<T=κΩ_m`, with the strict endpoint convention.

`E_kn=φ̂_n(γ_k)`, `φ̂_n(t)=∫φ_n(x)exp(−itx)dx`.

There is no row normalization, local-spacing weight, H normalization, or
`1/√(2π)` factor. Such changes would define a different Euclidean capacity
map and generally change its singular values and left vectors.

Set `s=rank E`, `J=ker E`, `r=d−s`, and choose a d×s matrix U with orthonormal
columns spanning `J⊥=range(E*)`. Define `F=EU`.
Then

`E=FU*`, `FF*=EE*`, `F*F=U*E*EU`.

Thus the s singular values of F are exactly the nonzero singular values of E,
independently of the choice of the orthonormal frame U. An explicit polynomial
or interpolation basis must first be orthonormalized in the physical metric;
its raw coefficient matrix does not have this invariance. Exact rank and
numerical rank are separate: record the resolution threshold and precision
stability for any computed active complement.

## 2. Factor2 and comparison with the full Weil matrix

The source explicit formula counts both signs of every critical ordinate.
On the even carrier the two evaluations coincide. Consequently the retained
critical-zero quadratic form is **2E*E**. The factor2 is required; there is no
Parseval `2π` divisor in this discrete zero sum. Pole and prime compensation
already belongs to the full arithmetic matrix A and is not added again.
See `capacity_matrix_2026-11-02/NORMALIZATION.md` for the pinned source lines.

The smallest active singular value gives the exact retained-sample floor

`β=2σ_min(F)²=min_(f∈J⊥,||f||=1) 2||Ef||²`.

For ordered A eigenvalues `λ_0≤…≤λ_(d−1)`, the first index beyond an
r-dimensional proposed quiet space is **λ_r**, with zero-based indexing.
Comparing β with that eigenvalue is a useful finite diagnostic. It does not
by itself identify J with A's low eigenspace or prove a complement floor
for the full A.

Write `R=A−2E*E`. Actual complement coercivity requires control of

`U*AU=2F*F+U*RU`.

The omitted zero contributions can include off-critical terms, so R cannot
be declared positive semidefinite unconditionally. A sufficient independent
budget is `U*RU≥−ηI` with `β−η≥μ>0`. Once actual complement coercivity
`U*AU≥μI` is proved, min–max gives `λ_r(A)≥μ` and hence the signed count
`#{λ(A)<μ}≤r`; no separate cross-block premise is needed for that min–max
statement. Cross-block coupling still enters the **full residual** `||A|_J||`
required by NOESCAPE L12/L13 and cannot be replaced by a compressed-J energy.

In particular a compressed complement measurement alone does not control the
negative bottom or establish a cofinal lower floor. A small measured σ_min,
or a comparison ratio at two finite carriers, is not an analytic conditioning
supplier either.

## 3. Which singular vector lives where?

For `F=Y Σ Z*`:

- the smallest **left** singular vector is a q-component vector indexed by
  retained zero rows; its squared components are zero-index weights;
- the corresponding **right** singular vector is an s-component vector in
  the chosen U frame; the physical carrier direction is `U z_min`.

Their pairing is `F z_min=σ_min y_min` and
`F* y_min=σ_min z_min`. Right coordinates alone depend on the choice of U;
the physical direction U z_min is invariant up to phase when the singular
value is simple. Near degeneracy requires a singular-subspace/projector
comparison rather than a canonical individual direction.

Two large left weights indicate a mixture of two evaluation rows. The two
largest-weight zero indices need not be adjacent in ordinate order. If they
are not adjacent, their difference is not a nearest-neighbor zeta gap, and
the intervening zero ordinates must not be silently skipped. Their phases
or signs matter to cancellation; weights alone do not determine it.

## 4. Gap statistic and cutoff boundary

For each retained distinct ordinate, use its **actual** nearest-neighbor gap
in the complete positive-ordinate list:

`g_k=min(γ_k−γ_(k−1), γ_(k+1)−γ_k)` for k>1,
`g_1=γ_2−γ_1`.

The next ordinate after the last retained row must be available even if it
lies at or beyond T. Otherwise the cutoff can artificially enlarge the last
reported gap. Likewise γ_2 is needed if only the first row is retained.
This convention uses positive neighbors, not the distance to the negative
partner of the first zero. Store which adjacent pair supplies each minimum;
the same close pair can flag two rows.

The proposed flag `g_k L/(2π)<0.3` measures closeness relative to the carrier's
Fourier lattice spacing `2π/L`. It is a **diagnostic carrier-dependent gap
flag**, not the classical Lehmer-pair criterion or a theorem about close
zeros. A large left singular weight at a flagged row does not prove that the
conditioning is caused by that pair. Conversely its two strongest rows may
be widely separated and unflagged.

## 5. What the new source audit supplies—and does not

Source read: commit `e724ae65ed39a8ba8b8f07c928d790ea9820342a`,
`docs/routeB_bus/proshka/SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_PAPER_AUDIT_2026-11-02.md`,
blob `4e6165039aaa6e5d52774413ca39de596be409bd`,
SHA256 `a52f2fd910bf298ae54b0a96fa4a3d31045aa278f6224c4ff3f3b1040ec30081`.
It audits Proshka source `2176dab16bf77dd015f7efcb5a6f704587f732c8`,
blob `ebf7f8cab61a795118bda5dc7e65a0b3386247b7`.

The accepted scoped supplier is a cofinal **rank lower bound and vanishing
full-operator residual on a moving quiet space**, using all actual complex
zeros in its cutoff and a specified shrinking-κ schedule. It is not a theorem
that finite critical-line evaluation rows exhaust those constraints at every
height, nor a numerical onset guarantee for the small cells.

Its relative Gram inequality is
`B* A² B≤δ² B*B` for a synthesis B of the quiet space. That B*B is the
**quiet-basis synthesis Gram**, not the capacity Gram E*E or the active
complement matrix F*F. The audit supplies no positive lower bound for
σ_min(F), no full-A complement coercivity, and no signed upper spectral count.
It explicitly leaves saturation and RH unproved.

**Verdict:** the finite SVD/gap experiment measures the correct missing
conditioning quantity when these definitions are retained. It remains a
diagnostic; the new rank/residual audit does not supply its proposed
conditioning or complement-coercivity bound.
