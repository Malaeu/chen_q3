# Codex report — Goal 058 curvature bordered secular preflight

Date: 2026-09-03

```yaml
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
```

## Part A — exact source preflight

Work in the normalized even basis

\[
e_0,\qquad e_n^+=(e_n+e_{-n})/\sqrt2,\quad 1\le n\le N,
\]

and put

\[
d_n=L^2+16\pi^2n^2,\quad
C_0=\frac{4\sinh(L/4)}{\sqrt L},\quad
C_n=\frac{4\sqrt L\sinh(L/4)L}{d_n},\quad
u_n=\sqrt2C_n.
\]

The literal `ccmW02Entry` source formula gives

\[
b_{\rm pole,n}=\sqrt2W_{0,2}(0,n)
=2C_0u_n
=\frac{32\sqrt2L\sinh^2(L/4)}{d_n},
\]

and

\[
(D_{\rm pole})_{nr}=W_{0,2}(n,r)+W_{0,2}(n,-r)
=2u_nu_r
=\frac{64L^3\sinh^2(L/4)}{d_nd_r}.
\]

Thus the exact source split is

\[
b=b_{\rm pole}+b_{\rm AP},\qquad
D=D_{\rm pole}-D_{\mathbb R}-D_P,
\]

with

\[
b_{\rm AP,n}=-\sqrt2\bigl(W_{\mathbb R}(0,n)+P(0,n)\bigr).
\]

After resolving the signs in the literal source constructors, the center-column
formula is

\[
b_n=\sqrt2\left[
\frac{32L\sinh^2(L/4)}{d_n}
+\frac{I_n}{2\pi n}+\frac{P_n}{\pi n}
\right],
\]

where

\[
I_n=\int_{(0,L]}\frac{e^{x/2}\sin(2\pi nx/L)}{\sinh x}\,dx,
\qquad
P_n=\sum_{k=2}^{m}\frac{\Lambda(k)}{\sqrt k}
\sin\!\left(\frac{2\pi n\log k}{L}\right).
\]

The displacement theorem

\[
XK-KX=\beta\eta^T-\eta\beta^T,
\qquad \beta_n=n\tau(n,0),
\]

recovers this center column and the Cauchy-like off-diagonal entries. It does
not relate the second-jet row

\[
c_n=\frac{\sqrt2}{2\pi^2n^2}
\]

to `β`, and on the parity split `X` exchanges the even and odd sectors. It
therefore does not close an inverse identity inside the even complement.

The exact bordered slope at the ground root is

\[
\partial_t\Phi(0,\lambda_1)
=\frac16
-2\langle c,(D-\lambda_1I)^{-1}b_{\rm pole}\rangle
-2\langle c,(D-\lambda_1I)^{-1}b_{\rm AP}\rangle.
\]

There is no source-level leading cancellation before an estimate. The first
surviving source-dependent term is

\[
-2\langle c,(D-\lambda_1I)^{-1}b_{\rm pole}\rangle,
\quad
b_{\rm pole,n}=\frac{32\sqrt2L\sinh^2(L/4)}{L^2+16\pi^2n^2}.
\]

The first non-pole survivor is the same mixed pairing with the explicit
integral-plus-von-Mangoldt row `b_AP` above. Neither the rank-two pole formula
nor `ccmWeilMatFinite_commutator` evaluates either pairing.

For the plant

\[
K_t=\begin{pmatrix}\lambda+b^2/t&b\\b&\lambda+t\end{pmatrix},
\qquad t>0,
\]

`λ` is the simple lowest eigenvalue when `b ≠ 0`, while

\[
S(\lambda)=cb/t
\]

has arbitrary scale. Hence any slope bound using only generic Schur,
Loewner, displacement-rank, or secular structure is rejected.

`R2_SECULAR_DERIVATIVE_ONLY_RENAMES_CURVATURE`

## Part B — Lean bookkeeping

File:
`q3.lean.aristotle/Q3/Proofs/RouteB/Goal058CurvatureBorderedSecular.lean`

Commit: `36c3812a`

Kernel-checked declarations:

1. `ccmW02Entry_rank_two_factorization` and
   `ccmW02Matrix_rank_two_factorization`: exact finite rank-two `W02` split.
2. `det_ccmCenterBlock` and `det_ccmCenterBlock_shifted`: scalar-center Schur
   determinant identities through `Matrix.det_fromBlocks₂₂`.
3. `ccmBorderedDeformation` and `det_ccmBorderedDeformation_div`: the exact
   curvature-specific bordered matrix and its normalized determinant.
4. `ccmBorderedPhi_hasDerivAt` and
   `curvature_pairing_eq_half_borderedPhi_deriv`: derivative
   `1/6 - 2⟨c,Rb⟩` and the half-slope curvature identity.
5. `finiteOddInterpolant_spec`, `ccm_evenSector_dividedDifference`, and
   `ccm_oddSector_dividedDifference`: one noncanonical finite squared-node
   interpolant with exact even symbol `u h(u)` and odd symbol `h(u)` formulas.

The interpolation theorem deliberately claims only a fixed finite
interpolant. It does not claim a canonical continuum `h`, diagonal Hermite
matching, operator monotonicity, or a cofinal estimate.

Validation:

- direct `lake env lean`: PASS;
- named target build: PASS (`7746/7746` jobs);
- `scripts/q3_check.sh`: PASS;
- strict Spine refresh: PASS after the required `semantic-index-refresh` reason;
- holes: none;
- printed axiom profile for every public theorem: only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Part C — Probe 7

Script: `docs/routeB_bus/phase5_codex/slope_split.py`

The script imports the unmodified production `CCMArbBuilder`, uses the exact
even-basis split

\[
b_{\rm pole,n}=\sqrt2W_{0,2}(0,n),\qquad
b_{\rm AP,n}=-\sqrt2(W_{\mathbb R}(0,n)+P(0,n)),
\]

and solves the two shifted systems with
`arb_mat.solve(algorithm="precond")`. Every cell also passes a direct third
solve for the unsplit center column.

| m=N | dps | `S_pole/(1/12)` | `S_AP/(1/12)` | `(1/12-S_pole)L²` | `1/12-S` |
|---:|---:|---:|---:|---:|---:|
| 13 | 240 | `3.4246752128473e22` | `-3.4246752128473e22` | `-1.8775682556955e22` | `0.00787244394607055` |
| 23 | 240 | `5.5961380291029e42` | `-5.5961380291029e42` | `-4.5847871658681e42` | `0.00534272221390689` |
| 43 | 240 | `6.4912562635524e80` | `-6.4912562635524e80` | `-7.6524480537355e80` | `0.00365359998000530` |
| 83 | 360 | `2.8397279736653e151` | `-2.8397279736653e151` | `-4.6207467460795e151` | `0.00257788335002556` |

All four values of `1/12-S` agree with the frozen Probe-5 `a1/xi0` reference
to at least eight significant digits. The pole and Arch-prime pieces are
individually enormous and cancel each other. The pole piece is neither close
to `1/12` nor negligible, so neither decisive condition in ADDENDUM 8 holds.

`P_POLE_PART_CARRIES_ONE_TWELFTH: UNRESOLVED`

Outputs:

- `docs/routeB_bus/phase5_codex/out/slope_split.json`
- `docs/routeB_bus/phase5_codex/out/slope_split.md`

`DIAGNOSTIC_NEVER_A_PROOF`. No cofinal quantifier is inferred from these four
cells.

## Follow-up analytic attack

The source split kills the hope that the pole term alone carries the
`1/12`. A useful next attack must expose the exact pole-versus-Arch-prime
cancellation before solving the nearly singular complement: either derive a
joint source identity for their combined center column under the full signed
Weil action, or rewrite the mixed pairing as a scalar moment whose arithmetic
integral and von-Mangoldt pieces cancel termwise or by a proved summation
formula. Reapplying a generic Schur identity, bounding the full complement
inverse, or assuming an absolute spectral floor would only reintroduce the
wall ruled out by Part A.
