# STATUS: TRY_SOURCE_PRIMITIVE_NULL_RIGIDITY_AFTER_HODGE_STRIP
```yaml
OPERATIVE_CLASS: TRY_SOURCE_PRIMITIVE_NULL_RIGIDITY_AFTER_HODGE_STRIP
PRIMARY_COUNT: 1
SCOPE: ABSTRACT
VERIFIER: PAPER
REQUEST_ID: REQ-2026-09-08-HODGE
BOUNDARY_ID: GOAL058_HODGE_TRANSPLANT_TEST_MINIMAL_SIGN_LEMMA_AND_ITS_ARITHMETIC_ANALOGUE
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PROVED_ON_CLASS
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: OBSTRUCTION_NAMED
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 1c9cf37e0e1456e6a27197e6032a1e134297ee05
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_HODGE_2026-09-08.txt
  GIT_BLOB: 594f1ed041370d8c4fe521e7d9b7de9f2089dfec
  SHA256: fd3beb9e101c491905807bbb7d71e76ea71e77375700e0f4d54dec9e240865da
  BYTES: 11840
  LINES: 62
  FINAL_LF: true
  CONNECTOR_FETCH_AT_CORRECTED_COMMIT: true
  SHA256_AND_GIT_BLOB_RECOMPUTED: true
  ALL_CHECKS_MATCH: true
  PRE_REBASE_HASH_SUBSTITUTED: false
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISIONS:
  CHOSEN_HODGE_PROOF: RIEMANN_ROCH_SERRE_DUALITY_WITH_FIXED_DEGREE_SECTION_BOUND
  COUNT_ALONE_SUFFICIENT: false
  SUBQUADRATIC_UPPER_ENVELOPE_LOAD_BEARING: true
  POLE_FORM_RANK_TWO_SIGNATURE_1_1: true
  POLE_FORM_IS_PROVED_TOTAL_Q_ORTHOGONAL_SUMMAND: false
  RADICAL_EQUALS_N_PT: ACCEPT_PINNED_PAPER_RESULT
  MULTIPLICITY_IS_WEIGHT_NOT_COORDINATE_RANK: true
  POSITIVE_REFERENCE_METRIC_SUPPLIES_HODGE_COMPATIBILITY: false
  EXACT_ARITHMETIC_HODGE_CELL: UNKNOWN
  NONEXISTENCE_OF_ARITHMETIC_HODGE_STRUCTURE_PROVED: false
  SUZUKI_REAL_ZERO_OPERATOR_USES_SHIFTED_POSITIVE_METRIC: true
  SUZUKI_ALL_WINDOW_UNSHIFTED_SIGN_PROVED: false
  FINITE_INTERVAL_IS_FINITE_DIMENSIONAL: false
  SUZUKI_SIGNED_EXTENSION_REMOVES_RH_PREMISE: false
  SOURCE_PRIMITIVE_NULL_RIGIDITY: NOT_PROVED
CLOSES: [REQ-2026-09-08-HODGE]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
SELECTED_REPRESENTATION_OF_SAME_ATOM: SOURCE_PRIMITIVE_NULL_RIGIDITY
DISCRIMINATOR: "Delta(f) = norm_H(A f)^2; not the scalar Q(f,f)"
DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: PENDING
  LEAN_KERNEL_VERIFIED: false
EXECUTION:
  HASH_AND_TEXT_VALIDATION: true
  NUMERICAL_RUN: false
  INTERVAL_CERTIFICATE_RERUN: false
  LEAN_EDIT: false
  LEAN_TOOLCHAIN_USED: false
  ARISTOTLE_SUBMISSION: false
  CODEX_EXECUTION_AUTHORIZED: false
  QUEUE_OR_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md
  PUSH_CAPABILITY: GITHUB_CONNECTOR_WRITE_AVAILABLE
  DELIVERY: DIRECT_COMMIT_WITH_IMMUTABLE_READBACK
  COMMIT_SHA_AND_CONTENT_HASH: DELIVERY_RECEIPT
  TRANSPORT_FINDING_PRESERVED: docs/routeB_bus/proshka/PROSHKA_TRANSPORT_FINDING_GOAL058_HODGE_2026-09-08.md
  TRANSPORT_FINDING_BLOB: 7c9486b251f3d0ab8bb387e0116db8058ffb2593
  OLD_ARTIFACTS_OVERWRITTEN: false
  COMMIT_IS_NOT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and first sources

**Hodge supplies neither a free positive metric nor a free nonnegative count. It supplies a compatibility theorem that turns one of those positive objects into the sign of the specified intersection form. That compatibility is the unfilled arithmetic cell.** In the algebraic proof below, its decisive content is an upper bound on sections along primitive directions, independent of the sign being proved. In the analytic version it is the existence of a pointwise primitive representative, together with the Hodge-star identity for that same pairing. [ABSTRACT][PAPER]

**Suzuki supplies genuine positive Hilbert-space structures and real-zero functions. The unrestricted-window construction does not identify their positive metric with the unshifted Weil form. The missing step is already present on a fixed arbitrary window; it is not only a passage to infinity.** [ABSTRACT][PAPER] READ S26, (1.9)–(1.11).

The request is read in full at its corrected immutable commit, and its UTF-8 bytes satisfy all four checks in the header. The earlier transport finding remains unchanged at its preserved path. This document adjudicates the mathematics, not that superseded transport issue.

### First-source keys and reading boundary

**READ [MIT2]:** Abhinav Kumar, MIT 18.727, *Algebraic Surfaces, Lecture 2*, Spring 2008, Theorem 1, §1.2 Proposition 1, Corollary 1 and Theorem 3, printed pp. 2–3. These give the surface Riemann–Roch formula and the primitive-sign route. **READ [MIT1]:** Lecture 1, §3, printed pp. 3–5, supplies the intersection/degree and restriction-sequence setting. The proof below expands the section bound explicitly; it does not treat a compressed growth argument as an axiom.

**READ [DN]:** Dinh–Nguyen, arXiv:math/0501449v2, Proposition 2.4 and §3, (3.1)–(3.2): passage from a cohomologically primitive class to a pointwise primitive representative. Our real-surface sign convention is fixed by the direct computation (H7), not by copying the paper's general sign convention.

**READ [CC20]:** Connes–Consani, arXiv:2006.13771v1, Appendix C, **Proposition C.1, (155)**, printed p. 51. It supplies the pole-null terminal criterion. The project sign is its opposite: with the two Mellin conditions imposed, the source form here is nonnegative in the desired direction.

**READ [S26]:** Suzuki, arXiv:2606.09096**v1**, Theorems 1.1, 1.3–1.5, (1.9)–(1.12), and the explicit RH assumption opening §7. The bound SCREW shelf specifies v1. An unversioned retrieval returned a later 32-page text with a different displayed target; it is not silently substituted for the 30-page v1 and its `z² ξ/ξ′` target.

**READ [S23]:** Suzuki, arXiv:2301.00421v3, (1.1)–(1.4), Theorem 1.1, printed pp. 1–2. **RELAY [ERR]:** the signed-extension correction is the project's correction reported in the bound SCREW request. Neither author acceptance nor a fresh verification of all repaired identities is claimed here.

**READ [CC22]:** Connes–Consani, arXiv:2205.01391, Theorems 1.1–1.2 and 3.4. This additional candidate prevents the false blanket claim that arithmetic Riemann–Roch, integer dimensions or Serre-type duality do not exist. Its exact object still differs from the requested surface-sign object.

**READ repository sources:** [K] KERNEL, especially (K6)–(K10), (K14)–(K26), (K34)–(K39); [KC] its independent check; [AL] ALIGN's decision/domain boundary; [LM] the named literature map; [SC] the bound SCREW request and its SIGNATURE, HYPERBOLICITY and CLOSURE addenda. All use the HODGE request commit. Their precise paths and the distinction between direct reading and relayed bibliography are in §10. Numerical material in [KC] and [LM] remains reported diagnostics, not a new interval certificate.

## 1. Q1 — dependency stripping of the algebraic proof

All derivations in this section are [ABSTRACT][PAPER]. The class is smooth geometrically integral projective surfaces over an algebraically closed field, in arbitrary characteristic. Over a finite field, apply the intersection argument after base change. The complex-analytic comparison in §1.5 is a separate characteristic-zero realization.

### 1.1 The actual inputs

Fix a smooth integral very ample hyperplane section **H**, write `h = H² > 0`, and let **K** be a canonical divisor. Write `h^i(L) = dim H^i(X,O_X(L))`. The proof uses exactly the following package, rather than the full classification of surfaces.

| Input | Exact statement used | Role |
|---|---|---|
| Symmetric degree-two intersection law | `(nD)² = n²D²`, `(nD)·K = n(D·K)`, and `L·H = deg(O_X(L)|H)` | Identifies the coefficient whose sign is sought. |
| Effective-degree positivity and restriction | A nonzero effective divisor has positive H-degree; `0 → O(L−H) → O(L) → O_H(L) → 0` is exact | Controls sections without knowing D². |
| Nonnegative dimensions | `h^i(L)` are finite nonnegative integers; `χ(L)=h^0(L)−h^1(L)+h^2(L)` | In particular `χ(L) ≤ h^0(L)+h^2(L)`. |
| Riemann–Roch | `χ(nD)=χ(O_X)+(n²D²−nD·K)/2` | Exact quadratic leading term. |
| Serre duality | `h^2(nD)=h^0(K−nD)` | Puts both positive terms under the same section bound. |
| Primitive constraint | `D·H=0` | Keeps the degrees of `nD` and `K−nD` fixed as n grows. |

The geometric inputs are READ in [MIT1], [MIT2] and the ample-intersection statement [ST]. We now derive, rather than assume, their growth consequence. No Hodge index inequality enters this derivation.

### 1.2 The section bound that makes the sign unavoidable

For a line bundle on the smooth curve H of degree `e`,
\[
 h^0_H(L)\le \max(0,e+1).
\]
For `e<0` it has no nonzero section. For `e≥0`, impose vanishing at `e+1` distinct points; each point costs at most one dimension and leaves negative degree. This proves the displayed bound directly.

For an integral divisor L on X with `d=L·H`, define
\[
 B_H(d)=
 \begin{cases}
 0,&d<0,\\
 \displaystyle\sum_{j=0}^{\lfloor d/h\rfloor}(d-jh+1),&d\ge0.
 \end{cases}
 \tag{H1}
\]
If `d<0`, effective-degree positivity gives `h^0_X(L)=0`. Otherwise restrict successively to H. At step j the restriction has degree `d−jh`; after `k=⌊d/h⌋+1` steps the remaining surface bundle has negative H-degree. Taking dimensions in the restriction sequences gives
\[
 h^0_X(L)\le B_H(L\cdot H).                         \tag{H2}
\]
This is uniform over line bundles with that fixed degree. It is not an appeal to finiteness of each separate cohomology group.

For `D·H=0`, (H2) and duality give, for every positive integer n,
\[
 h^0(nD)\le B_H(0)=1,\qquad
 h^2(nD)\le B_H(K\cdot H),\qquad
 h^0(nD)+h^2(nD)\le C_H:=1+B_H(K\cdot H).             \tag{H3}
\]
Riemann–Roch and `h^1≥0` now imply
\[
 \frac{n^2}{2}D^2-\frac n2D\cdot K+\chi(O_X)
 \le C_H,
\]
so
\[
 D^2\le\frac{D\cdot K}{n}
          +\frac{2(C_H-\chi(O_X))}{n^2}
 \longrightarrow0.
 \qquad\boxed{D^2\le0.}                             \tag{H4}
\]
The decisive envelope has the correct direction. A lower bound for `h^0` would not replace the upper bound (H3).

A still smaller logical interface suffices: replace the constant bound (H3) by
`h^0(nD)+h^2(nD)=o_D(n²)`. No uniformity over all D is required. With `q(D):=−D²`, the count actually carrying the sign can be written
\[
 h^1(nD)=\frac{n^2}{2}q(D)+\frac n2D\cdot K
                 +h^0(nD)+h^2(nD)-\chi(O_X),
 \qquad \frac{2h^1(nD)}{n^2}\longrightarrow q(D).     \tag{H5}
\]
Thus **nonnegative count + exact quadratic coefficient + independent subquadratic error** forces `q(D)≥0`. The nontrivial geometric content is what prevents the other cohomology dimensions from hiding a quadratic contribution. Calling that content merely `h^0≥0` deletes the controlling inequality.

### 1.3 Equality case and the fibre complement

Extend (H4) first to rational divisor classes by clearing denominators, then to real numerical classes by continuity. If `D·H=0` and `D²=0`, for every `E·H=0` and real t,
`(D+tE)²=2t(D·E)+t²E²≤0`. Both signs of t force `D·E=0`. Since also `D·H=0`, D pairs to zero with every divisor class. Therefore D is numerically trivial. The induced form on the primitive numerical quotient is negative definite. This equality-case argument is READ in [MIT2, §1.2 Corollary 1] and is reproduced here to identify the exact role of the radical.

On `C×C`, the two fibre classes satisfy `F₁²=F₂²=0`, `F₁·F₂=1`; `H=F₁+F₂` is ample. For any divisor D, its fibre-orthogonal component is
\[
 D_0=D-(D\cdot F_2)F_1-(D\cdot F_1)F_2,
 \quad D_0^2=D^2-2(D\cdot F_1)(D\cdot F_2)\le0.
\]
This is the sign calculation needed by the curve argument. Neither a Frobenius eigenvalue computation nor the full surface-signature theorem is needed to obtain this primitive inequality.

### 1.4 Exact falsifier of the count-only inference

On the lattice `Z²`, take intersection matrix `B=2I₂`, canonical vector `K=0`, and `χ₀=1`. For `x=(a,b)`, set
\[
 h^0(x)=h^1(x)=h^2(x)=1+a^2+b^2.
 \tag{H6}
\]
These are nonnegative integer dimensions, `h^2(x)=h^0(K−x)`, and
`h^0−h^1+h^2=χ₀+B(x,x)/2`. Take `H=(1,0)` and `D=(0,1)`: `H²=2`, `H·D=0`, but **D²=2>0**. All three named count/RR/duality identities hold; the section envelope fails because `h^0(nD)=1+n²`.

This is an exact countermodel to that abstract implication, not an alleged algebraic surface. It deliberately does not satisfy effective-degree positivity and restriction. The weakest repair is to restore their required consequence `h^0+h^2=o(n²)`. The algebraic proof is therefore count-based, but not count-only. No claim of a unique minimal axiomatization of all Hodge proofs is made.

### 1.5 The analytic version has a different last input

**READ [DN, Proposition 2.4; (3.1)]:** a primitive class admits a cohomologous representative α that is pointwise primitive. On a Kähler surface this means `α∧ω=0`. Stokes' theorem preserves its intersection pairing under the representative change.

Fix the usual complex orientation. At a point, a real primitive `(1,1)` form is unitarily diagonalizable as
`α=r(e¹∧Je¹−e²∧Je²)`, while `ω=e¹∧Je¹+e²∧Je²`. Direct wedge multiplication gives
\[
 *\alpha=-\alpha,\qquad
 -\int_X\alpha\wedge\alpha
   =\int_X\alpha\wedge *\alpha
   =\|\alpha\|_{L^2}^2\ge0.                         \tag{H7}
\]
Equality forces α to vanish. For complex classes use the corresponding Hermitian polarization. This version does not need a section count. It needs a **positive metric compatible with the very same intersection pairing**, on representatives of all primitive classes. The existence of some unrelated positive metric is not the Hodge–Riemann input.

## 2. Q2 — transplant table, with object corrections

### 2.1 The retained source and the precise meaning of the pole plane

[ABSTRACT][PAPER] READ K, (K6)–(K10). Retain exactly the request's antilinear-first form, translations, prime-power weights and both moments. On
`ℋ=ker M₊∩ker M₋ ⊂ ℰ`,
\[
 Q(f,g)=\mathcal D(f,g)-c_A\langle f,g\rangle
 -\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}
       \{\langle f,U_{\log m}g\rangle+\langle f,U_{-\log m}g\rangle\},
 \quad \langle g,Af\rangle_{\mathscr H}=Q(g,f).       \tag{H8}
\]
The reference norm is `‖f‖²_ℋ=𝒲[f]+𝒟[f]`, not `Q[f]`; `‖A‖≤65/3`, and `ker A=𝒩_pt` is the pinned paper result.

The **pole term** P really has rank two and signature `(1,1)`:
`P=2|M_c|²−2|M_s|²`. Independence of `M₊,M₋` follows already from the two translated bump functions used in KERNEL's moment correction. Thus P induces a hyperbolic form on `ℰ/ℋ`.

However, **P is a summand of Q, not a proved Q-orthogonal direct summand of ℰ**. The remaining source terms may couple any chosen lift of the two moment coordinates to ℋ. Restriction to ℋ removes P exactly; it does not prove an ambient Witt decomposition of Q. The fibre analogy preserves two moment constraints and the rank-two pole pairing, but does not import the surface's total index one.

### 2.2 Table

Every row is [ABSTRACT][PAPER] for its stated identification or obstruction; every missing arithmetic supplier is [ABSTRACT][CONDITIONAL]. **UNKNOWN** means no supplier was established in this audit. **ABSENT** is reserved for the precisely refuted implication, not for all possible future constructions.

| Hodge ingredient | RH-side analogue on the pinned objects | Status | Exact missing lemma or obstruction |
|---|---|---|---|
| Fibre hyperbolic plane | `P=2 Re(M₊ overline(M₋))`, kernel ℋ | **EXISTS**, READ request §0 and K (K6) | None for this rank-two form. An ambient Q-orthogonal fibre-plane identification is **UNKNOWN**, and unnecessary for the pole-null consumer. |
| Numerically trivial classes | `𝒩_pt=rad(Q|ℋ)=ker A` | **EXISTS**, READ K (K19)–(K23), KC | None for the radical. It does not decide whether other isotropic vectors exist. |
| Primitive complement, then quotient | `ℋ/𝒩_pt` with induced Q | **EXISTS** as a nondegenerate signed quotient, READ K (K23), (K34) | Its positive sign is not part of nondegeneracy. No unproved Hilbert completion in the Q-norm is allowed. |
| Ample reference: `H²>0` and positivity against effective divisors | Positive metric `𝒲+𝒟`; positive energy `𝒟`; two pole functionals | The metric and energy **EXIST**, READ K (K7). The **ample/effectivity analogue is UNKNOWN** | A source-defined admissible-positive class and restriction/degree law yielding a subquadratic bound. Neither moment vanishing nor `𝒟≥0` gives that law. |
| Restriction to a hyperplane and fixed-degree section bound | No section functor or restriction sequence for these test functions has been supplied | **UNKNOWN** | An actual nonnegative count with a bound analogous to (H3), or another proved mechanism paying the same signed comparison. Ordinary boundedness `|Q|≤(65/3)‖·‖²` is not subquadratic growth under `f→nf`. |
| Riemann–Roch quadratic identity | Signed explicit formula (K16) | **EXISTS as a signed trace identity**, READ K; **UNKNOWN as cohomological RR** | A source-defined count `b_n(f)≥0` with `b_n(f)=n²Q[f]/2+r_n(f)` and an independently proved `r_n(f)=o_f(n²)`. No such count is defined by (K16). |
| Serre duality | Functional equation and `jλ=−conj(λ)` | The involution **EXISTS**, READ request/K; full duality/count interface **UNKNOWN** | Identify nonnegative-degree objects on which j gives a duality analogous to `h²(nD)=h⁰(K−nD)`. An involution alone leaves hyperbolic blocks. |
| Nonnegative dimensions | `m_λ>0`; also the independently positive metric and `‖Af‖²` | These positive quantities **EXIST**; their identification with the primitive sign is **UNKNOWN** | A positive weight is not a positive pairing: an off-line pair contributes `2m Re(conj(u)v)`. KERNEL's positive square still has an unpaid signed remainder. |
| Hodge–Riemann compatibility | A proposed source map T with `Q(f,g)=⟨Tf,Tg⟩`, or a sufficient one-sided comparison | **UNKNOWN** | Prove the equality/comparison on a dense pole-null core, including every prime term, with T defined without assuming Q is positive. Correct kernel alone is insufficient. |
| Primitive Hodge equality cell | `Q[f]=0 ⇒ f∈𝒩_pt`, equivalently `Q[f]=0 ⇒ Af=0` | **UNKNOWN**; exact selected gap | Source primitive null rigidity, stated finally in §10.4. Together with the existing positive anchor it forces the sign; §4 proves the implication. |
| Passage from tested classes to all classes | KERNEL core density and continuity in `𝒲+𝒟` | **EXISTS**, READ K §2.2 and (K9) | Positivity on every actual source window would pass to ℋ. Positivity on a different shifted form would not. |

The proposed count row is a **testable contract**, not a construction: naming `b_n=n²Q/2`, clipping its negative values, or defining it using a positive square root of Q would not supply an independent count or error bound.

**READ [CC22, Theorems 1.1–1.2]:** genuine integer-valued arithmetic dimensions and a Serre-type duality exist for Arakelov divisors on the compactification of Spec Z. Their Riemann–Roch term is rounded degree, not a surface-intersection quadratic coefficient for arbitrary f in ℋ. By its displayed degree formula, its index on nD has at most linear growth. There is no supplied map identifying its quadratic leading coefficient with (H8). This candidate is not declared impossible to extend; its present theorem does not fill this cell.

### 2.3 Correct the multiplicity and signature ledger

[ABSTRACT][PAPER] Derivation from READ K (K16), (K21)–(K23a). Normalize the separating test at a distinct zero λ to obtain `e_λ` with transform one at λ and zero at every other distinct zero. A j-fixed zero contributes the one-dimensional matrix `(m_λ)`. A two-element j-orbit contributes
\[
 m_\lambda\begin{pmatrix}0&1\\1&0\end{pmatrix},
 \qquad \operatorname{sig}=(1,1).                    \tag{H9}
\]
**Multiplicity scales the matrix; it does not multiply its rank.** A zero of order r still supplies one point-evaluation coordinate in the quotient by `𝒩_pt`. Jets would describe a different quotient. A generic conjugation/reflection quartet consists of two such j-orbits, hence gives two positive and two negative directions.

For any finite j-stable set of distinct zeros, the separator span realizes exactly these blocks. For the full form, define an index as the supremum of finite-dimensional definite subspaces, not as a claimed Hamel-basis decomposition. The result is
\[
 \operatorname{ind}_{-}(\bar Q)
   =\#\{\text{distinct two-element j-orbits}\},\qquad
 \operatorname{ind}_{+}(\bar Q)=\infty.               \tag{H10}
\]
Here the count may be infinite. For a finite number k of off-line orbits, the upper bound follows on compact smooth tests by setting their k negative block coordinates to zero in the signed explicit formula. Any negative subspace of dimension greater than k would then contain a nonzero nonnegative vector. Continuity and compact-core approximation transfer this bound to ℋ. If there are infinitely many orbits, finite separator spans give arbitrarily many negative directions.

Positive index infinity also has a **source-side proof**: the KERNEL (K14) lower bound holds on the infinite-dimensional space `(∂²−1/4)C_c^∞(I)` for one interval of length `2^−24`. Every vector in that space is pole-null, and Q exceeds its physical norm squared. This avoids assuming a basis or a positive zero-sum formula on the whole completion.

Thus the observer's block description is correct after deleting **“with multiplicity” from the dimension count**. Also, (K16) is used on its proved compact/special-test domain and by continuity; absolute convergence of a two-variable zero series for every pair in ℋ is not silently added.

## 3. Q3 — which part Suzuki supplies

All source statements below are READ at the stated locators. The comparisons and countermodels are [ABSTRACT][PAPER]. No conclusion is imported from Suzuki §7 under RH.

### 3.1 The exact positive object is shifted

**READ [S26, (1.9)–(1.11), Theorem 1.5]:** choose a real shift τ below the lowest eigenvalue of A_a and form
\[
 T_a=A_a-\tau I>0,\qquad
 \|f\|_{T_a}^2=Q_W^a[f]-\tau\|f\|_2^2.              \tag{H11}
\]
The derivative operator in the resulting Hilbert space has self-adjoint extensions whose characteristic functions W have real zeros. This is a genuine realization of **positive reference geometry plus a real-zero operator**. Its deficiency indices `(1,1)` are not the inertia of Q and not the pole plane.

On compact tests, Suzuki's Fourier variable satisfies `λ=−iγ`, hence `F_f(λ)=f-hat(−γ)`. Reversing the sesquilinear slots converts his linear-first convention to ours: `Q_W(f,g)=Q(g,f)`, and the diagonal values agree. We require only this common-core comparison here, not an isometry of the different completed spaces. Restricting to the same two moment kernels removes our pole term.

In those coordinates the **unshifted** source energy is still
\[
 Q[f]=\|f\|_{T_a}^2+\tau\|f\|_2^2.                 \tag{H12}
\]
When τ is negative, (H12) is not a sum of nonnegative terms. To fill the Hodge cell one must prove the missing comparison
`‖f‖²_Ta ≥ −τ‖f‖²_2` on the actual pole-null class, or an equivalent unshifted rigidity statement. Self-adjointness of the derivative does not supply this comparison.

The exact adversarial control is
\[
 A_a=\operatorname{diag}(-1,1),\quad \tau=-2,
 \quad T_a=\operatorname{diag}(1,3)>0,
 \quad Q[e_1]=-1.                                    \tag{H13}
\]
It refutes the abstract inference from a positive shifted metric to a positive original form. It is not an actual negative zeta window.

There is a stronger control for the **whole canonical construction**, not merely this matrix. Starting with any admissible source realization, replace
\[
 Q_c[f]=Q[f]-c\|f\|_2^2,\quad A_{a,c}=A_a-cI,
 \quad \tau_c=\tau-c.
 \qquad A_{a,c}-\tau_c I=T_a.                         \tag{H13a}
\]
The lowest eigenvalue and shift move by the same amount. The positive metric, derivative operator, deficiency spaces and W can remain exactly unchanged. For any fixed nonzero core test f, choosing `c>Q[f]/‖f‖²` makes `Q_c[f]<0`. Thus that real-zero construction, taken alone, cannot distinguish opposite source signs. The perturbation changes the arithmetic source; it is a falsifier of a structure-only inference, not an allowed replacement of zeta's Q. A valid arithmetic argument must use information that fixes and controls this unshifted source, not just the unchanged T_a geometry.

### 3.2 What is and is not a finite-window Hodge theorem

**READ [S26, Theorems 1.1, 1.3, 1.4]:** the operator realization, continuity of the bottom eigenvalue and positivity for **sufficiently small a** are actual results. “The expansion is derived below the first prime” is not the assertion that Theorem 1.4 proves positivity throughout that whole interval.

A finite interval remains an **infinite-dimensional** function space. Theorem 1.5 is therefore not a Hodge–Riemann theorem on a finite-dimensional primitive numerical space. It is also not the all-a sign of Q_W^a. For the genuinely certified small-window class, the sign is available; for general a, the shift-removal comparison remains unproved in the cited construction.

[COFINAL_FAMILY][PAPER] If the original Q were nonnegative on every compact pole-null window, KERNEL's density and continuity would already transfer that sign to ℋ. Conversely, a strictly negative value in ℋ would persist in some compact exactly pole-null approximation. **There is no additional sign defect that can exist only at infinite support while all actual source windows are nonnegative.** The separate real-zero-approximant route needs a source-identifying limit, not a theorem that positivity is born at infinity.

### 3.3 The de Branges and signed-extension boundary

**READ [S23, (1.3), Theorem 1.1]:** the specified Hilbert completion and its de Branges norm identification are constructed under RH. A **de Branges space** is a Hilbert space of entire functions with a compatible evaluation/analytic structure; naming it does not establish that an indefinite Weil pairing is its norm.

**RELAY [ERR]:** adopting the project's signed extension fixes the indicated parity/transform defect. It does not prove the Hermite–Biehler condition or remove the RH premise from the norm identity. Accordingly the repaired identity is a conditional model of the desired compatibility, not its unconditional supplier. Our quotient remains defined in the independent `𝒲+𝒟` topology; identifying its completion with H_W is a separate claim.

**READ [S26, Corollary 1.6 and opening of §7]:** the proposed identification limit is a conditional route; its heuristic discussion assumes RH. The v1 target is meromorphic. Any use of an entire-function Hurwitz argument must specify holomorphic zero-free normalizers and a pole-free domain, or a precise meromorphic convergence formulation. Arbitrary pointwise finite gauges cannot simply be treated as holomorphic gauges. We do not adjudicate the whole parallel SCREW limit problem again here.

**Answer to Q3:** the machinery realizes the positive-reference/spectral part. On sufficiently small source windows it also supplies an actual sign. It does **not** fill the primitive Hodge compatibility cell for all windows, and it does not make infinity the sole missing axiom.

### 3.4 Where the primes must enter

[ABSTRACT][PAPER] In this task the arithmetic already enters explicitly in (H8), through every von Mangoldt coefficient and its translation, and in Suzuki through the screw kernel defining A_a. The missing proof must use those coefficients to establish the **unshifted** comparison or the exact leading coefficient and error bound of a positive count. Their presence in a definition alone is not a proof of their sign effect.

The request's Davenport–Heilbronn warning is used as an adversarial requirement: a proof using only generic functional-equation and growth symmetries has not isolated this arithmetic. It is not a theorem that every conceivable zeta-specific proof must literally cite an Euler product. An equivalent source identity can encode the same information. No sign proof from the generic involution j is admitted here.

## 4. Final proposal — primitive null rigidity, not another positive metric

[ABSTRACT][PAPER] The selected representation is already suggested by the bound HYPERBOLICITY addendum; no priority claim or new mandatory supplier is made. It is useful because the radical has been identified, so the remaining obstruction is precisely the existence of **isotropic but nonradical** vectors. Isotropic means `Q[f]=0`; radical means `Q(g,f)=0` for every g.

The reduction from this equality case to the whole sign has an elementary source proof. KERNEL (K14) supplies a fixed u with `Q[u]>0`. Suppose v has `Q[v]<0`. Put
\[
 w=v-u\,\frac{Q(u,v)}{Q[u]},\qquad
 Q(u,w)=0,\qquad Q[w]=Q[v]-\frac{|Q(u,v)|^2}{Q[u]}<0.
\]
Then
\[
 f=u+\sqrt{\frac{Q[u]}{-Q[w]}}\,w
 \quad\Longrightarrow\quad
 Q[f]=0,\qquad Q(u,f)=Q[u]>0.                        \tag{H14}
\]
Thus null rigidity excludes every negative v at once. Conversely, a nonnegative Hermitian form has null rigidity by applying its nonnegativity to `f+tg`, for real and imaginary t. No spectral gap, closed range or uniform positive lower bound is required.

The **discriminator** is
\[
 \Delta(f)=\|Af\|_{\mathscr H}^2
   =\sup_{\|g\|_{\mathscr H}=1}|Q(g,f)|^2.            \tag{H15}
\]
It vanishes exactly on `𝒩_pt`. In the conditional off-line block (H9), `Q[e_λ]=0` but
`Q(e_{jλ},e_λ)=m_λ`, so
`Δ(e_λ)≥m_λ²/‖e_{jλ}‖²_ℋ>0`. This is a discriminator, not a claim that an off-line zero exists. The source definition of A uses no zero list; the separators test its semantics.

A proposed count mechanism or coordinate construction must therefore kill (H14), not merely vanish on the already known null family. The still-open assertion is stated once more, with its full domain, at the end of the document.

### Route map and the required two re-representations

The following cost scores are ordinal planning estimates, not mathematical evidence. All unproved suppliers have [ABSTRACT][CONDITIONAL] status.

| Representation | Decisive object | Kill-power / cost | Main risk and current status |
|---|---|---|---|
| **Selected: source equality-case rigidity** | `Q[f]=0 ⇒ Δ(f)=0`, with A defined by (H8) | 10/10 / 7/10 | Exact and consumer-sufficient by (H14); no source proof yet. It preserves the signed form and avoids demanding a gap. |
| **Count representation** | Source-defined `b_n(f)≥0`, `2b_n(f)/n²→Q[f]`, with independent error control | 10/10 / 9/10 | A count of the right object is not supplied. Wrong degree or a quadratic remainder defeats the proposal before computation. |
| **Compatible positive coordinates** | A source construction with a proved unshifted pairing identity on a dense pole-null core | 10/10 / 9/10 | Correct kernel or positive shifted geometry is insufficient. Suzuki supplies part of this structure but not that identity. |

The original signed-head/complement route is not abandoned or refuted. These are interfaces for the same open atom. No escalated computation is authorized.

## 5. Strongest attacks and exact scope of refutation

[ABSTRACT][PAPER] The strongest objection to the selected route is valid: **the passage from null rigidity to the sign is easy; proving null rigidity for the source is the unpaid arithmetic.** We have not made that proof easier merely by naming it. What became more precise is the compatibility that a proposed Hodge substitute must provide, and the exact tests rejecting insufficient substitutes.

| Rejected inference | Exact evidence | KILL_SCOPE | FAILURE_TYPE / EPISTEMIC_STATUS |
|---|---|---|---|
| Nonnegative counts, RR and duality alone force primitive sign | Integer countermodel (H6), with `D²=2` | THEOREM_SHAPE | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for this abstract implication |
| A positive shifted metric or its real-zero construction forces the unshifted source sign | (H11)–(H13a), strict source value `−1` and an unchanged canonical construction | THEOREM_SHAPE | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for this abstract implication |
| Pointwise-zero multiplicity creates that many independent quotient coordinates | Exact block (H9), rank two for every positive multiplicity | THEOREM_SHAPE | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for multiplicity-as-rank accounting |

These controls are pinned by this verdict's immutable committed bytes; (H11) is additionally pinned by S26v1 (1.9). None is a negative value for the actual zeta source. **No ROUTE_FAMILY kill is made.** Unknown arithmetic counts, unshifted norm identities and Hodge structures remain research debt, not impossibility results.

The claim that P is a Q-orthogonal hyperbolic summand is **unsupported**, not proved false for this exact Q. It needs a splitting theorem only if a later argument actually consumes one. The current consumer does not.

## 6. Consumer-first dependency epistemics

Logical implications: [ABSTRACT][PAPER]. Missing suppliers: [ABSTRACT][CONDITIONAL].

| K8A field | Finding |
|---|---|
| DOWNSTREAM_CONSUMER | CC20 Appendix C, Proposition C.1 (155), applied to the same complex compact smooth pole-null tests; KERNEL extends the source by continuity. |
| ACTUAL_CONSUMER_REQUIREMENT | Nonnegativity of the full Q on that class. Neither a uniform positive floor nor a preferred positive-coordinate basis is required. |
| ORIGINAL_REQUESTED_OBJECT | A transplanted Hodge proof through the pole data, radical and arithmetic primitive quotient, possibly supplied by canonical systems. |
| ORIGINAL_OBJECT_IS | **NOT_NECESSARY** for a literal surface/RR construction or a full compatible basis. Such structures are possible sufficient suppliers, not mandatory interfaces. Their existence for this source remains UNKNOWN. |
| KNOWN_WEAKER_INTERFACES | Null rigidity plus the existing positive anchor gives Q≥0 by (H14). A nonnegative asymptotic count with an independently vanishing error gives Q≥0 by the same lower-envelope logic as (H5). A dense-core unshifted lower certificate also suffices. |
| FAILURE_TYPE | NO_DERIVATION for the arithmetic compatibility; COUNTEREXAMPLE only for the three exact abstract implications in §5. |
| EPISTEMIC_STATUS | **RESEARCH_DEBT** for the source sign and its candidate suppliers. Mathematical death applies only to the exact refuted theorem shapes. |
| NOVELTY_AXIS | Explicit separation of nonnegative count from its subquadratic error bound, followed by a source-faithful equality-case contract. No claim to invent Hodge theory, Riesz representation or null rigidity. |
| REOPEN_TRIGGER | A source-defined count with the correct quadratic coefficient and proved subquadratic error; or a same-form unshifted comparison; or a source proof that every isotropic vector is radical. It must survive (H6), (H13), and the conditional separator control without assuming the conclusion. |

No basis-independent lower norm equivalence is demanded on `ℋ/𝒩`. Positive definiteness on an infinite-dimensional quotient need not imply coercivity in the inherited reference norm. This avoids reopening ALIGN's rejected uniform-floor target.

## 7. Frozen predictions, new registrations and closeout

### 7.1 Observer predictions — original events retained

```text
P_HODGE_MINIMAL_IS_COUNT: 0.65 — Q1: the minimal sign-producing ingredient in the chosen proof is a tautologically nonnegative count/dimension via Riemann–Roch + duality.
P_TABLE_CELL_EMPTY: 0.80 — Q2: the Hodge-index cell has status ABSENT or UNKNOWN; no existing arithmetic object fills it.
P_RR_ANALOGUE_IS_EXPLICIT_FORMULA_WITHOUT_COUNT: 0.75 — Q2: the Riemann–Roch row is filled by the explicit formula (K16) with the explicit remark that it lacks the nonnegative count.
P_SUZUKI_REALISES_ONLY_WINDOW: 0.70 — Q3: the canonical-system machinery realises the analogue on finite windows only; the a → ∞ passage is the absent axiom.
P_DEPENDENCY_STRIPPING_NAMES_ONE_LEMMA: 0.60 — the verdict ends with ONE exact missing lemma stated in the language of §0 objects.
```

| Prediction | Fate | Reason; no event substitution |
|---|---|---|
| P_HODGE_MINIMAL_IS_COUNT | **PARTIAL** | The selected proof is count-based. The count-only/minimality reading is refuted by (H6); the operative count can be h¹, and the independent subquadratic upper envelope is indispensable. |
| P_TABLE_CELL_EMPTY | **CONFIRMED_ON_THE_EXAMINED_SOURCE_SET** | The exact cell is UNKNOWN. This is not a proof that no arithmetic analogue exists anywhere; CC22 is a genuine but differently typed arithmetic count. |
| P_RR_ANALOGUE_IS_EXPLICIT_FORMULA_WITHOUT_COUNT | **PARTIAL** | The signed identity and the lack of the required count are confirmed. The explicit formula does not fill a literal RR/cohomology row merely by being an identity. |
| P_SUZUKI_REALISES_ONLY_WINDOW | **REFUTED_AS_STATED** | At arbitrary fixed a, Theorem 1.5 supplies real zeros for an operator built in the shifted metric, not the primitive sign of the original form. Infinity is not the sole missing step. |
| P_DEPENDENCY_STRIPPING_NAMES_ONE_LEMMA | **CONFIRMED_AS_A_NAMED_REMAINDER** | §10.4 gives one exact source-null-rigidity statement. It is not claimed proved. |

Partial events are not retroactively converted into binary successes or assigned a misleading aggregate score.

### 7.2 Registrations made in this session before the proof checks

`P_A_COUNT_NEEDS_GROWTH`, **0.80**, predicted a separate growth bound beyond nonnegative dimensions: **CONFIRMED** by (H1)–(H6).

`P_A_CANONICAL_NOT_SOURCE_SIGN`, **0.90**, predicted that canonical-system real zeros do not certify the original window form: **CONFIRMED** by the direct reading of (1.9), (H13), and the stronger invariant control (H13a).

**New prospective registration:** `P_HODGE_STRIP_SURVIVES_INDEPENDENT_AUDIT`, **0.90**: an independent checker will accept the fixed-degree bound (H2), the block-rank correction (H9), and the source positive-anchor reduction (H14) without adding a new positivity assumption. **UNTESTED** here. Failure of any one makes this combined event false; do not repair its definition after the audit.

### 7.3 Closeout

**Progress class:** REPRESENTATION_PROGRESS. **Selected cognitive operator:** MINIMAL_LEMMA. **Route score:** 4/5 as a falsifier/contract audit, not as distance to RH.

What became smaller: the vague missing “Hodge structure” became a same-form compatibility requirement with two explicit implementations, and a single equality-case target on the already defined source.

What was refuted: count-only forcing, shifted-metric forcing, and multiplicity-as-rank. What must not recur: importing ambient index one from the pole term; relabeling the reference norm as Q; treating all windows as positive; discarding the source's prime couplings; or treating finite diagnostics as a cofinal theorem.

Smallest named gap: source primitive null rigidity, another representation of `ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND`. Its source proof is still missing. The positive metric, radical, continuity and final logical implication are not missing.

The cheapest decisive checks in this batch were (H6) and (H13), both exact paper controls. Before any new count or coordinate proposal is implemented, check its quadratic coefficient and unshifted pairing against those controls. No expensive numerical discrimination is needed to reject these already invalid inferences.

**Memory entry for the verdict ledger:** a positive object produces the desired sign only through a proved compatibility with the unchanged signed source; on the RR route, this includes a genuinely subquadratic error bound. This is a repository record, not a change to personal memory.

## 8. One verification handoff; no execution mandate

**Next local task:** `HODGE_PRIMITIVE_SIGN_DEPENDENCY_AUDIT`. This is a proposed independent paper audit of this verdict, not an authorization to edit Lean, run numerics or launch a new research batch.

Inputs: the byte-locked HODGE request, [K] and the directly read locators in §0. Check (H2) without Hodge positivity, the `h⁰+h²=o(n²)` envelope, the antilinear-first calculation (H14), and the exact shifted identity (H11). Confirm that every UNKNOWN table cell is an unproved supplier, not a claimed absence theorem. Check the distinct-zero negative-index argument on compact tests before using density.

Success: all three registered mathematical controls survive, the table preserves the same Q and domain, and no analytic RH supplier is marked closed. Failure report: `HODGE_SOURCE_COMPATIBILITY_OR_DEPENDENCY_GAP`, naming the first equation, missing hypothesis and weakest repair. Do not substitute an easier form or a different quotient.

**Publication gate.** Branch: `rh_clean`. The only path written is `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md`. The commit subject begins `[Proshka]`. The commit SHA and recomputed content hash are supplied in the delivery receipt and verified against an immutable connector readback. A file cannot contain the hash of its own enclosing commit without changing that commit; this receipt is not a second verdict.

Before publication the destination was absent, and the preserved transport file read back with blob `7c9486b251f3d0ab8bb387e0116db8058ffb2593`. No replacement of that file is authorized.

**Working directory: repository root; text-integrity checks only:**
```bash
git log -1 --format='%H %s' -- docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md
git hash-object docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md
shasum -a 256 docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md
```
These commands contain the literal path; no variable substitution is required. No Lean files, Lean blob hashes or axiom profiles are produced. No `lake` or Mathlib validation was available or run in this adjudication. A successful text gate changes only delivery status; a successful paper audit validates the new derivations, **not** the missing source-null-rigidity theorem.

## 9. Proshka's own line

I choose the algebraic proof because it exposes the growth term that a transplanted argument must actually control.
The Kähler proof is shorter after its representative theorem, but that theorem can hide the entire compatibility burden.
The canonical-system alternative is concrete, yet its shift separates its positive metric from the source sign.
Those are reasons to keep both as comparisons rather than to confuse their conclusions.
The owner's form–radical–quotient framing removes several irrelevant construction problems.
We already have a radical and a usable positive reference space.
We do not need to build them again under different names.
What remains is whether a zero value can belong to a vector outside that radical.
That formulation detects an entire hyperbolic block instead of following individual zeros.
It also prevents a new positive norm from being mistaken for a source lower bound.
One move beyond this batch is a genuinely arithmetic count with a quadratic leading term equal to the source form.
The first question is its definition, not how accurately it can be evaluated.
A quadratic remainder or the wrong degree would defeat that implementation immediately.
The other move is a source-defined change of representatives that preserves Q and makes its sign local.
The Kähler calculation explains exactly why preservation is essential.
An unpaid mixed term or spectral shift would defeat that implementation.
I would ask for one proposed count or one representative map, with its complete formula and admissible domain.
I would not ask for another table of very small eigenvalues.
The required evidence must distinguish a zero energy from a vector annihilated by every pairing.
The useful surprise is that the analogy points to an equality case, not necessarily to a stronger positive floor.
That fits the already present nontrivial radical instead of fighting it.
I distrust the suggestion that two moment constraints alone import an ambient index theorem.
I also distrust treating “only infinity remains” as a property of any family of real-zero functions.
The next useful contribution must preserve the source pairing and explain why its arithmetic cannot leave an isotropic nonradical vector.

## 10. Research log

### 10.1 Repository sources consulted

Unless stated otherwise, these reads are pinned to `1c9cf37e0e1456e6a27197e6032a1e134297ee05` in `Malaeu/chen_q3`.

| Key / reading | Locator | What was taken |
|---|---|---|
| Protocol — READ | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, current `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4` | Source lock, single verdict, scope and verification rules. |
| Request — READ IN FULL, REHASHED | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_HODGE_2026-09-08.txt`, blob `594f1ed041370d8c4fe521e7d9b7de9f2089dfec` | Authoritative task and all five frozen predictions. |
| K — READ, relevant sections | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md`, blob `d171a2fb7b6b917a1780656952b1db5458cc9a34`; (K6)–(K26), (K34)–(K39) | Exact completion, signed source, positive anchor, separators, radical and prohibited inference from a positive square. |
| KC — READ | `docs/routeB_bus/KERNEL_INDEPENDENT_CHECK_2026-09-08.md` | Independent paper checks and correct C.1 locator; numerical decimals not promoted. |
| AL — READ, decision/domain boundary | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ALIGN_2026-09-08.md`, blob `7c6841aa0d8a575a5fcee9fe03d5ae37e316c997` | No uniform positive physical floor, exact signed-source and coverage boundaries. |
| SC — READ, task and relevant shelf | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SCREW_2026-09-08.txt` | Parallel-task boundary, v1 reading, and RELAY of the signed-extension erratum. |
| SC-SIGNATURE — READ IN FULL | `docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_SCREW_SIGNATURE_2026-09-08.md`, blob `f66090b80efb877c1191a81631cf7af69ad269f5` | Proposed dictionary, specifically submitted for multiplicity correction. |
| SC-HYPERBOLICITY — READ IN FULL | `docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_SCREW_HYPERBOLICITY_2026-09-08.md`, blob `da5429a0b2c0e8d093d67fa74b34d52bd92e35c5` | Existing null-rigidity proposal and corrected finite-window warning. |
| SC-CLOSURE — READ IN FULL | `docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_SCREW_CLOSURE_2026-09-08.md`, blob `d92bbfce5c9036e69e48a1c6545de344c6f43f14` | Keep real-zero preservation separate from identification; do not duplicate the parallel batch. |
| LM — READ, relevant map sections | `docs/routeB_bus/litreview/SOS_WEIL_POSITIVITY_LITERATURE_MAP_2026-09-07.md` | Acquisition pointers and forbidden global extrapolations. Its reports about other papers remain RELAY unless independently listed below. |
| Preserved transport — READ, header only | `docs/routeB_bus/proshka/PROSHKA_TRANSPORT_FINDING_GOAL058_HODGE_2026-09-08.md`, current branch, blob `7c9486b251f3d0ab8bb387e0116db8058ffb2593` | Confirmed preservation; no mathematical input. |
| Delivery metadata — READ | GitHub branch endpoint, observed head `7a03e1260d954c0d63fb7104f209f0511ef77b84`; verdict destination returned 404 | Publication preflight only. Later branch activity is not substituted for request-pinned evidence. |

`docs/CHAT_DIGESTS.md`, personal archives, the queue and unrelated uploaded conversations were not opened. The request already contains the owner's frame. COMPENSATE, INVARIANT, U1 and CHAIN are parent references carried by the request/KERNEL/ALIGN, not independently reaudited sources here. Their earlier proofs are not silently reused as newly checked arithmetic suppliers.

### 10.2 External sources and acquisition outcomes

| Reading | Locator | Taken or rejected |
|---|---|---|
| READ MIT1 | MIT OCW 18.727, Spring 2008, `lect1.pdf`, §3, printed pp. 3–5; `https://ocw.mit.edu/courses/18-727-topics-in-algebraic-geometry-algebraic-surfaces-spring-2008/` | Surface intersection and degree/restriction framework; relevant PDF page visually checked. |
| READ MIT2 | Same course, `lect2.pdf`, Theorem 1; §1.2 Proposition 1, Corollary 1, Theorem 3, printed pp. 2–3 | Chosen proof route; both sign pages visually checked. No unrelated claims in the notes are imported. |
| READ ST | Stacks Project, `https://stacks.math.columbia.edu/tag/0BEV`; also curve RR section `0B5B` | Ample intersection positivity; curve RR inspected but the elementary curve section bound in §1.2 was derived directly. |
| READ DN | `https://arxiv.org/pdf/math/0501449`, returned v2; Proposition 2.4, §3 (3.1)–(3.2) | Pointwise primitive representative method. General printed sign convention is not used to set our surface orientation. |
| READ CC20 | `https://arxiv.org/pdf/2006.13771v1`, Appendix C, Proposition C.1 (155), printed p. 51 | Exact pole-null criterion; theorem page visually checked. |
| READ S26v1 | `https://arxiv.org/pdf/2606.09096v1`, Theorems 1.1, 1.3–1.5; (1.9)–(1.12); §7 opening | Shifted metric and the true real-zero operator. Printed pp. 5–6 visually checked. |
| READ, VERSION EXCLUDED S26 unversioned | `https://arxiv.org/pdf/2606.09096`, introductory results and target formula | Later text differs from v1; not substituted for the bound target. No claim that a version change itself is a mathematical defect. |
| READ S23 | `https://arxiv.org/pdf/2301.00421`, returned v3; (1.1)–(1.4), Theorem 1.1, printed pp. 1–2 | Explicit RH premise of the Hilbert/de Branges identification; printed p. 2 visually checked. |
| RELAY ERR | Bound SCREW request, §0, references `paper_weil/ERRATUM_NOTE_SUZUKI_DRAFT.md` | Signed extension used as a proposed project repair, not as an accepted external theorem or a completed fresh audit. |
| READ CC22 | `https://arxiv.org/pdf/2205.01391`, Theorems 1.1–1.2, 3.4 | Actual arithmetic dimensions/duality exist, but the displayed degree law does not supply the quadratic coefficient of Q. |
| READ abstract only | `https://arxiv.org/abs/math/9811068` | Connes trace-formula context; no theorem from its unread body supplies a sign here. |
| RELAY, not reaudited | `2310.18423v2`, `2602.04022v1`, `2206.03682`; Bombieri, Yoshida, Zhu, Conrey–Li as summarized in K/LM/SC | No additional global positivity, finite threshold or impossibility theorem imported. The requested local-versus-global decision uses S26 directly. |
| READ acquisition pointer | Akhil Mathew, `https://amathew.wordpress.com/2013/01/28/the-riemann-roch-and-hodge-index-theorems-on-surfaces/` | Led to MIT's authored notes; not used as an independent proof of the needed growth bound. |
| CONSULTED, no relevant supplier | Milne, `https://www.jmilne.org/math/CourseNotes/AG.pdf`, searched for Hodge | No load-bearing Hodge theorem obtained from this document. |
| ACQUISITION FAILED | Attempted Edinburgh geometry notes and Clay `https://www.claymath.org/wp-content/uploads/2022/06/riemann.pdf` | No usable text obtained; no result attributed to these failed reads. |

Search-result snippets and encyclopedia hits were discovery pointers, not technical theorem sources. External reading is separated from the request-derived object definitions throughout.

### 10.3 Rejected implementations and reusable identities

These are outcome summaries, not a claim that every research possibility was exhausted.

| Candidate | First decisive fact | Reusable residue |
|---|---|---|
| A count by itself forces Hodge sign | (H6) satisfies nonnegative dimensions, quadratic RR and duality with a positive primitive square | The correct count interface needs an independent `o(n²)` error bound. |
| Reference positivity is ampleness | A positive reference metric coexists with an indefinite target, already in (H13) | Keep the same-form compatibility as an explicit equation. |
| Subtract the pole plane and import index one | P is one term of Q; no total-Q orthogonal splitting follows | `P|ℋ=0` is exact and sufficient for removing the pole contribution. |
| Count repeated zeros as new quotient coordinates | Each distinct point gives a single evaluation functional in (H9) | Weights retain multiplicity; inertia counts distinct j-orbits. |
| Treat the canonical system as an unshifted positive basis | `Q=‖·‖²_Ta+τ‖·‖²_2` | The exact shift-removal comparison is the unpaid cell. |
| Fill the cell with CC22's arithmetic RR theorem | Its nD-index has degree-one growth, not the requested surface-type quadratic coefficient | It supplies a real count model, not a source-Q identification. |
| Assert that only the limit needs work | A bad source vector survives in a compact window by continuity | Actual all-window positivity already globalizes; identification of other real-zero functions is a different task. |

Useful exact identities are (H5), (H12), (H13a), (H14) and (H15). None is a failed numerical computation. No numerical run occurred. The source count and source rigidity remain unknown; their formal implications have been proved above.

### 10.4 One exact missing lemma

**SOURCE_PRIMITIVE_NULL_RIGIDITY — [ABSTRACT][CONDITIONAL], NOT PROVED.**

Use exactly the form Q, Hilbert space ℋ, independent reference metric and Riesz operator A of (H8), namely KERNEL (K6)–(K10). Prove from those source coefficients, without assuming Weil positivity, an RH-dependent norm identity, or a zero-location hypothesis, that
\[
 \boxed{\quad
   \forall f\in\mathscr H,\qquad
   Q(f,f)=0\ \Longrightarrow\ Af=0
   \quad}
\]
Equivalently, every isotropic primitive test must lie in the already identified radical `𝒩_pt`. Equation (H14) and the existing positive source anchor show that this lemma reaches the unchanged nonnegativity consumer. No quantitative positive floor is required.
