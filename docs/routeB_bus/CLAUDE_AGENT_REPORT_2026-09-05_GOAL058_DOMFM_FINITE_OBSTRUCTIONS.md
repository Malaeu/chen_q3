# CLAUDE AGENT REPORT — GOAL058 DOM/FM finite obstructions

**Date:** 2026-09-05
**Branch:** `rh_clean`
**Result:** `DOMFM_FINITE_OBSTRUCTIONS_KERNEL_GREEN`

**Source:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DOM_FM_ZERO_MARGIN_AND_TRADEOFF_LEMMA_2026-09-05.md`
— items D1.1 (TRADE), D1.2 (EIG-TRADE), D2.4 (finite version, incl. SIGNED-PSD),
D3.2 (COMP-GAP), and their "Lean-ready heads" paragraphs.

**Artefact:** `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/DomfmFiniteObstructions.lean`
(847 lines, 39 theorems, 8 definitions, namespace `Q3.RouteB.Domfm`).

No existing file was edited. Nothing was committed or pushed.

---

## 1. What is proved

Everything below is finite: complex inner product spaces, finite matrices, finite
sums. There is no integral, no measure, no zeta input, and no statement about the
sign of the Weil form anywhere in the file.

### D1.1 — the trade-off (TRADE)

Abstract engine `rayleigh_le_of_projection_witness`, matrix head
`domfm_projected_rayleigh_le`:

```
theorem domfm_projected_rayleigh_le
    {K : Matrix (Fin n) (Fin n) ℂ} (hK : K.IsHermitian)
    {Kop : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hKop : ∀ x i, Kop x i = ∑ j, K i j * x j)
    {V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} {y p : EuclideanSpace ℂ (Fin n)}
    (hy : y ≠ 0) (hp : p ≠ 0) (hpV : p ∈ V)
    (horth : ∀ v ∈ V, ⟪v, y - p⟫_ℂ = 0) :
    rayleigh Kop p ≤ rayleigh Kop y + 2 * ‖Kop‖ * (‖y - p‖ / ‖y‖)
```

Conforming to the judge's head paragraph:

* `E = EuclideanSpace ℂ (Fin n)`, `K : Matrix (Fin n) (Fin n) ℂ`, `K.IsHermitian`;
* the **coefficient identity** between `Kop` and `K` is carried explicitly as
  `hKop` — it is not left to an API spelling; `toEuclideanCLM_coeff` proves that
  `Matrix.toEuclideanCLM K` satisfies it, so the hypothesis is never vacuous;
* `M := ‖Kop‖` is the **operator norm** of the continuous linear map. No entrywise
  matrix norm is substituted anywhere;
* the projection is given by **witnesses** (`p ∈ V` and `∀ v ∈ V, ⟪v, y-p⟫ = 0`),
  not by an unverified projection API;
* `p ≠ 0` is a hypothesis, as the judge's boundary check demands.

Supporting pieces, each proved: `re_inner_sub_map_add` (the exact polarisation
`R(v) − R(u) = Re⟪v−u, T(v+u)⟫` for symmetric `T`), `rayleigh_real_smul`
(normalisation invariance — both vectors are normalised before the estimate, so
no denominator is dropped), `norm_proj_sq_eq` (Pythagoras `‖y‖² = ‖p‖² + ‖y−p‖²`),
`projection_defect_lt_one` (`d < 1` follows from `p ≠ 0`).

Variational corollary (left half of TRADE), both forms:

* `domfm_projected_rayleigh_attained_on_unit` — `∃ w ∈ V, ‖w‖ = 1 ∧ R(w) = R(p)`;
* `domfm_restricted_min_le_projected_rayleigh` (and matrix alias
  `..._matrix`) — `sInf (rayleigh T '' {w | w ∈ V ∧ ‖w‖ = 1}) ≤ rayleigh T p`,
  with `BddBelow` supplied by `neg_opNorm_le_rayleigh`.

### D1.2 — the eigenvector improvement (EIG-TRADE)

`domfm_eigenvector_projection_quadratic_error` (engine
`eigenvector_projection_quadratic_error`), under D1.1's hypotheses plus
`Kop y = (lam : ℂ) • y`, gives **both** conclusions:

```
rayleigh Kop p - lam = (⟪y-p, Kop (y-p) - lam • (y-p)⟫_ℂ).re / ‖p‖ ^ 2
∧ |rayleigh Kop p - lam| ≤ (‖Kop‖ + |lam|) * d ^ 2 / (1 - d ^ 2)
```

with `d = ‖y-p‖/‖y‖`. The exact identity is proved from the eigen-equation
(`⟪y, (K−λ)(y−p)⟫ = 0` by symmetry), not assumed; `1 − d² = ‖p‖²/‖y‖² > 0` is
derived from `p ≠ 0`.

### D2.4 (finite) — the absolute-Schur certificate class is empty

Definitions: `signedDegree J i = ∑ j, J i j`, `absoluteDegree J i = ∑ j, |J i j|`,
`IsAbsoluteSchurWeight J q ↔ (∀ i, 0 < q i) ∧ ∀ i, ∑ j, |J i j| * (q j / q i) ≤ d i`,
and the signed quadratic form `signedForm`.

**Impossibility** — `domfm_no_positive_absolute_schur_weight`:

```
(J : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i j, J i j = J j i)
(hdefect : ∑ i, (signedDegree J i - absoluteDegree J i) < 0) :
    ¬ ∃ q : Fin n → ℝ, IsAbsoluteSchurWeight J q
```

Proof exactly as prescribed: sum the row inequality over `i`, symmetrise
(`schur_sum_swap`), apply `z + 1/z ≥ 2` (`two_le_ratio_add_ratio`), contradict the
negative defect. No zeta theory, no spectral-gap estimate.

**Sufficiency** — `domfm_absolute_schur_sufficient`: if such a `q` exists then
`0 ≤ signedForm J s` for every `s : Fin n → ℂ`, via
`2|sᵢ||sⱼ| ≤ |sᵢ|² qⱼ/qᵢ + |sⱼ|² qᵢ/qⱼ`. This is what makes the impossibility a
kill of a *proof method* rather than a bare non-existence statement.

`signedForm_eq_offDiagonal` converts the full double sum used internally into the
`i ≠ j` sum of the verdict, under `J i i = 0`.

### D2.4 — the mandatory nonnegativity plant (SIGNED-PSD)

`domfm_signed_three_vertex_psd_plant` bundles seven facts about
`plantJ3 = !![0,2,-1; 2,0,2; -1,2,0]` (edge weights `w₁₂ = w₂₃ = 2`, `w₁₃ = −1`):

1. `∀ s₁ s₂ s₃ : ℂ, 2‖s₁−s₂‖² + 2‖s₂−s₃‖² − ‖s₁−s₃‖² = ‖s₁ − 2s₂ + s₃‖²`;
2. `plantLaplacian3 = !![1,-2,1; -2,4,-2; 1,-2,1] = diagonal (signedDegree plantJ3) − plantJ3`;
3. its row sums are zero;
4. `plantJ3 0 2 < 0` (a genuinely negative interaction edge);
5. `∑ᵢ (dᵢ − aᵢ) = −4 < 0`, so the obstruction of the previous theorem applies;
6. hence **no** positive absolute-Schur weight exists for it;
7. and yet `∀ s, 0 ≤ signedForm plantJ3 s` (via 1).

Items 6 and 7 together are the judge's point: reading (SCHUR-KILL) as negativity
of the form is a demonstrable logic error. The file says so in the docstring and
proves it.

### D3.2 — the compression gap (COMP-GAP)

`domfm_compressed_gram_minus_shift`, reusing `Q3.RouteB.weilShiftMatrix` from
`WeilGramMinusShift.lean`:

```
Zᴴ * weilShiftMatrix Γ cL β * Z + (e : ℂ) • (Zᴴ * Z)
  = Zᴴ * Γ * Z - ((cL - e : ℝ) : ℂ) • (Zᴴ * Z) - (2 : ℂ) • rankOneStar (Zᴴ *ᵥ β)
```

an exact matrix identity, no positivity used, redundant `Z` allowed and no Gram
matrix inverted. The equivalence `domfm_compressed_gram_minus_shift_posSemidef_iff`
is the literal (COMP-GAP) statement. Supporting lemma
`conjTranspose_rankOneStar_mul` : `Zᴴ (ββ*) Z = (Zᴴβ)(Zᴴβ)*`.

**Correction to the requested wording, worth recording.** The compressed shift is
carried by `ZᴴZ`, **not** by the identity matrix of the compressed index type. The
compressed object is therefore a `weilShiftMatrix` again only when `Z` is
isometric; that special case is
`domfm_compressed_gram_minus_shift_isometry` (hypothesis `Zᴴ * Z = 1`). Stating
the general case with `(cL−e) • 1` would have been false. This matches the
verdict's own formula, which writes `G_Z = Z*Z` throughout.

Plant — `domfm_proper_compression_negative_complement_plant`: with
`K = weilShiftMatrix (diag(0,2)) 1 0 = diag(−1,1)` (reusing
`Q3.RouteB.weilShiftMatrix_plant_eq` and `..._plant_not_posSemidef`) and
`Z = (0,1)ᵀ`, the compressed matrix `ZᴴKZ = (1)` is positive semidefinite while
`K` is not. A dictionary is not a harmless change of basis unless its range is
proved full.

---

## 2. Shelf check performed before writing

`rg -n "rayleigh|Rayleigh|Schur|posSemidef" q3.lean.aristotle/Q3 | head -n 30`
returned: `Q3/Axioms.lean` (`RayleighQuotient` over ℝ for Toeplitz matrices,
`Szego_Rayleigh_lower_bound` and `Schur_test` as Tier-1 **axioms** — deliberately
not touched or used here), `Q3/Proofs/RouteB/P59SignFreeRitz.lean` (real
`EuclideanSpace ℝ`, Ritz defect machinery — different object: it needs a spectral
decomposition and a gap, whereas D1.1 needs neither), and
`Q3/Proofs/RouteB/WeilGramMinusShift.lean`.

Actual reuse: `WeilGramMinusShift.lean` — `weilShiftMatrix`, `rankOneStar`,
`weilShiftMatrix_plant_eq`, `weilShiftMatrix_plant_not_posSemidef`. This is the
only Q3 import of the new file.

`P59SignFreeRitz.lean` was inspected and **not** reused: it is real-scalar and its
`projectiveDefect` estimates run through eigenbasis weights and a spectral gap;
D1.1/D1.2 are gap-free and complex, so nothing there fits without weakening the
statement.

---

## 3. Validation (kernel channel)

All commands run from the stated directories; `${PIPESTATUS[0]}` recorded.

### 3.1 `lake env lean`

```
$ cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle
$ lake env lean Q3/Proofs/RouteB/DomfmFiniteObstructions.lean
PIPESTATUS0=0
```

No output at all: zero errors, zero warnings (the `mathlibStandardSet` and
`unusedSectionVars` linters are disabled at the top of the file, as in
`WeilGramMinusShift.lean`; every other linter is live and silent).

### 3.2 `lake build`

```
$ lake build Q3.Proofs.RouteB.DomfmFiniteObstructions
✔ [2383/2383] Built Q3.Proofs.RouteB.DomfmFiniteObstructions (20s)
Build completed successfully (2383 jobs).
PIPESTATUS0=0
```

### 3.3 `scripts/q3_check.sh`

```
$ cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean
$ scripts/q3_check.sh Q3/Proofs/RouteB/DomfmFiniteObstructions.lean
lean Q3/Proofs/RouteB/DomfmFiniteObstructions.lean
scan Q3/Proofs/RouteB/DomfmFiniteObstructions.lean
q3_check ok
PIPESTATUS0=0
```

No hole marker (`sorry` / `admit` / `exact?`) anywhere in the file, including
docstrings; no new `axiom` in the diff.

### 3.4 `#print axioms` for every theorem

Scratch file
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/axioms_domfm.lean`
imports the module and prints the axioms of all **39** theorems. Every single line
reads:

```
'Q3.RouteB.Domfm.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

for
`re_le_norm_complex`, `abs_re_le_norm_complex`, `inner_self_ofReal`,
`rayleigh_of_norm_one`, `rayleigh_real_smul`, `re_inner_sub_map_add`,
`neg_opNorm_le_rayleigh`, `rayleigh_le_of_projection_witness`,
`projection_defect_lt_one`, `norm_proj_sq_eq`,
`domfm_projected_rayleigh_attained_on_unit`,
`domfm_restricted_min_le_projected_rayleigh`,
`eigenvector_projection_quadratic_error`, `toEuclideanCLM_coeff`,
`isSymmetric_of_isHermitian`, `domfm_projected_rayleigh_le`,
`domfm_restricted_min_le_projected_rayleigh_matrix`,
`domfm_eigenvector_projection_quadratic_error`, `signedForm_eq_offDiagonal`,
`two_le_ratio_add_ratio`, `schur_sum_swap`,
`domfm_no_positive_absolute_schur_weight`, `domfm_absolute_schur_sufficient`,
`plantJ3_symm`, `plantJ3_diag`, `plantJ3_negative_edge`, `plantLaplacian3_eq`,
`plantLaplacian3_row_sums`, `domfm_signed_three_vertex_identity`,
`plantJ3_signedForm`, `plantJ3_signedForm_nonneg`, `plantJ3_defect`,
`domfm_signed_three_vertex_psd_plant`, `conjTranspose_rankOneStar_mul`,
`domfm_compressed_gram_minus_shift`,
`domfm_compressed_gram_minus_shift_posSemidef_iff`,
`domfm_compressed_gram_minus_shift_isometry`, `plantZ_compression_eq`,
`domfm_proper_compression_negative_complement_plant`.

`PIPESTATUS0=0`. Exactly the expected triple; no `sorryAx`, no project axiom.

### 3.5 Import firewall

```
$ bash scripts/check_import_firewall.sh
OK: import-firewall check
... "status": "PASS"
exit=0
```

---

## 4. Second channel — numerical check, written from the statements

Script:
`/tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/6bd00a97-564a-4947-8560-8e2e08594119/scratchpad/domfm_numeric_check.py`
(numpy, seed 20260905). It was written from the mathematical statements, not from
the Lean proof terms; random Hermitian matrices, random subspaces via QR, random
complex test vectors.

```
(1) TRADE      min slack (R(y)+2Md-R(p))      = 1.681378e-01   (must be >= 0)
(1) identity   max |R(p)-R(y) - Re<v-u,K(v+u)>| = 9.714e-16
(1) product    max | ||v-u||||v+u|| - 2d |      = 1.110e-15
(1) variational min (R(p) - lambda_min(K|V))    = -8.881784e-16   (must be >= 0)
(2) EIG exact  max |R(p)-lam - Re<r,(K-lam)r>/||p||^2| = 2.967e-13
(2) EIG bound  min ((M+|lam|)d^2/(1-d^2) - |R(p)-lam|) = 4.780428e-03   (must be >= 0)
(3) symmetrisation min (sum_ij|J|q_j/q_i - sum_i a_i) = 2.526495e-05   (must be >= 0)
(3) no random positive q ever satisfied (SCHUR) when sum(d-a)<0: True
(3) sufficiency  min signedForm over nonneg-J plants   = 1.166017e-02   (must be >= 0)
(4) identity   max |2|s1-s2|^2+2|s2-s3|^2-|s1-s3|^2 - |s1-2s2+s3|^2| = 2.842e-14
(4) degrees d = [1.0, 4.0, 1.0], a = [3.0, 4.0, 3.0], sum(d-a) = -4.0   (must be < 0)
(4) Laplacian = [[1.0, -2.0, 1.0], [-2.0, 4.0, -2.0], [1.0, -2.0, 1.0]], row sums = [0.0, 0.0, 0.0]
(4) min signedForm over random s = 6.035696e-03; lambda_min(L) = -2.243e-16   (both >= 0)
(5) COMP-GAP   max entrywise |LHS-RHS| = 1.711e-13
(5) plant      lambda_min(Z*KZ) = 1.000 (>=0), lambda_min(K) = -1.000 (<0)
```

Trials: 400 (item 1), 400 (item 2), 400 (item 3), 2000 + 2000 (item 4), 300
(item 5). The one negative number, `-8.88e-16` in the variational line, is the
floating-point zero of the equality case (`V` containing the projection direction
of the compression minimiser); it is not a violation.

The numerical channel is **DIAGNOSTIC, NEVER A PROOF**. The proof channel is the
kernel run in §3; the numbers above only exclude a mis-stated theorem.

---

## 5. Boundaries — what this file does NOT claim

* No analytic object appears: no integral, no measure, no Fourier transform, no
  prime sum, no `ξ`. D1.3, D2.1, D2.2, D2.3, D3.1, D3.3 and all of D4 of the
  verdict are **out of scope** and are not touched.
* Nothing is asserted about the sign of the Weil form, of `K_m`, of `Γ_m`, or of
  `T_ε`. `domfm_no_positive_absolute_schur_weight` excludes a *certificate class*;
  `domfm_signed_three_vertex_psd_plant` exists precisely to block the inference
  from that exclusion to negativity of the form.
* The source crosswalk from `Γ_m`, `α`, `β`, `c_L` to the literal CCM entries
  (`ccmQKernel`, `ccmW02Entry`, `ccmPrimeEntryN1`, `ccmWREntry`) is **not** done
  here; it remains the separate PAPER obligation named in D3.2.
* `(SCHUR-KILL)`'s explicit constant `−(43/42)ℓ₀² log(8/7)` and `(DEFECT)` are
  analytic and are **not** formalised; only the finite mechanism that they feed is.
* Nothing is conditional on RH; no route is promoted.

## 6. Open items handed back

1. `domfm_full_range_compression_posSemidef_iff` (surjective synthesis ⇒ the
   compressed inequality is equivalent to `K + eI ⪰ 0`) is named in the verdict
   but was not in this task's list; it is a short follow-up on top of
   `domfm_compressed_gram_minus_shift`.
2. `domfm_signed_degree_defect` (DEFECT) and `domfm_canonical_schur_defect_upper_bound`
   (SCHUR-KILL) are analytic heads and stay open.
3. The wording correction in §1 (D3.2) — compressed shift is `ZᴴZ`, not `1` —
   should be carried into any prose that quotes (COMP-GAP).

**Result code: `DOMFM_FINITE_OBSTRUCTIONS_KERNEL_GREEN`.**
