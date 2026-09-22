# Fokas–Lenells: exact finite-window Mellin crosswalk

- review status: `reviewed`
- safe for embeddings: `yes`
- classification: `background route / source-pinned research candidate`
- date: `2026-09-22`
- live frontier changed: `no`
- proof admission: `none`
- Route B: `CHALLENGER_NOT_RH`; `PX_RH_CLAIM: NOT_MADE`

## Provenance and retrieval status

Owner supplied a new UTF-8 export of Proshka's Fokas review. The archived raw
file is linked below after ingestion. Raw SHA-256:
`10b6446e51a48e43e1808d6d8fe1024b46063f8edea14ae8809dd52bc9f4e098`.

[Living source chat](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6aafb38a-a7a4-83eb-9940-84a574eae168).
The full VERDICT.md preview was read in that chat on 2026-09-22. It declares
`PROJECT_SOURCE_COMMIT: 70da2617592c5dc5d14215f23dc487f2004f58b7`,
`PROJECT_SOURCE_BLOB: 51c54f58d8d091b70b545e09094157f0384c94b9`, and
`PRODUCTION_REQUEST_BINDING: NO_REGISTERED_TXT_THIS_IS_LITERATURE_REVIEW_ONLY`.
This review is imported research, not a registered production response.

The pasted `sandbox:/mnt/data/fokas_routeb_2026-09-22/VERDICT.md` and
`fokas_routeb_audit.zip` links are session-local, not repository paths. Browser
clicks reported download start, but no local file bytes were obtained. The
original ZIP, registration.json, identity_checks.py and result data therefore
remain **NOT_RETRIEVED**. The claimed 18 controls and registration digest
`97ed0b2870d0cc17d132aebdb0eb8f8ee0f0b1af8a9d8f98033dd8c533897fff`
are Proshka-reported, not independently reproduced here. Do not manufacture
those artifacts or index their numerical claims as verified results.

## Checked source and exact object

The pinned [Ferrers–Mellin generator](../../../docs/routeB_bus/proshka/ccm_exact_source_generator_2026-09-20/VERDICT.md)
§4 G4–G7 is the primary project formula. Current intake base is
`63c028ac17995e9abb57a6c4a95cefc92ec1c63f`.
For integer m≥2, L=log m, λ=√m, n∈ℤ, put

\[
s_n=\tfrac12-2\pi i n/L,\qquad D_m(s)=\sum_{k=1}^m k^{-s}.
\]

For bounded measurable H on [−1,1], set h(x)=H(x/λ) on [−λ,λ], zero outside;
E_*h(u)=√u Σ_{k≥1}h(ku), and
V_{n,m}(u)=L^{-1/2} exp(2πin log(λu)/L).
The unchanged coefficient is

\[
\alpha_{m,n}(H)=\int_{1/\lambda}^{\lambda}
\overline{V_{n,m}(u)}E_*h(u)\,du/u.
\]

For the actual source use the selected mode0/mode4 Ferrers combination at
c=2πm, retaining the grouped infinite Legendre series. It is not a finite
polynomial or the stored decimal cache. Final finite row normalization is
q_n=α_n/Z_{m,N}, Z²=Σ_{|n|≤N}|α_n|², with **Z>0 still required**.

## Surviving paper identity: paired window remainder

Define ℋ(s;x)=∫_0^x H(v)v^{s−1}dv and ℋ(s)=ℋ(s;1), Re s>0.
A change of variable v=ku/λ in each of the finitely many nonzero summands gives

\[
\alpha_{m,n}(H)=\frac{m^{1/4}}{\sqrt L}
\sum_{k=1}^m k^{-s_n}\int_{k/m}^1H(v)v^{s_n-1}\,dv.
\]

The factor uses m^{s_n}=√m. Off this lattice the corresponding analytic
expression has prefactor m^{s−1/4}/√L; do not extend the lattice prefactor
unchanged to arbitrary complex s. Split at zero and use
D_m(s)=ζ(s)−ζ(s,m+1), with Hurwitz ζ continued analytically. Then exactly

\[
\alpha_{m,n}(H)=\frac{m^{1/4}}{\sqrt L}
\left[\zeta(s_n)\mathcal H(s_n)-\mathcal R_m(s_n;H)\right],
\]
\[
\mathcal R_m(s;H)=\zeta(s,m+1)\mathcal H(s)
+\sum_{k=1}^m k^{-s}\mathcal H(s;k/m).
\]

The separated ζ/Hurwitz formula is read at s≠1 in Re s>0; at s=1
only its meromorphic combination has the removable-pole interpretation.
The coefficient lattice Re s_n=1/2 never meets that pole.

This derivation is checked algebraically against G4 (take H(v)=v^d).
Bounded measurability gives integrability on Re s>0; the finite sum requires no infinite
sum interchange. For the actual Ferrers expansion, absolute summability and
|P_j|≤1 justify grouped integration; a global regrouping by monomial degree
has not been justified. This is PAPER representation progress, not Lean
admission, a bound on R_m, or positive Weil energy.

## External primary-source links

The following landing pages were independently opened on 2026-09-22. Versioned
arXiv links replace ambiguous references. Full theorem-hypothesis verification
for the contour import remains a separate discovery check.

1. [Fokas–Lenells, Memoirs AMS 275(1351), 2022; arXiv:1201.2633v3](https://arxiv.org/abs/1201.2633v3).
   [Versioned PDF](https://arxiv.org/pdf/1201.2633v3). Intended locator:
   Theorem 2.1, equation (2.3), substituting s↦1−s. This is the exact
   finite-Dirichlet-sum supplier, not a large-t bound for every mode.
2. [Fokas–Lenells, Hankel/Bleistein, arXiv:2605.03466v1](https://arxiv.org/abs/2605.03466v1).
   [HTML](https://arxiv.org/html/2605.03466v1).
   [Reported journal DOI](https://doi.org/10.3390/math14122204).
   The abstract preserves a special transition integral. Project phase/parameter
   matching and a uniform source-family bound are OPEN.
3. [Fokas, Atkinson/divisor error terms, Cambridge repository](https://www.repository.cam.ac.uk/items/cd8703ca-b07c-4503-ac42-483c587df3c3).
   [DOI](https://doi.org/10.1098/rsos.250855).
   Background lead only; no identified operator bridge to the project K.
4. [Harvard CMSA seminar announcement](https://cmsa.fas.harvard.edu/event/fokas/).
   Event metadata is not a theorem or a substitute for the announced manuscript.

## What does not follow

- R_m does not disappear from writing α as a zeta term minus R_m.
- Zero mass does not annihilate Mellin moments: H=P₂=(3v²−1)/2 has
  ∫_0^1H=0 but ℋ(1/2)=−2/5. This control is outside the actual selected pair;
  it rejects only a mass-zero-only argument, not a special prolate identity.
- T_{m,n}=2π|n|/log m is zero at n=0 and tends to zero for fixed n as m grows.
  Large-T asymptotics alone cannot cover the whole row.
- Fixed O(T^{-P}) does not automatically meet an exponentially small budget.
- [Realification](../../../docs/routeB_bus/proshka/ccm_realification_transfer_2026-09-20/VERDICT.md)
  certifies the unchanged complex cache only in its stated finite cell/class.
  Analytic-source error, cofinal floor and transform budget remain OPEN.
- Corrected bandwidth numerics are diagnostics, not equality of exact source
  and cache or certified transfer of the floor. Phase-invariant failure of
  cache=source is not a proof of ground≠trial.
- The tracking budget is C_E(m_j,N_j)||r_j||/δ_j + Tail_j(E) + NormError_j(E),
  not multiplication by δ_j. Ground selection and a valid spectral separation
  must precede the residual estimate.

## Consumer, search dictionaries, and next decisive test

Downstream target: `FiniteGroundTransformToCCMTrialLocallyUniform`.
Intermediate requirement: the **same exact source** with a proved family
error bound and compatible ground selection, normalization and compact-domain
transform budget. See [Goal 058](../../../docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md)
and [bounded search brief](../../../docs/Codex/BRIEF_2026-09-22_FOKAS_PAIRED_WINDOW.md).
The exact production theorem/consumer edge remains UNBOUND; discovery may yield
candidates, not a consumed supplier or a closed node.

Search dictionaries:
- Mellin convolution, dilation sum, finite-window Mellin transform, incomplete Mellin transform;
- Abel–Plana, Hurwitz zeta remainder, finite Dirichlet sum, Hankel contour;
- prolate Sturm–Liouville, Lagrange identity, boundary concomitant, Green identity.

`TRY_FOKAS_PAIRED_WINDOW_REMAINDER`: retain the two terms of R_m together;
use the actual selected mode equations to derive exact boundary terms or
cancellation, before absolute-value bounds. Preserve zero mode, both signs of n,
c=2πm, grouped Ferrers expansion, support, phase, measure and Z>0.
Return one exact identity with its domain and surviving boundary terms, or an
explicit obstruction. No new spectral grid. No floor/limit claim without its
own hypotheses and consumer mapping.

## Archived original

[Owner-supplied raw text](../incoming_notes/archive/20260922_121348_2026_09_22_fokas_paired_window/raw/2026_09_22_fokas_paired_window.txt); bytes preserved unchanged.
