# Q2: Botha simple-even quickcheck

**DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH.**

External source: **REACHABLE**. Independent finite zeta parity/simplicity
comparison: **CONSISTENT** on all20tested carrier cells. Verdict for the
claimed full-operator theorem: **INCONCLUSIVE_RESOLUTION**. The bottom
Ritz values do not converge across the two carrier resolutions, so these
calculations neither reproduce nor refute the continuum simple-even claim.
No external code or certificate chain was executed or trusted.

The pinned GitHub source is bbb4424afbba51496a74389a5fe0716c6409bd15;
DOI10.5281/zenodo.23852617 resolves successfully. Its Theorem4.1 is on
PDFpage7; the full form is(1.1),page2. The registered grid failure and its
two stated repairs appear on pages23–24. See EXTRACTION.md and SOURCES.json.

Crosswalk: external halfwidthL=log(m)/2; our physical support length is
logm. With the explicit full Weil form and L2-normalized basis the scale
is1 and additive shift0. The requestedm55 is slightly outside the source's
L<=2 claim, which ends at exp4=54.59815. The gridm47 samples near, rather
than exactly at, its registered failure window. NORMALIZATION.md documents
independent constant/first-odd entry replays with maximum discrepancy7.39e-80.

## Native zeta matrices, N=m

|m|lambda_even0|lambda_even1|lambda_odd0|odd-even gap|even1-even0 gap|
|---:|---:|---:|---:|---:|---:|
|3|1.00455e-6|8.11650e-3|1.16480e-4|1.15475e-4|8.11549e-3|
|5|3.55381e-12|1.38420e-7|1.02508e-9|1.02152e-9|1.38416e-7|
|7|2.77371e-17|2.30641e-12|1.04999e-14|1.04722e-14|2.30638e-12|
|10|1.34396e-24|3.55011e-19|8.59891e-22|8.58547e-22|3.55009e-19|
|15|1.96740e-35|1.28406e-29|2.18856e-32|2.18660e-32|1.28406e-29|
|20|2.58447e-46|3.67889e-40|4.29976e-43|4.29718e-43|3.67889e-40|
|30|1.57811e-66|4.94848e-60|3.50786e-63|3.50628e-63|4.94848e-60|
|40|2.98118e-85|2.06500e-78|1.14250e-81|1.14220e-81|2.06500e-78|
|47|8.65901e-99|7.34267e-92|3.19007e-95|3.18921e-95|7.34267e-92|
|55|5.68994e-113|9.58868e-106|3.10391e-109|3.10334e-109|9.58868e-106|

Every native even ground is positive and lies below both the next even
level and odd bottom. The same finite ordering holds at N=2m for m<=20
and N=m+8 for the larger windows. The two source quadratures use128/160
Gauss-Legendre nodes on each of8panels. Precision is120digits except
m47/55, independently repeated at160digits after the initial120digit
roundoff guard found those tiny cells unresolved.

All preferred zeta gap signs agree under quadrature refinement. The maximum
relative eigenvalue replay difference is2.07e-25; the smallest ratio of a
positive parity/simplicity gap to the quadrature replay discrepancy is
2.51e28. These replay comparisons are floating diagnostics, not error
bounds for the continuum or interval eigenvalue certificates.

## Carrier resolution is not convergence

None of the10zeta windows satisfies relative Ritz-value convergence1e-3
between the chosen N values. Examples:

|m|N pair|lambda_even0 at lowN / at highN|
|---:|---|---:|
|3|3,6|9.63771|
|7|7,14|4.46286e6|
|20|20,40|4.19687e21|
|47|47,55|5.83750e9|
|55|55,63|1.11205e10|

At m55 the values are5.68993531345e-113 and5.11664007140e-123.
Consequently the shared finite parity ordering cannot be substituted for
a proof that the true closed operator has the same parity or multiplicity.
The source itself claims much smaller continuum scales near halfwidth2;
our finite upper values do not contradict its claimed lower/upper bounds.

## Broken worlds

The same matrix formulas with the actual DH coefficients and gamma term,
no DH pole, produce a strict odd-below-even finite ordering:

|world|m|N|lambda_even0|lambda_odd0|odd-even gap|
|---|---:|---:|---:|---:|---:|
|DH|47|55|-.280337823|-.298992435|-.018654612|
|DH|55|55|-.663920646|-.712933819|-.049013173|
|DH|55|63|-.714447598|-.753793976|-.039346377|
|plant|5|5|-.021211628|-.026547449|-.005335821|
|plant|5|10|-.023080012|-.031878131|-.008798118|
|plant|40|40|-.463963519|-.557017055|-.093053536|
|plant|40|48|-.465170539|-.558349969|-.093179430|

DHm47 changes its finite parity conclusion when N increases from47to55:
this is why native resolution alone is inadequate. The m47 enlarged-carrier
violation is inside the external zeta halfwidth range; m55 is the explicitly
requested just-outside-range control. Neither DH nor the planted source is
the zeta form appearing in the external theorem, so these are discriminators,
not counterexamples to that theorem. No continuum parity limit is inferred
from the broken-world two-carrier scans either.

The planted world is the same added quartet w=2pi/log2+i/4, multiplicity1.
Its even update is4Re(F_even(w)F_even(w)^T); its odd update is
4Re(S_odd(w)S_odd(w)^T), where S is the sine transform. A direct physical
odd-entry check verifies the sign. Further finite plant violations occur
at m10and20 on both tested carriers; all rows are retained in preferred.csv.

P3(prior.80): supported only as finite-matrix consistency; the full claim
remains INCONCLUSIVE_RESOLUTION. P4(prior.40): supported by finite DH
violations, including a parity change under refinement. A generic assertion
that simple-even holds in both the true and every broken world is not
supported by this grid.

## Files and reproduction

preferred.csv contains both carrier resolutions for every world/window;
quadrature_replay.csv and carrier_resolution.csv preserve both comparisons.
The original120/160digit output and unresolved120digit high-m cells remain
in the raw tables; they are not silently rounded into positive evidence.
check.py implements our matrix formulas; external sources were read only.

```
uv run --with mpmath python check.py
uv run --with mpmath python check.py --dps 160 --ms 47 55
uv run --with mpmath python normalization.py
uv run --with mpmath python analyze.py
```

The outcome is a source-aware bounded numerical check, not an independent
verification of the external theorem or any RH claim.
