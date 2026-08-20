# Meixner & Schäfke 1954 — verified theorem-usage cards

Josef Meixner, Friedrich Wilhelm Schäfke, "Mathieusche Funktionen und
Sphäroidfunktionen mit Anwendungen auf physikalische und technische Probleme",
Springer, Grundlehren der mathematischen Wissenschaften Band LXXI, 1954.
ISBN 978-3-540-01806-3 (print) · 978-3-662-00941-3 (eBook) · DOI 10.1007/978-3-662-00941-3
428 pages.

**Source location: `/mnt/hdd01/Paper_to_read/978-3-662-00941-3.pdf`** (owner's
Uni access, 2026-08-20). The book is **NOT** committed to this repository: it is
a copyrighted monograph of 31 MB, and a pointer plus this card is what the
project needs. Chapter 4 also exists separately as
`/mnt/hdd01/Paper_to_read/978-3-662-00941-3_4.pdf` (104 pages).

Page mapping for this scan: printed page 242 is PDF page 254, so **printed
page N is PDF page N + 12**. Satz 9 sits on printed 243 = PDF 255, entirely on
that one page; PDF 256 already opens section 3.252.

Text quality: Acrobat Paper Capture OCR. Formulas are heavily mangled;
every structural claim below was read against the surrounding prose, and the
places where the OCR is unreadable are named under NOT READ.

---

## Satz 9 (§3.2 "Die Sphäroidfunktionen ps_n^m(z; γ²)") — printed p. 243
This is the theorem CCM Lemma 7.2 and Fuchs 1964 both cite. Fuchs cites it as
"[6], Chap. 3, Theorem 9, p. 243, here γ = a², m = 0".

STRUCTURE (two statements under one heading, for `γ → +∞`, with `q = 2(n−m)+1`):

1. **Eigenvalue asymptotic**, an expansion in descending powers of `γ`:
```
λ_n^m(γ²) = −γ² + γ q + m² − (1/8)[q² + 5]
            − (1/(64γ))[q³ + 11q − 32 m² q]
            − … (further printed terms in γ^{-2}, γ^{-3}, γ^{-4}, γ^{-5})
            + O(γ^{-6})
```

2. **Mode asymptotic, first approximation, uniform on `[−1, 1]`**:
```
ps_n^m(z; γ²) = (−1)^m · C(γ) · ((n+m)! / ((n−m)! (2n+1)))^{1/2}
                · (1 − z²)^{m/2} · D_{n−m}((2γ)^{1/2} z) + O(γ^{-1})
```
where `D_ν` is the parabolic cylinder (Weber–Hermite) function and `C(γ)` is a
`γ`-power prefactor whose exponent the OCR renders as `(4γ)^{1/4}`-like but
does not resolve — see NOT READ.

K7-TAG: THEOREM (proved in the book; the page states it is obtained by the
method just developed — a linear combination ansatz in `D_{p−2r}` with a
truncated series for `λ_p(γ)`, choosing coefficients so that the residual
`‖F_γ y_p + λ_p y_p‖ · ‖y_p‖^{-1}` vanishes to as high an order in `γ^{-1}` as
possible, plus the uniform-approximation argument of §2.333.)

USED IN Q3 FOR: floor **F72.1** of the L73.2 wall,
`SELECTED_FERRERS_LEMMA72_UNIFORM_RATE` — the judge's single remaining genuine
analytic core (verdict REQ-F, commit 835d7e97, cost 8/10, described there as
`OPEN_ANALYTIC_CORE_ONE`). Until 2026-08-20 the source was not on the shelf at
all.

### The rate matches CCM, and here is the chain

Satz 9 gives the mode error as `O(γ^{-1})`. CCM Lemma 7.2 claims `O(λ^{-2})`.
These agree, through identifications each of which is already established:

```
judge's scope lock (REQ-H, 3abb8613, proved on paper from our definitions):
        Fuchs's c = a² = project γ = 2π λ²
Fuchs's own citation line:  Meixner–Schäfke γ = his a²
therefore:                  γ_MS = 2π λ²
therefore:                  O(γ_MS^{-1}) = O(λ^{-2})
```

⚠️ This is a derivation, not a Lean theorem, and it is **not** to be used as a
supplier premise in that form. It is recorded because it is the first evidence
that the paper rate and the book rate are the same statement in two coordinate
systems, rather than two different claims — which is exactly the kind of
question that killed REQ-E when left implicit.

### Uniformity is in the right variable

Satz 9's uniformity is on `[−1, 1]` in the dimensionless `z`. Our window is
`[−λ, λ]` in the physical variable, and the project already carries the
dimensionless carrier (`mode4SlepianC`, `selectedFerrersDimensionlessFourierAction`
in `D0Mode4FerrersDimensionlessFourierScaling.lean`). So `z = x/λ` maps the
book's uniformity onto the sup-norm over `[−λ, λ]` that CCM Lemma 7.2 needs.
The change of variable itself still has to be proved.

### What still stands between this page and floor F72.1

1. `D_{n−m}` is a parabolic cylinder function, not our Hermite mode. The
   standard bridge `D_n(x) = 2^{-n/2} e^{-x²/4} He_n(x)` is classical but is
   **not** in this card and not verified here.
2. The prefactor `C(γ)` must be read from a clean copy (see NOT READ), because
   an unresolved power of `γ` in front of the mode is precisely a normalization
   ambiguity, and normalization is what our graveyard is made of.
3. Satz 9 speaks about `ps_n^m`. Binding our selected Ferrers modes to that
   literal object is floor **F72.0B**, still open and still awaiting the
   judge's R1/R2 fork.
4. None of the above is Lean. Formalizing a parabolic-cylinder asymptotic is
   the 8/10 the judge priced; having the source does not lower that price, it
   only removes the "we do not have the statement" blocker.

---

## Satz 8 (same section, immediately above Satz 9) — printed p. 243
The weaker predecessor: the same mode approximation, but **in quadratic mean
over `[−1, 1]`** rather than uniformly, with the same `O(γ^{-1})` error and the
same parabolic-cylinder shape.

K7-TAG: THEOREM.

USED IN Q3 FOR: nothing directly — recorded so that nobody later cites the
`L²` statement when the sup-norm one is required. CCM Lemma 7.2 is a sup-norm
claim; Satz 8 will not supply it. Satz 9 is the one to port.

---

## NOT READ / NOT VERIFIED FROM THIS COPY
- The exact `γ`-power prefactor `C(γ)` in both Satz 8 and Satz 9. OCR renders
  it as fragments like `(4Y)t_'_` and `(~)l_!_`; the exponent is not
  recoverable from this scan. **This is load-bearing** and must be read from a
  clean page image before any port.
- The full printed eigenvalue expansion: terms in `γ^{-2}` through `γ^{-5}` are
  present on the page but their coefficients are OCR-scrambled. Only the
  leading structure `−γ² + γq + m² − (1/8)(q²+5)` was read with confidence.
- §2.333, cited on the page as the source of the uniform-approximation
  argument, was not opened.
- MEIXNER [3] and SIPS [1], cited on the following page for the recursion
  system behind the coefficients, were not opened.
- Chapter 4 (`978-3-662-00941-3_4.pdf`) was not examined at all.
