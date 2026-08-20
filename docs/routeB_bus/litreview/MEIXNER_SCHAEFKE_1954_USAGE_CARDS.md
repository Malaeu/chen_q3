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

1. **Eigenvalue asymptotic**, an expansion in descending powers of `γ`, read
   from the rendered page:
```
λ_n^m(γ²) = −γ² + γq + m² − (1/8)[q²+5] − (q/(64γ))[q²+11−32m²]
  − (1/(1024γ²))[5(q⁴+26q²+21) − 384m²(q²+1)]
  − (1/γ³)[ (1/(128·128))(33q⁵+1594q³+5621q) − (m²/128)(37q³+167q) + (m⁴/8)q ]
  − (1/γ⁴)[ (1/(256·256))(63q⁶+4940q⁴+43327q²+22470)
            − (m²/512)(115q⁴+1310q²+735) + (3m⁴/8)(q²+1) ]
  − [ (1/γ⁵)(1/(1024·1024))(527q⁷+61529q⁵+1043961q³+2241599q)
      − (m²/(32·1024))(5739q⁵+127550q³+298951q)
      + (m⁴/512)(355q³+1505q) − (m²/16)q ]
  + O(γ^{-6})
```
   For our case `m = 0` every `m`-term drops and this collapses to
```
λ_n^0(γ²) = −γ² + γq − (1/8)(q²+5) − (q/(64γ))(q²+11)
            − (5/(1024γ²))(q⁴+26q²+21)
            − (1/(128·128 γ³))(33q⁵+1594q³+5621q)
            − (1/(256·256 γ⁴))(63q⁶+4940q⁴+43327q²+22470)
            − (1/(1024·1024 γ⁵))(527q⁷+61529q⁵+1043961q³+2241599q)
            + O(γ^{-6})
```
   with `q = 2n+1`, so `q = 1` for degree zero and `q = 9` for degree four.

2. **Mode asymptotic, first approximation, uniform on `[−1, 1]`**:
```
ps_n^m(z; γ²) = (−1)^m · (4γ/π)^{1/4} · (1/(n−m)!) · ((n+m)!/(2n+1))^{1/2}
                · (1 − z²)^{m/2} · D_{n−m}((2γ)^{1/2} z) + O(γ^{-3/4})
```
where `D_ν` is the parabolic cylinder (Weber–Hermite) function.

⚠️ **CORRECTION 2026-08-20, same day.** The first version of this card gave the
remainder of the Satz 9 mode statement as `O(γ^{-1})` and left the prefactor
unread, both because the OCR layer is unusable here. The page was then rendered
as an image and read directly: the prefactor is `(4γ/π)^{1/4}` and **the raw
remainder is `O(γ^{-3/4})`, not `O(γ^{-1})`**. Satz 8, the mean-square
predecessor, is the one carrying `O(γ^{-1})`.

The judge caught the same thing independently in the REQ-I verdict (commit
082421cf) and named the resolution: `O(γ^{-1})` is the remainder **after**
dividing by the mode's own `(4γ/π)^{1/4}` scale, and in physical variables that
is `O(λ^{-2})` — the rate CCM Lemma 7.2 claims. So the number was right and its
placement was wrong; his ledger records it as
`usage_card_raw_O_gamma_minus_1: SUPERSEDED_RATE_PLACEMENT`.

```
raw Satz 9 mode remainder                          O(γ^{-3/4})
after normalising by (4γ/π)^{1/4}                  O(γ^{-1})
in physical variables, with γ = 2πλ²               O(λ^{-2})   = CCM Lemma 7.2
```

Read the page as an image before quoting any exponent from this book. The OCR
does not survive the formulas.

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

Satz 9 gives the raw mode error as `O(γ^{-3/4})`; normalised by the mode's own
scale it is `O(γ^{-1})`. CCM Lemma 7.2 claims `O(λ^{-2})`. These agree, through
identifications each of which is already established:

```
judge's scope lock (REQ-H, 3abb8613, proved on paper from our definitions):
        Fuchs's c = a² = project γ = 2π λ²
Fuchs's own citation line:  Meixner–Schäfke γ = his a²
therefore:                  γ_MS = 2π λ²
therefore:                  O(γ_MS^{-1}) = O(λ^{-2})
```

**RATIFIED by the judge** in the REQ-I verdict (082421cf): `ms_gamma = 2*pi*lambda^2`,
`project mode4SlepianC = ms_gamma`, `project mode4JacobiG = ms_gamma^2`,
`fuchs_a_squared = ms_gamma`. It remains a paper-level chain, not a Lean theorem,
and is **not** to be used as a supplier premise in that form. It is recorded because it is the first evidence
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
2. ~~The prefactor must be read from a clean copy.~~ **DONE**: `(4γ/π)^{1/4}`,
   read from the rendered page. For `m = 0` the judge writes the leading
   coefficient as `(4γ/π)^{1/4} / sqrt((2n+1)·n!)`, and the physical scalars as
   `(1/√2)·λ^{-1/2}` for degree zero and `(3/√2)·λ^{-1/2}` for degree four —
   which match the `s_0`, `s_4` of the earlier FLOORS verdict. His instruction:
   absorb the prefactor exactly once in the source normalization, never fit it.
3. Satz 9 speaks about `ps_n^m`. Binding our selected Ferrers modes to that
   literal object is floor **F72.0B**, still open and still awaiting the
   judge's R1/R2 fork.
4. None of the above is Lean — but the price DID move once the source landed.
   The judge's repricing in the REQ-I verdict:
```
F72.1 before                                  8/10
  paper scope and parameter uncertainty       1/10  CLOSED
  fixed-mode D-to-Hermite in Lean             2/10  F72.1B, LEAN_READY
  uniform big-O to eventual bound port        3/10  F72.1C
F72.1 after F72.0B                            4/10
F72.0B + F72.1 combined                       6/10
full reproof of Satz 9 in Lean                9/10  NOT SELECTED
```
   So the wall is no longer one 8/10 block: it is a predecessor plus a
   `LEAN_READY` piece plus an assembly, and reproving the book is explicitly
   off the table.

---

## Satz 8 (same section, immediately above Satz 9) — printed p. 243
The weaker predecessor: the same mode approximation with the **identical**
prefactor `(4γ/π)^{1/4}` and the same parabolic-cylinder shape, but stated
**in quadratic mean over `[−1, 1]`** rather than uniformly — and with remainder
`O(γ^{-1})`, which is *better* than Satz 9's raw `O(γ^{-3/4})`. That ordering is
the natural one: the uniform statement costs a quarter power of `γ`.

K7-TAG: THEOREM.

USED IN Q3 FOR: nothing directly — recorded so that nobody later cites the
`L²` statement when the sup-norm one is required. CCM Lemma 7.2 is a sup-norm
claim; Satz 8 will not supply it. Satz 9 is the one to port.

---

## NOT READ / NOT VERIFIED FROM THIS COPY
- ~~The exact prefactor.~~ RESOLVED by rendering the page: `(4γ/π)^{1/4}`,
  identical in Satz 8 and Satz 9. Only the remainders differ (`γ^{-1}` versus
  `γ^{-3/4}`).
- The full printed eigenvalue expansion: terms in `γ^{-2}` through `γ^{-5}` are
  present on the page but their coefficients are OCR-scrambled. Only the
  leading structure `−γ² + γq + m² − (1/8)(q²+5)` was read with confidence.
- §2.333, cited on the page as the source of the uniform-approximation
  argument, was not opened.
- MEIXNER [3] and SIPS [1], cited on the following page for the recursion
  system behind the coefficients, were not opened.
- Chapter 4 (`978-3-662-00941-3_4.pdf`) was not examined at all.


---

## ORDER TRAP, pre-killed by the judge (REQ-I verdict, 082421cf)

The parabolic cylinder order is `ν = n − m = (q−1)/2`, **not** `q`. For our two
selected modes with `m = 0`:

```
n = 0 → q = 1 → D_0        n = 4 → q = 9 → D_4
```

Using `D_q` instead of `D_{n−m}` is recorded there as
`false_order_D_q: KILLED_BY_PARITY_AND_CENTER_PLANT` and as
`FALSE_D_Q_TO_H_N_BRIDGE`. The `q` in Satz 9 is the linear slope of the
eigenvalue expansion and the harmonic-oscillator energy label; it is not an
index of the cylinder function.
