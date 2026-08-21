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

---

## §3.22 Satz 1 (existence of the eigenvalues and of the regular solutions) — printed p. 235

Read from the rendered page (PDF 247), not from OCR.

VERBATIM (German, as printed):
"Für jedes reelle γ² hat die Sphäroiddifferentialgleichung (2) abzählbar
unendlich viele Eigenwerte λ, zu denen es eine Lösung gibt, die bei z = ±1
stetig, also von der Form (1 − z²)^{m/2} g(z) mit einer ganzen Funktion g(z)
ist. Diese Eigenwerte sind sämtlich reell und einfach. Die reellen
Eigenwertpaare λ, γ² liegen in der (λ, γ²)-Ebene auf regulär analytischen
charakteristischen Kurven λ(γ²), die wir mit λ = λ_n^m(γ²), λ_n^m(0) = n(n+1)
(n = m, m+1, m+2, …) festlegen können. Die zum Eigenwertpaar λ_n^m(γ²), γ²
gehörende Eigenlösung ist mit n − m gerade oder ungerade."

K7-TAG: THEOREM (proved in the book, obtained in §3.22 from the §1.5 general
theory whose hypotheses 1.–8. are verified on the preceding page).

USED IN Q3 FOR: this is the **existence** statement floor F72.0B2B needs, after
the REQ-2026-08-20-L verdict ratified that mathematical existence suffices and
constructive implementation is not required. It is the judge's named
`NEXT_CHEAPEST_DECISIVE_TEST: SATZ9_FIRST_KIND_EXISTENCE_PROVENANCE_CARD`.

WHAT IT SUPPLIES, FIELD BY FIELD, against `Satz9SourceData`:

```
existence of the mode        "zu denen es eine Lösung gibt"           ✓
regularity                   continuous at z = ±1, form (1−z²)^{m/2} g,
                             g ENTIRE — so real-analytic inside and
                             continuous up to the endpoints            ✓
parity                       "mit n − m gerade oder ungerade";
                             for m = 0 and n ∈ {0,4} both n−m are even,
                             so BOTH selected modes are EVEN           ✓
the eigenvalue itself        λ_n^m(γ²), real and simple                ✓
branch identification        λ_n^m(0) = n(n+1), n = m, m+1, …
                             so for m=0: λ_0^0(0) = 0, λ_4^0(0) = 20   ✓
```

SIMPLICITY IS THE LOAD-BEARING WORD. "sämtlich reell und einfach" means the
eigenvalue determines its solution up to a scalar, which is exactly the
hypothesis our center-normalized uniqueness receiver
(`G6N1CenterNormalizedUniquenessReceiver.lean`) turns into an equality of
normalized views. Without simplicity the receiver would still be true but the
source side could be a different solution at the same eigenvalue.

MONOTONICITY, recorded because it may matter for the crosswalk:
`−1 < λ'(γ²) < 0` for all real `γ²`, and the curves do not intersect.

### WHAT IT DOES NOT SUPPLY

~~**Nonzero centre value.** The page says nothing about `ps_n^0(0; γ²) ≠ 0`.~~
**RESOLVED 2026-08-21, and not by citation.** The book does not state it and
does not need to: it follows from the other fields. An even solution has zero
derivative at the centre; if its value there were zero too, its centre data
would coincide with the zero function's, which solves the same homogeneous
equation, and uniqueness would force it to vanish identically on the window.
A nontrivial even solution therefore cannot vanish at the centre.

Proved in `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1EvenSolutionCenterNonvanishing.lean`
(blob f353622e), `center_ne_zero_of_even_of_nontrivial`, zero errors on the
first run. The hypotheses are parity, the equation and nontriviality — no paper
input and no project object. So the `center_ne` field of `Satz9SourceData`
does not have to be sourced; an inhabitant exhibiting a nontrivial even
solution gets it for free.

The `γ = 0` Legendre values `P_0(0) = 1`, `P_4(0) = 3/8` are consistent with
this but were never the argument.

**The branch crosswalk W13.7.** The labelling `λ_n^m(0) = n(n+1)` pins which
characteristic curve is meant, in the book's own normalization of the ODE. Our
project carries `mode4ClassicalEvenEigenvalue`. Whether the two labellings name
the same branch is exactly the open obligation, and the verdict is explicit
that it does not follow from the shared parameter:
`theta_equality_is_automatic_from_G: false`.

**The physical lift.** Satz 1 is stated in the dimensionless `z ∈ [−1,1]`. The
divergence-form equation our receiver consumes is in the physical variable on
`[−λ, λ]`. That transport is W13.8/W13.9 and is not on this page.

### NOT READ on this page
- §1.5 and §1.6, whose hypotheses 1.–8. are checked on printed p. 235 just
  above Satz 1, were not opened.
- Satz 2 of the same section (analytic continuation of `λ_n^m` in the complex
  `γ²`-plane) was read but is not needed here.
- Figures 13–17 on printed pp. 236–237 were not examined.

---

## §3.22 Satz 1, read again for EXHAUSTIVENESS — printed p. 235

The judge's REQ-2026-08-21-M verdict (`35edb61a`) names
`VERIFY_EXHAUSTIVE_EVEN_SOLUTION_SET_WORDING_FOR_DLMF_30_3_5` the cheapest
decisive test, with failure codes `W13_7_SOURCE_SOLUTION_SET_NOT_EXHAUSTIVE`
and `W13_7_ONE_WAY_MEMBERSHIP_CAN_SKIP_INDICES`. Here is the wording check.

### The book's enumeration is exhaustive, and the definite article is the reason

The sentence that carries it, from the same Satz 1:

"**Die** reellen Eigenwertpaare λ, γ² liegen in der (λ, γ²)-Ebene auf regulär
analytischen charakteristischen Kurven λ(γ²), die wir mit λ = λ_n^m(γ²),
λ_n^m(0) = n(n+1) (n = m, m+1, m+2, …) festlegen können."

`Die reellen Eigenwertpaare` — the definite plural, all of them — lie on those
curves. This is not a one-way membership statement about some eigenvalues; it
says the family `{λ_n^m}` exhausts the real spectrum at every parameter. With
the parity clause "mit n − m gerade oder ungerade", at order `m = 0` the even
eigenvalues are exactly `{λ_{2j}^0(γ²) : j = 0, 1, 2, …}`, in that labelling.

Together with "sämtlich reell und einfach", the spectrum at fixed `γ²` is a set
of simple real values with a canonical enumeration, and the curves do not
intersect, so the enumeration is order-preserving in the parameter. That is
exactly what the selected representation `FIXED_G_STRICT_ORDER_ISOMORPHISM`
needs.

### The cutoff is admission only, and here is the arithmetic that proves it

Our project's characteristic iff
(`mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero`,
`D0Mode4DLMF3035EvenCharacteristicSource.lean:80`) carries the hypothesis
`Λ ≤ 20`. It is tempting to read that cutoff as isolating our three selected
even branches, since `λ_4^0(0) = 4·5 = 20`. **It does not, and the error would
be silent.**

Using the leading two terms of Satz 9, `λ_n^0(γ²) ≈ −γ² + γ(2n+1)`, at our own
precommitted parameters `γ_k = 2π(k+2)`:

```
k = 0   γ ≈ 12.57     n=0: −145   n=2: −95   n=4: −45   n=6: +5    n=8: +56
k = 1   γ ≈ 18.85     n=0: −337   n=2: −261  n=4: −186  n=6: −110  n=8: −35
k = 5   γ ≈ 43.98     n=0: −1891  n=2: −1715 n=4: −1539 n=6: −1363 n=8: −1187
```

Already at `k = 0` the sixth-degree branch sits at about `+5`, below the
cutoff; by `k = 5` the eighth-degree branch is a thousand below it. The number
of even branches under `Λ ≤ 20` grows without bound as `k` grows.

So the cutoff admits our branches but selects nothing. This is precisely why
the verdict records `source_derivative_monotonicity_role: CUTOFF_ADMISSION_ONLY`
and picks the fixed-parameter ordering rather than the cutoff as the anchor.
Anyone later tempted to isolate by the cutoff has these numbers as the
counterexample.

⚠️ The table is a leading-order estimate from Satz 9, not a proof; it is a
falsifier for the cutoff-isolation idea, not a supplier of anything.

### Index firewall, restated from the verdict

DLMF 30.3.5's split degree `s = 2(K−1)` is **not** the source degree `n`. The
verdict lists `W13_7_SPLIT_DEGREE_CONFUSED_WITH_MODE_DEGREE` as a failure code.
Our selected ordinals are `j ∈ {0,2}`, the source degrees are `n = 2j ∈ {0,4}`,
and `K` is a truncation parameter belonging to neither.

---

## DLMF §30.3 checked against the book — the exhaustiveness contract comes from the BOOK, not from DLMF

The judge's REQ-M verdict set the decisive test as the literal quantifiers of
DLMF 30.3.5, and registered a prediction at probability 0.86 that the first
failure would be "source theorem recorded only as one-way *these are
solutions*". **That prediction is confirmed.**

### What DLMF says (fetched from dlmf.nist.gov/30.3, 2026-08-21)

```
"has the solutions λ = λ_{m+2j}^m(γ²), j = 0,1,2,…"
```

`has the solutions` — one-way. No claim that these are the only solutions of
the even characteristic equation. DLMF 30.3.7 is presented as an alternative
coefficient form "we can also use", without a separate normalization contract.

⚠️ CONFIDENCE: this reading came from a fetch of the page, not from this body
reading the rendered page itself, and an absence-of-claim is weaker evidence
than a quoted claim. Treat "DLMF states no exhaustiveness" as a strong
indication, not as verified. Re-check against the rendered page before it
becomes a premise.

What DLMF does supply, and it is useful:

```
30.3.1   λ_m^m < λ_{m+1}^m < λ_{m+2}^m < ⋯          strict ordering
         λ_n^m(0) = n(n+1)                          the same branch label
         −1 < dλ_n^m/d(γ²) < 0                      the same monotonicity
         eigenvalues are analytic functions
```

but **no explicit statement of simplicity or reality** beyond what the ordering
implies.

### What the book supplies that DLMF does not

Meixner–Schäfke §3.22 Satz 1, printed p. 235, carded above, gives both of the
missing pieces in one sentence each:

```
exhaustiveness   "DIE reellen Eigenwertpaare … liegen auf … Kurven λ_n^m(γ²)"
simplicity+real  "Diese Eigenwerte sind sämtlich reell und einfach."
```

The definite plural is the exhaustiveness contract, and simplicity is what the
center-normalized receiver consumes.

### Consequence for W13.7B

The decisive test **fails on DLMF and passes on the book**. The verdict's
FAIL/AMBIGUOUS branch says to use the runner-up characterization from DLMF
30.3(i) and 30.4.1–30.4.5 plus completeness theory, explicitly warning not to
drift into project branch continuation. There may now be a cheaper third way:
source the exhaustiveness contract from Meixner–Schäfke directly, since the
book is what DLMF cites and it states plainly what DLMF only implies.

That is an adjudication, not a decision this body takes. Filed to the judge as
REQ-2026-08-21-N.

### Note on the fetched page

The fetched text carried invisible codepoints `U+2061` (function application)
and `U+2062` (invisible times). These are ordinary MathML operators in DLMF's
markup, not hidden instructions; recorded because a security guard flagged them
and the next reader should not be alarmed by the same thing.
