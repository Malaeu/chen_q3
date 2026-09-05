# Williams filter over Broughan, *Equivalents of the RH*, Vol. 3 (CUP, EMA 187, 2023)

Target object (ours): **(DOM)** `Σ_n (Λ(n)/√n) E_s(log n) + ∫ b₊E_s dt ≥ ∫ b₋E_s dt` for all compact smooth `s`, `E_s(t) = ∫
f₀(x)f₀(x+t)|s(x+t)−s(x)|²dx`, `f₀ = Φ/‖Φ‖`, `FΦ = Ξ`, `b(t)=k(t)−e^{t/2}`, `b>0 ⇔ e^t<ρ=1.3247`. Source card:
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/WALL_OBJECT_CARD_2026-09-03.md`. Filter question (Williams method): *whose
unconditional partial result is strongest, and does it transport to (DOM) as a statement about a subclass of tests `s` or about a
deformation `ν_t`?*

## TOC actually fetched
`https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/189371E437CB3DAACE9106A5D9E76161` (fetched 2026-09-05).
Vol. 3, subtitle *Further Steps towards Resolving the Riemann Hypothesis*, EMA 187, 2023. Chapters: 1 Nicolas' `π(x)<li(θ(x))`; 2
Nicolas' Number of Divisors Function; 3 An Aspect of the Zeta Function Zero Gap Estimates (pp. 88–108, page range confirmed via
Cambridge Core chapter page); 4 The Rogers–Tao Equivalence [*sic* — the authors are Brad **Rodgers** and Terence Tao]; 5 The
Dirichlet Series of Dobner; 6 An Upper Bound for the de Bruijn–Newman Constant; 7 The Pólya–Jensen Equivalence; 8 Ono et al. and
Jensen Polynomials; 9 Gonek–Bagchi Universality and Bagchi's Equivalence; 10 A Selection of Undecidable Propositions; 11
Equivalences and Decidability for Riemann's Zeta. Appendices A–O (hyperbolic polynomials, Montel/Hurwitz, Bohr, de Reyna's
expansion, propositional/predicate calculus, recursive functions, ordinal numbers).

Cards below merge chapters that share one equivalent (4+5+6; 7+8; 10+11) → 7 cards.

## CARD 1 — Nicolas' `π(x) < li(θ(x))` (ch. 1)

1. **STATEMENT.** `A(x) := li(θ(x)) − π(x) > 0` for all `x ≥ 11` ⟺ RH. `θ` = Chebyshev, `li` = log integral. Source: J.-L. Nicolas,
   *Estimates of li(θ(x)) − π(x) and the Riemann hypothesis*, Ramanujan J. (2019); open preprint
   `https://hal.science/hal-02078840/document` (title+author verified in search results; PDF blocked by Anubis at fetch time —
   statement text itself is [SEARCH-RESULT, not read in source]).
2. **STRONGEST UNCONDITIONAL PARTIAL.** Nicolas' unconditional half is an **oscillation theorem**: if RH is false, `A(x)` changes
   sign infinitely often (same shape as his 1983 primorial theorem, see Card 2). No unconditional "`A(x)>0` on a half-line" exists.
   Direction: **barely-true side** — it says the inequality has no reserve.
3. **WEIL-FORM TRANSLATION.** **NONE KNOWN.** Searched: `Nicolas equivalence pi(x)<li(theta(x)) unconditional partial`; `"Nyman-
   Beurling" criterion "Weil" explicit formula bridge positivity`; `Bombieri Lagarias Complements to Li's criterion Weil
   positivity`. The only positivity dictionaries found (Bombieri–Lagarias, *J. Number Theory* 77 (1999) 274–287; Bombieri, *Rend.
   Lincei* s.9 v.11 (2000) 183–233) run through **Li's criterion**, not through `θ`/`π` sup-norms.
4. **TRANSPORT TO (DOM).** No transport as a subclass of `s`. One *narrow* hook, and it is real: our equivalent finite form **(FM)**
   (finite margin over primes with explicit cutoff `P(v,ε)` + tail) needs effective bounds on `ψ(x)−x` for the tail. Nicolas-line
   explicit prime estimates are exactly that input. This is a **supplier for a tail term**, not a transport of the equivalence.
5. **FRESH TOOL (2019+).** Effective/explicit prime-counting estimates (Platt–Trudgian-style verified-RH-height inputs). **Sees the
   prime side directly** — the only family in Vol. 3 that does — but only through `Σ_{p≤x}` sup-norms, never through a quadratic
   form.
6. **VERDICT.** `DIFFERENT_TEST_SPACE_NO_BRIDGE` — prime-aware but sup-norm-shaped; no positive-definite bridge to `Q(f₀·s)`.
   Confidence 0.8.

## CARD 2 — Nicolas' number-of-divisors / Euler-φ equivalence (ch. 2)

1. **STATEMENT.** Two related criteria. (a) Euler-φ, Nicolas 1983: with `N_k = Π_{i≤k}p_i` (primorial), `N_k/φ(N_k) > e^γ log log
   N_k` for all `k ≥ 2` ⟺ RH. Source: J.-L. Nicolas, *Petites valeurs de la fonction d'Euler*, **J. Number Theory 17** (1983)
   375–388, `https://doi.org/10.1016/0022-314X(83)90055-0`; author's PDF `http://math.univ-lyon1.fr/~nicolas/petitsphi83.pdf`. (b)
   Divisor version (the chapter title): Ramanujan/Robin style bound on `log d(N)` at (superior) highly composite `N` against `li`
   plus a zero-sum term; Broughan's source is J.-L. Nicolas, *Highly composite numbers and the Riemann hypothesis*, **Ramanujan J.
   57** (2022) 507–550 (author PDF listed as `math.univ-lyon1.fr/~nicolas/hcnHR.pdf`, returned 404 on fetch — bibliographic data
   [SEARCH-RESULT]; exact inequality **not quoted here because I did not read it**).
2. **STRONGEST UNCONDITIONAL PARTIAL.** Nicolas 1983 proves *unconditionally*: **if RH is false the inequality holds for infinitely
   many `k` and fails for infinitely many `k`.** Direction: **barely-true side** — it is a sign-oscillation theorem, the arithmetic
   twin of Rodgers–Tao (Card 4). It forbids any margin.
3. **WEIL-FORM TRANSLATION.** **NONE KNOWN.** Same three queries as Card 1, plus `Nicolas number of divisors d(n) Riemann hypothesis
   equivalence highly composite`. Robin/Nicolas inequalities are `Σ_{p≤x}log(p/(p−1))`-shaped; no paper found writing them as
   `Q_W(v) ≥ 0` on any test class.
4. **TRANSPORT TO (DOM).** None. The object is a *sup over integers of a multiplicative function*, not a quadratic form; there is no
   `s` making `E_s` reproduce `Π_{q≤x}q/(q−1)`.
5. **FRESH TOOL (2019+).** Nothing newer than explicit-estimate bookkeeping; the 2022 Ramanujan J. paper is consolidation, not a new
   technique. Prime-aware, positivity-blind.
6. **VERDICT.** `DIRECTION_WRONG` — the only unconditional content is "no reserve on either side", which is the same news our
   `MARGIN-KILL` already delivered. Confidence 0.85.

## CARD 3 — Zeta-function zero-gap estimates (ch. 3)

1. **STATEMENT.** Chapter title and page range verified (pp. 88–108, Cambridge Core); **the chapter's actual equivalence statement
   is NOT verifiable from open sources** — no abstract is exposed, Google Books preview returned only front matter. My reading,
   marked as inference: it supplies the zero-gap / pair-correlation input consumed by ch. 4 (it sits immediately before the
   Rodgers–Tao chapter). [INFERENCE, UNVERIFIED]
2. **STRONGEST UNCONDITIONAL PARTIAL.** The pair-correlation input Rodgers–Tao actually use is Montgomery's estimate; Rodgers–Tao's
   own abstract (arXiv:1801.05914) states the contradiction is with "known results about Riemann zeta function zero distributions,
   particularly Montgomery's pair correlation estimates". Direction: constrains zero *statistics*, i.e. again the barely-true side.
3. **WEIL-FORM TRANSLATION.** **ALREADY DONE, ON OUR SHELF.** Montgomery's pair correlation *is* the explicit formula applied to a
   specific test class; our repo holds `docs/routeB_bus/litreview/MONTGOMERY_PAIR_CORRELATION_1973_USAGE_CARDS.md`.
4. **TRANSPORT TO (DOM).** Pair correlation is the `Q`-form evaluated on plane-wave-like tests — and our shelf has already killed
   **plane waves as a sufficient condition** (two-frequency kernel) in the `Убито` list.
5. **FRESH TOOL (2019+).** Nothing new visible from outside the book.
6. **VERDICT.** `ALREADY_ON_OUR_SHELF` — the usable content is the pair-correlation card we hold, and the plane-wave route it feeds
   is already killed. Confidence 0.6 (chapter content unread).

## CARD 4 — de Bruijn–Newman constant `Λ` (ch. 4 Rodgers–Tao, ch. 5 Dobner, ch. 6 Polymath15)

1. **STATEMENT.** `H_t(z) := ∫_0^∞ e^{tu²}Φ(u)cos(zu)du`, `Φ(u) := Σ_{n≥1}(2π²n⁴e^{9u} − 3πn²e^{5u})exp(−πn²e^{4u})` (verbatim from
   arXiv:1904.12438 abstract). There is a finite `Λ` with: zeros of `H_t` all real ⟺ `t ≥ Λ`. **RH ⟺ `Λ ≤ 0`.** Newman's conjecture:
   `Λ ≥ 0`.
2. **STRONGEST UNCONDITIONAL PARTIALS — two, pointing opposite ways.**
- **`Λ ≥ 0`** — B. Rodgers, T. Tao, *The de Bruijn–Newman constant is non-negative*, arXiv:1801.05914, Forum of Math. Pi 8 (2020).
   Reproof + generalisation to the extended Selberg class: A. Dobner, *A proof of Newman's conjecture for the extended Selberg
   class*, arXiv:2005.05142, Acta Arith. (2021); abstract: "any L-function in the extended Selberg class has an associated de
   Bruijn-Newman constant and … all of these constants are nonnegative", proof "requires no information about zeta function zeros".
   **Direction: barely-true.** Combined with RH this forces `Λ = 0`: RH, if true, is true with **zero margin**.
- **`Λ ≤ 0.22`** — D.H.J. Polymath, arXiv:1904.12438, *Res. Math. Sci.*: "we are able to obtain a new upper bound `Λ ≤ 0.22`
   unconditionally" (verbatim). **Direction: toward RH**, but by effective analytic estimates plus numerics — it closes 0.22 of an
   infinite-codimension gap. (Shelf note: our own survey records a [RELAY, unverified] `Λ ≤ 0.1787854` blog claim, Aug 2026, no
   arXiv id.)
3. **WEIL-FORM TRANSLATION.** **NONE KNOWN as a written dictionary.** Searched: `"de Bruijn-Newman" constant "Weil" positivity
   explicit formula quadratic form translation`; `"explicit formula" for H_t / xi_t heat flow primes von Mangoldt Weil functional
   deformation`. No paper writes a `ν_t` explicit formula for `H_t`. The structural reason is decisive: `H_t` for `t ≠ 0` has **no
   Euler product**, hence no explicit formula and **no prime atoms** — the flow deletes exactly the side our wall is about.
4. **TRANSPORT TO (DOM).** There *is* a candidate identification at `t = 0`, and it is checkable on our disk: the Polymath `Φ` is
   (up to the same rescaling our card records as "scale 4 relative to CCM (7.1)") **our `Φ`** — both are the super-exponentially
   decaying function whose cosine transform is `Ξ`, and both decay like `exp(−c·e^{2|x|})`. If so, the dBN flow is the deformation
   **`f₀ ↦ f₀,t(x) = f₀(x)e^{tx²}`** of the *ground state*, **not** a deformation `ν_t` of the measure. So the transport is: *(DOM)
   for the fixed `ν` with a Gaussian-reweighted ground state.* But `Λ ≥ 0` says the deformed problem is unsolvable for `t<0`, and
   for `t>0` there is no `ν_t` at all. Net: **no positivity is transported in the RH direction.**
5. **FRESH TOOL (2019+).** Tao's zero-dynamics / local-equilibrium method; Dobner's complex-analytic replacement for it (modified
   Dirichlet series producing off-line zeros for `t<0`); Polymath15's effective `H_t(x+iy)` bounds for small/medium `x`. Dobner's
   abstract explicitly says his method needs **no zero information** and works in the extended Selberg class — i.e. it is **blind to
   the prime atoms `Λ(n)/√n`**; it cannot decide an inequality whose whole content is atoms vs `b₋`.
6. **VERDICT.** `DIRECTION_WRONG`. The strong unconditional result (`Λ ≥ 0`) is an *independent, external confirmation of our own
   `MARGIN-KILL`/`TRADE` entries*: nothing in (DOM) can be proved with a uniform positive reserve. Value to us is negative-
   knowledge, high; transportable positivity, none. Confidence 0.85.

## CARD 5 — Pólya–Jensen hyperbolicity (ch. 7) and Ono et al. (ch. 8)

1. **STATEMENT.** Pólya 1927: RH ⟺ the Jensen polynomials `J^{d,n}_ξ(X) = Σ_{j=0}^{d} C(d,j) γ_{n+j} X^j` of the Taylor/derivative
   sequence of `ξ` at its point of symmetry are **hyperbolic** (all roots real) for **all** `d ≥ 1, n ≥ 0`. Quantifiers matter: RH
   needs all `(d,n)`.
2. **STRONGEST UNCONDITIONAL PARTIAL.** M. Griffin, K. Ono, L. Rolen, D. Zagier, *Jensen polynomials for the Riemann zeta function
   and other sequences*, arXiv:1902.07321, PNAS 116 (2019). Verbatim: "We obtain an asymptotic formula for the central derivatives
   `ζ^{(2n)}(1/2)` that is accurate to all orders, which allows us to prove the hyperbolicity of a density 1 subset of the Jensen
   polynomials of each degree. Moreover, we establish hyperbolicity for all `d ≤ 8`. These results follow from a general theorem
   which models such polynomials by Hermite polynomials." Sharpened wedge (already on our shelf): Holland, arXiv:2608.08682 —
   `n³log²(n+2) ≥ K d⁵ ⇒ J^{d,n}` hyperbolic; also Griffin–Ono–Rolen–Thorner–Tripp–Wagner, arXiv:1910.01227, Adv. Math. 397 (2022).
   **Direction: toward RH** — genuinely, this is the only card in Vol. 3 whose main unconditional theorem proves a piece of the RH
   side. **Counterweight, must be recorded:** D. W. Farmer, *Jensen polynomials are not a plausible route to proving the Riemann
   Hypothesis*, arXiv:2008.07206 — verbatim: "we find there is no justification for the suggested connection to the Riemann
   Hypothesis … Jensen polynomials, as well as a large class of related polynomials, are not useful for attacking the Riemann
   Hypothesis."
3. **WEIL-FORM TRANSLATION.** No paper found that writes Jensen hyperbolicity as `Q_W(v) ≥ 0`. Searched: `de Bruijn-Newman Weil
   positivity quadratic form`; `Nyman-Beurling Weil explicit formula bridge`; `Bombieri Lagarias Li's criterion Weil positivity`.
   **BUT** the dictionary is one line and does not need a paper: the Jensen coefficients are the **even moments of our own `f₀`**,
   `γ_n ∝ ∫ f₀(x) x^{2n} dx`, because `F f₀ = Ξ` and differentiating `Ξ` at the centre pulls down powers of `x` under the transform.
   So the Jensen object and the (DOM) object are built from the *same* raw data. [DERIVATION, verify on disk before use.]
4. **TRANSPORT TO (DOM).** The candidate subclass is explicit and **non-local**, which is exactly the class our `COUPLED` theorem
   (`6b103bd1`) does *not* kill (it kills finite stencils): **`S_poly(d) = { s : s(x) = Σ_{k=1}^{d} a_k x^k }`**, i.e. polynomial-
   modulated tests `f₀·s`. For `s ∈ S_poly(d)`, `|s(x+t)−s(x)|²` expands into finitely many monomials, so `E_s(t)` is a finite
   combination of `∫ f₀(x)f₀(x+t)x^{i}(x+t)^{j}dx`, and (DOM) becomes a **finite Hankel/Hermite-type positivity condition in the
   same moments `γ_n`** that Jensen hyperbolicity constrains. Independent evidence that we are already living in this subspace: the
   repo's own Probe 6 (commit `a18f1e02`) found the trial defect `u2 ∈ span{y, y·x², y·x⁴}` to 99.7% — i.e. `x^{2k}`-modulations of
   the `Ξ`-row, precisely `S_poly`.
5. **FRESH TOOL (2019+).** GORZ's **Hermite-asymptotic modelling** of derivative sequences (all-orders asymptotic for
   `ζ^{(2n)}(1/2)`), extended by the Holland wedge. Prime side: the asymptotic is driven by the archimedean `Γ`-factor; the prime
   sum enters only in exponentially smaller corrections. So the tool is **near-blind to the atoms `Λ(n)/√n`** and cannot by itself
   decide atoms-vs-`b₋`. This is also Farmer's objection in our language.
6. **VERDICT.** `TRANSPORTABLE_CANDIDATE` — the moment bridge is explicit, the subclass `S_poly` is genuinely non-local (so not
   covered by `COUPLED`), and our own numerics already point at it. Confidence **0.35**: the bridge transports the *statement*, but
   the fresh tool behind the unconditional result is prime-blind, so a transported theorem will most likely reproduce the
   archimedean part we already have (`d_A` bookkeeping).

## CARD 6 — Gonek–Bagchi universality / Bagchi's equivalence (ch. 9)

1. **STATEMENT.** Bagchi's equivalence: RH ⟺ **strong recurrence** of `ζ` in `D = {1/2 < Re s < 1}` — for every compact `K ⊂ D` with
   connected complement and every `ε > 0`, `liminf_{T→∞} (1/T)·meas{τ ∈ [0,T] : sup_{s∈K}|ζ(s+iτ) − ζ(s)| < ε} > 0`. Source: B.
   Bagchi, thesis (ISI Calcutta, 1981) and *Recurrence in topological dynamics and the Riemann hypothesis*, Acta Math. Hungar. 50
   (1987); survey locator: Matsumoto, *A survey on the theory of universality for zeta and L-functions*, arXiv:1407.4216. Chapter
   PDF locator: Cambridge Core `…/9781009384803c09_337-387.pdf`.
2. **STRONGEST UNCONDITIONAL PARTIAL.** Voronin universality: `ζ` approximates every non-vanishing analytic `g` on such `K` with
   positive lower density; **but the self-approximation `g = ζ|_K` is precisely the excluded case** (`ζ` has zeros off the line iff
   self-approximation fails). Direction: neither — it stops exactly at the boundary of the equivalence and has done so since 1975.
3. **WEIL-FORM TRANSLATION.** **NONE KNOWN.** Searched: `Bagchi equivalence strong recurrence universality Gonek`; `Nyman-Beurling
   Weil explicit formula bridge positivity`. Universality is a `sup`-norm/topological-dynamics statement on a strip; the Weil form
   is an `L²` hermitian form on the critical line. No bridge in the literature.
4. **TRANSPORT TO (DOM).** None. `sup`-norm density on a 2-D region has no positive-definite counterpart, and there is no `s` for
   which `E_s` reproduces a recurrence density.
5. **FRESH TOOL (2019+).** Discrete/hybrid universality equivalences (e.g. arXiv:2310.03619, arXiv:2308.07031). Blind to prime atoms
   as *quantities* (the Euler product enters only through Bohr-type almost-periodicity).
6. **VERDICT.** `DIFFERENT_TEST_SPACE_NO_BRIDGE`. Confidence 0.9.

## CARD 7 — Undecidable propositions and decidability of RH (ch. 10, 11)

1. **STATEMENT.** Not an equivalence in the analytic sense: a metamathematical placement. K. Broughan, *The Decidability of the
   Riemann Hypothesis*, arXiv:2312.11565 — verbatim abstract: "Using a result of recursive function theory and results of the
   complex analysis of Takeuti, which is based on a type theory and the work of Kreisel, and which gives a conservative extension of
   first order Peano arithmetic (PA), assuming all critical zeros of the Riemann zeta function are simple, we show that RH is
   decidable in PA."
2. **STRONGEST UNCONDITIONAL PARTIAL.** The result itself is **conditional on simplicity of the critical zeros**, which is unproved.
   Unconditionally: RH is `Π₁` (a `Π₁` arithmetical statement), so it is not independent of PA in the "true but unprovable by
   counterexample" way. Direction: neither — it constrains proof-shape, not zeros.
3. **WEIL-FORM TRANSLATION.** Not applicable; none exists and none is meaningful.
4. **TRANSPORT TO (DOM).** No transport of content. **One usable consequence for our endgame frame:** it says nothing in logic
   forbids the shape our `docs/FINITE_CERTIFICATE_PRINCIPLE.md` assumes (coercive tail + finite exact certificate) — but "decidable"
   here is not "decidable by a finite computation we can run".
5. **FRESH TOOL (2019+).** Takeuti/Kreisel conservative-extension machinery imported into analytic NT. Prime side: irrelevant to it.
6. **VERDICT.** `DIFFERENT_TEST_SPACE_NO_BRIDGE`. Confidence 0.9.

## Shelf cross-check (done before writing)

`rg` over the repo: de Bruijn–Newman and Jensen/GORZ are **already surveyed** in
`docs/routeB_bus/litreview/SURVEY_WALLS_A_B_DELTA_2026-09-03{,_APPENDIX_NEW}.md` (Holland arXiv:2608.08682, Michalowski
arXiv:2602.20313 "kernel not PF₅", Polymath `Λ ≤ 0.22`), Bombieri/Li's criterion in `WEIL_POSITIVITY_OBJECT_CARD_2026-09-04.md`,
Montgomery in `MONTGOMERY_PAIR_CORRELATION_1973_USAGE_CARDS.md`. **Nicolas appears once (CHAT_DIGESTS only, as the request that
produced this report); Bagchi/universality and decidability appear nowhere.** So cards 1, 2, 6, 7 are new to the shelf — and all
four come back negative.

## Summary (5 lines)

1. **Exactly one TRANSPORTABLE_CANDIDATE: Pólya–Jensen / Griffin–Ono–Rolen–Zagier (Cards 5, ch. 7–8).** The bridge is that the
   Jensen coefficients `γ_n` are the even moments `∫f₀ x^{2n}` of *our own* `f₀`, so (DOM) restricted to the non-local subclass
   `S_poly(d) = {s = Σ_{k≤d} a_k x^k}` is a finite positivity condition in the same moments.
2. **First cheap probe for it (minutes, existing cache):** expand `E_s` for `s = x` and `s = x²` in closed form, evaluate `Q(f₀·s)`
   against the already-computed `Ξ`-row moments, and check whether the Jensen/Hermite wedge `n³log²(n+2) ≥ K d⁵` maps onto any
   `(d)`-range where our prime atoms `0.037599` beat `N₋ = 0.083642` — i.e. whether polynomial modulation ever moves the 2.2×
   deficit. Pre-register the number before running.
3. **Second, even cheaper probe (30 s, prerequisite):** verify on disk that our `Φ` *is* the Polymath/dBN `Φ` up to the recorded
   scale — if yes, the dBN flow is exactly `f₀ ↦ f₀e^{tx²}`, which types the whole ch. 4–6 block as a ground-state deformation with
   **no** `ν_t`, and closes it permanently instead of re-opening it each survey.
4. **Everything else is negative and that is the useful yield:** Rodgers–Tao `Λ ≥ 0` and Nicolas' 1983 oscillation theorem are two
   independent external confirmations that RH has **zero margin** — our `MARGIN-KILL`/`TRADE` entries are not an artefact of our
   construction. Bagchi and the decidability chapters have no bridge at all.
5. **Prime-blindness is the discriminator:** of the seven cards, only Nicolas (1–2) sees `Λ(n)/√n`, and it sees it as a sup-norm,
   not a form. No fresh 2019+ tool in Vol. 3 sees the prime atoms *inside a quadratic form* — which is why no equivalent in this
   book can decide atoms-vs-`b₋` on its own.
