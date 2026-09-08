# Local-at-a-zero invariants of ξ/ζ — literature map and gap

Date 2026-09-08. Web-enabled literature pass. Scope: quantities attached to ONE zero ρ.
Requirements tested: **(1)** local at an individual ρ · **(2)** independent prime-side
(Euler product / von Mangoldt) representation, not through the zeros and not through
analytic continuation of ζ'/ζ into the strip · **(3)** exact flip at Re ρ = 1/2.

Verification legend: `[V]` = verified here (own derivation and/or own computation);
`[L]` = read in the source; `[A]` = abstract only, NOT verified; `[?]` = unverified relay.

---

## 0. Two facts established here, not relayed

**F1 (functional-equation symmetries of the log-jet).** For simple ρ set
`c₀(ρ) = lim_{s→ρ}[ξ'/ξ(s) − 1/(s−ρ)] = ξ''(ρ)/(2ξ'(ρ))`. From ξ(s)=ξ(1−s) one gets
ξ'/ξ(1−s) = −ξ'/ξ(s), hence **c₀(1−ρ) = −c₀(ρ)**; from ξ(s̄)=conj ξ(s), **c₀(ρ̄)=conj c₀(ρ)**.
On the line 1−ρ = ρ̄, so conj c₀ = −c₀, i.e. **Re c₀(ρ) = 0 for every on-line zero,
unconditionally**. `[V]` derived; `[V]` computed: for ρ₁ = 1/2 + i·14.1347…,
ξ''/2ξ' = −5.6e−47 + 0.579630577477882 i (mpmath, dps=30, derivatives of ξ only — a channel
that never touches the Hadamard sum). Second channel, symmetric sum Σ'_{|γ'|≤541} 1/(ρ₁−ρ')
over 600 zeros = 0.0 + 0.534404 i; the analytic tail estimate 2γ₁∫_T^∞ (log(γ/2π)/2π)γ^{−2}dγ
≈ 0.037 closes the 0.045 gap to the required precision. Files:
`/home/chirurgie/.claude/jobs/4b35770d/tmp/vortexlit/chk.py`.

**F2 (extremal off-line zero).** With symmetric (principal-value) Hadamard summation,
c₀(ρ) = Σ'_{ρ'≠ρ} 1/(ρ−ρ'), and Re 1/(ρ−ρ') = (β−β')/|ρ−ρ'|². If β = Re ρ is **maximal**
over the zero set, every term is ≥ 0, and > 0 for every on-line ρ' — the real-part series
converges absolutely (Σ|γ−γ'|^{−2} < ∞ at density ~log T). Hence **Re c₀(ρ_max) > 0
strictly**. `[V]` derived. This is the pointwise shadow of Hinkkanen/Lagarias
(§2, row Log-jet) but I found **no published statement of it at the zero itself**.

---

## 1. Table of local-at-a-zero quantities

Symmetry columns: behaviour under J: ρ↦1−ρ and C: ρ↦ρ̄. Off-line orbit = quartet
{ρ,1−ρ,ρ̄,1−ρ̄}; on-line orbit = pair {ρ,ρ̄} (J and C coincide) — this collapse is the
source of every flip below.

| # | Quantity | Definition | Locator | J | C | Prime side? | Exact flip? |
|---|---|---|---|---|---|---|---|
| **JET** |
| 1 | ζ'(ρ) | derivative at simple zero | Gonek–Hejhal J_{−k}(T)=Σ\|ζ'(ρ)\|^{−2k} ~ T(log T)^{(k−1)²}; [2310.03949 §1] `[A]`, lower bounds [2208.06922], [2106.03057] | ξ'(1−ρ)=−ξ'(ρ) `[V]` | ξ'(ρ̄)=conj `[V]` | **NO** — Dirichlet series for ζ' converges only Re s>1; Riemann–Siegel gives a finite *integer* sum, asymptotic and not an Euler product | **NO** — \|ξ'\| positive on and off the line |
| 2 | ξ^{(k)}(ρ), ζ^{(k)}(ρ) | higher jets | Stopple [1508.05870 §5, eq. before (12)]: ξ'=η, ξ''-relations `[L]` | k-parity sign | conj | NO (same reason) | NO — not normalisation-invariant; only ratios are |
| **LOG-JET** |
| 3 | **c₀(ρ) = ξ''(ρ)/2ξ'(ρ)** = ½Pξ(ρ) = Σ'1/(ρ−ρ') | regular part of ξ'/ξ at ρ | Stopple [1508.05870] **Lemma (6)**: `Pf(w)=2q'(w)/q(w)`; **Thm 2 proof**: "*Since Pξ is purely imaginary on the critical line*" `[L]` | **odd**: c₀(1−ρ)=−c₀(ρ) `[V]` | conj `[V]` | **NO** — ξ'/ξ = ζ'/ζ + h'/h inside the strip; the prime series −ΣΛ(n)n^{−s} needs continuation, i.e. exactly the excluded route | **YES (partial)** — Re c₀=0 on-line unconditionally `[V]`; Re c₀(ρ_max)>0 for the extremal off-line zero `[V]`. Non-extremal off-line zeros: **open** |
| 4 | Re(ξ'/ξ)(s) on the half-plane | not at a zero — nearby | RH ⟺ Re(ξ'/ξ)(s)>0 for Re s>1/2: **Hinkkanen**, *Complex Var. Theory Appl.* 34 (1997) 119–139; **Lagarias**, *Acta Arith.* 89 (1999) 217–234 `[?]` (both relayed via [2201.08599], [2509.18963]) | odd | conj | NO | YES but **not local** (open half-plane) |
| 5 | explicit bounds on Re Σ_ρ 1/(s−ρ) near the line | Goldštein–Grigutis [2201.08599]; Grigutis–Turčinskas [2509.18963] **Thm 6**: `0 < (0.28−ε(t))c/(σ−1/2) < Re Σ 1/(s−ρ)`, t > 3.11·10¹⁰ `[A]` | — | — | NO (their §: "no prime-related representation") | region statement, not pointwise |
| **PROJECTIVE** |
| 6 | Pξ(ρ) = ξ''/ξ' (pre-Schwarzian) | = 2c₀ — **duplicate of #3** | Stopple [1508.05870 §4] `[L]` | odd | conj | NO | YES (= #3) |
| 7 | **c₁(ρ) = −Σ'1/(ρ−ρ')²**, i.e. Pξ'(ρ) = −PΞ'(γ) | 2nd log-jet | Stopple **Thm 2, eq. (11)**: `−PΞ'(γ)=Re[(η'/η)'(ρ)] + Re[(h'/h)'... ]`; "*−PΞ'(γ)=Pξ'(ρ) is real*" `[L]` | **even**: c₁(1−ρ)=c₁(ρ) `[V]` | conj `[V]` | NO | **YES (reality flip)** — Im c₁(ρ)=0 for every on-line zero unconditionally `[V]`; Im c₁ ≠ 0 off-line only *generically*, **unproven** |
| 8 | Schwarzian S_ξ = Pξ' − ½(Pξ)² | third-order | Stopple eq. (7),(8): `¼(Pf'+(Pf)²)(w)=3(q'/q)'(w)` `[L]` | even | conj | NO | same class as #7 |
| **INTERACTION** |
| 9 | Lehmer pair | Δ²·(…)<… on consecutive γ± | Csordas–Smith–Varga, *Constr. Approx.* 10 (1994) 107–129 `[?]` | pairwise | — | NO | NO — a gap statistic; RH assumed throughout |
| 10 | **strong Lehmer pair** | `Δ²(−PΞ'(γ₊) − PΞ'(γ₋)) < 42/5`, eq. (9) | Stopple [1508.05870] **Def. §4, Thm 1** `[L]`; Thm 3 eq. (17) rewrites it as `−Re Σ_{ρ'} 1/(ρ₊−ρ')² + Im Σ 1/(ρ₊−ρ') + …` over zeros ρ' of **ζ'** | — | — | NO | NO (RH assumed); it feeds Λ ≥ 0, not on/off-line |
| 11 | zeros ρ' of ζ' near ρ | horizontal distribution | **Speiser**, *Math. Ann.* 110 (1934) 514–521: RH ⟺ ζ' has no zeros in 0<σ<1/2 `[?]`; **Levinson–Montgomery**, *Acta Math.* 133 (1974) 49–65: N₁⁻(T)=N⁻(T)+O(log T) `[?]`; bimodal horizontal density Dueñez–Farmer–Froehlich–Hughes–Mezzadri–Phan, *Nonlinearity* 23 (2010) 2599 `[A]` | — | — | NO | **YES but global** — Speiser is a statement about the whole region, not attached to one ρ |
| **DYNAMICS** |
| 12 | **dBN flow velocity of a zero** | `∂_t x_k(t) = 2 Σ'_{j≠k} 1/(x_k−x_j)` | **Rodgers–Tao [1801.05914] Thm 4.1, eq. (56)** (principal-value summation) `[L]` | — | — | NO | NO |
| 13 | Λ (de Bruijn–Newman) | global constant | Rodgers–Tao [1801.05914]: Λ ≥ 0 `[L]`; RH ⟺ Λ ≤ 0 (Newman) | — | — | NO | family-level |
| **ARITHMETIC DUAL** |
| 14 | Weil / Guinand explicit formula | Σ_ρ ĥ(ρ) = arch + Σ_p Σ_k Λ(p^k)… | classical; family-level bridge | quartet | conj | **YES** | Weil positivity ⟺ RH — but **for all test functions**, never one ρ |
| 15 | Li / Keiper λ_n | λ_n = Σ_ρ[1−(1−1/ρ)^n] = (1/(n−1)!) dⁿ/dsⁿ[s^{n−1}log ξ(s)]\|_{s=1} | Li, *JNT* 65 (1997) 325–333; **Bombieri–Lagarias**, *JNT* 77 (1999) 274–287 (arithmetic formula for λ_n via Guinand–Weil; general-multiset Thm) `[?]`; Coffey, *Proc. R. Soc. A* 464 (2008) 711–731 `[A]`; Coffey [math-ph/0505052] `[A]` | quartet | conj | **YES** (arith + arch split) | **family-level only**: λ_n ≥ 0 **for all n** ⟺ RH; no single n decides |
| 16 | Voros superzeta | `Z(s\|t)=Σ_ρ(½+t−ρ)^{−s}` (16); `𝒵(σ\|t)=Σ_k(τ_k²+t²)^{−σ}` (17); `𝔷(s\|τ)=Σ_k(τ_k+τ)^{−s}` (18) | Voros [1403.4558] eqs. (15)–(19), Tables 2–6 `[L]`; monograph *Zeta Functions over the Riemann Zeros*, Springer LNM 1995 (2010) | symmetric by construction | — | **YES** via (15)/Keiper–Li integral rep. | RH ⟺ all τ_k real (15); criterion is **large-order asymptotics of Keiper–Li**, family-level |
| 17 | Jensen polynomials J^{d,n}_ξ | hyperbolicity | Pólya; Csordas–Norfolk–Varga, *TAMS* 296 (1986) 521–541 (Turán inequalities, Pólya's 58-year problem) `[?]`; Griffin–Ono–Rolen–Zagier, *PNAS* 116 (2019) 11103, [1902.07321] (all d≤8; all d for large n) `[A]`; **Farmer** [2008.07206] *Jensen polynomials are not a plausible route to proving RH*, *Adv. Math.* (2022) `[A]` | Taylor coeffs at 1/2 | real | **YES** (coeffs of ξ ← Mellin of θ, not primes directly) | **family-level**; Farmer: differentiation destroys the structure that would decide |
| 18 | Laguerre inequalities L_n(ξ) | `f'²−ff'' ≥ 0` and iterates | Csordas–Norfolk–Varga (as above); Dimitrov–Lucas (order-2 Turán unconditional) `[?]` | — | — | via Taylor coeffs | family-level |

---

## 2. Duplicates under the functional equation

Three literatures describe **the same object**:

```
c₀(ρ)  =  ½ · Pξ(ρ)  =  (1/2i) · ∂_t x_k |_{dBN flow}
log-jet     Stopple's pre-Schwarzian     Rodgers–Tao eq. (56)
```
`[V]` (the last step: ρ = ½+ix, Σ'1/(ρ−ρ') = −i Σ'1/(x−x'), so ∂_t x_k = 2i c₀(ρ_k);
c₀ purely imaginary on-line ⇒ the velocity is real, consistent).
Consequence: **the "velocity of a zero" under the de Bruijn–Newman flow IS the log-jet.**
Neither literature cites the other for this identification (`[V]` — no citation found either way).

Second duplication: #6 = #3 (Pξ = 2c₀); #7 = #8 up to (Pξ)²; #12 = #3.
Third: Voros's 2nd-kind 𝒵(σ|t) (17) is the prompt's Z(σ,v) with v = t².

---

## 3. Verdict on the three-requirement intersection

**(1)+(3) — local AND senses Re ρ − 1/2: YES, exactly one family — the log-jet.**
- Re c₀(ρ) = 0 on-line unconditionally `[V]`; > 0 at the extremal off-line zero `[V]`.
- Im c₁(ρ) = 0 on-line unconditionally `[V]`; off-line non-vanishing unproven.
- Published surrogates: Stopple's one-line remark inside the proof of Thm 2 [1508.05870]
  (the closest published form of note (a) part 1); Hinkkanen 1997 / Lagarias 1999
  (half-plane, not pointwise); Speiser 1934 + Levinson–Montgomery 1974 (region, not pointwise).
- **This IS the Speiser/Levinson–Montgomery mechanism in pointwise form** — Speiser's ζ'
  zeros are exactly where ξ'/ξ can lose its sign; but no source states the extremal-zero
  argument F2. Mark it as our own.

**(1)+(2) — local AND independent prime side: NONE found.**
Every prime-side handle on ζ inside the strip in the literature goes through (i) analytic
continuation of ζ'/ζ, (ii) the explicit formula (a pairing with a test function, summed
over ALL zeros), or (iii) an approximate functional equation / Riemann–Siegel finite sum
over integers, which is an asymptotic, not an identity. None is local at a single ρ.
Closest candidate, and it is the whole story of the gap: **Moriya, arXiv:2607.04316**
(*A Gaussian–Perron Prime-Side Defect and Local Profiles Near Critical-Line Zeros*,
v2, 8 Jul 2026) `[A]` — defines a smoothed **prime-side logarithmic force**, compares it
with ζ'/ζ, and proves the defect near each fixed simple critical-line zero has a
"selected-zero profile" with exponentially small nonlocal remainder. **But**: it *assumes*
RH, its comparison object is ζ'/ζ itself (continuation into the strip — requirement (2)
fails), and it is a profile theorem, not a criterion. Single-author, unrefereed preprint,
abstract-only reading here — **UNVERIFIED**.

**(2)+(3) — prime side AND senses the line: YES, family-level only.**
Weil/Guinand positivity (#14), Li–Keiper λ_n with Bombieri–Lagarias's arithmetic formula
(#15), Voros's Keiper–Li asymptotic criterion (#16), Jensen/Turán/Laguerre (#17–18).
All are sums over the whole zero set; none survives restriction to one ρ.

**All three (1)+(2)+(3): NONE.** No published quantity satisfies the intersection.

---

## 4. Closest published "local passport of a zero", and the first gap

**Closest: Stopple, arXiv:1508.05870, §5, Theorems 2 and 3.** It is a genuine data-sheet
of an individual zero ρ = ½+iγ: eq. (11) writes −PΞ'(γ) through η'/η and h'/h at ρ (i.e.
through ζ'(ρ) and the archimedean factor), and eq. (17) re-expresses it as
`−Re Σ 1/(ρ₊−ρ')² + Im Σ 1/(ρ₊−ρ') + ½log(γ''/2π) + O(…)` over **neighbouring zeros ρ' of ζ'**.
Two chapters of a passport — the jet and the neighbourhood — in one place, with error terms.

**First gap: the passport has no arithmetic page.** Nothing in it, and nothing found in the
whole survey, gives the value at one ρ a second, independent evaluation from primes.
The prime side enters the subject only as a *pairing against a test function summed over
all zeros* (Weil/Guinand). A functional whose value at a single ρ has both a zero-free
prime expression and a zero-side expression does not appear in the literature.
Requirement (2) at a single zero is, as far as this survey reaches, **untouched**.

---

## 5. The two observer notes, checked

**(a) — CONFIRMED, and partly novel.** The symmetries c₀(1−ρ)=−c₀(ρ), c₀(ρ̄)=conj c₀(ρ)
and Re c₀ = 0 on-line: derived here from the functional equation `[V]` and confirmed
numerically to 47 digits `[V]`. Closest published statement: Stopple [1508.05870],
proof of Theorem 2 — "*Since Pξ is purely imaginary on the critical line*" — for the whole
line, from which the value at a zero follows; he does not use it as a detector.
The extremal-zero strict positivity Re c₀(ρ_max) > 0 (F2): **no published locator found**.
It is the pointwise form of Hinkkanen 1997 / Lagarias 1999 (RH ⟺ Re ξ'/ξ > 0 on Re s > 1/2),
which is the modern packaging of the Speiser / Levinson–Montgomery mechanism.
So: yes, it is that mechanism — but the pointwise-at-the-zero statement is ours.

**(b) — arithmetic CONFIRMED, no published no-go found.** For entire f with f(1−s)=f(s)
and f(s̄)=conj f(s), the off-line quartet contributes 4 Re f(ρ) and the on-line pair
2 Re f(ρ): real and real-analytic in β = Re ρ, so no pointwise flip `[V]`. I found **no
paper stating this as a no-go**. The nearest published things:
- Bombieri–Lagarias [JNT 77 (1999) 274–287] Theorem 1 — Li positivity is a property of an
  arbitrary multiset closed under conjugation, hence carries no zeta-specific pointwise
  content; positivity of the *whole sequence* is what is equivalent to RH `[?]` (read via
  Sekatskii [1304.7895] Thm 2, "Generalized Bombieri–Lagarias theorem", not the original).
- Farmer [2008.07206] — the analogous "the structure that would decide is destroyed"
  message for Jensen polynomials `[A]`.
- arXiv:2606.24924 (Jun 2026) claims a *local obstruction*: "every zero produces opposite
  vertical curvatures on the two horizontal sides of the pole", so a naive pointwise
  concavity criterion cannot work `[A]` — same flavour, non-mainstream preprint, UNVERIFIED.

---

## 6. Not found / explicitly negative results of the search

- **«A Didactic Coefficientwise Prime–Zero Dictionary for log ζ» (2026): DOES NOT EXIST
  on arXiv.** arXiv API: `all:"prime-zero dictionary"` → 0 results; `abs:"didactic" AND
  abs:"zeta"` → 0 results; `all:"coefficientwise" AND all:"prime" AND all:"zeta"` → 0
  results `[V]`. Nearest real 2026 items: [2604.14596] Li, *Prime–Zero Duality* (fractal /
  RG-flow, speculative) `[A]`; [2607.02828] Groskin, *A finite Guinand–Weil dictionary and
  archimedean tail order for the truncated Weil quadratic form* (Connes–van Suijlekom
  truncation; "every value of the truncated form is an exact sum over the zeros"; 512 zeros
  verified; explicitly makes no RH claim) `[A]` — **already on the shelf**, full card at
  `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/GROSKIN_TAILORDER_USAGE_CARDS.md`
  (read 2026-08-07/27); no new triage needed; [2603.21535] prime zeta series about s=1 `[A]`.
- No published extremal-zero positivity statement for Re c₀ (F2).
- No published identification "dBN flow velocity = log-jet = ½ pre-Schwarzian".

Search hygiene note: arXiv HTML titles returned U+2062 (invisible times) inside `ζ′(ρ)` —
a LaTeX-to-Unicode artefact, not an injection; stripped, no content lost.

---

## 7. Sources

Stopple, *Lehmer pairs revisited*, arXiv:1508.05870, *Exp. Math.* 26 (2017) 1 ·
Rodgers–Tao, *The de Bruijn–Newman constant is non-negative*, arXiv:1801.05914 ·
Voros, arXiv:1403.4558 and *Zeta Functions over the Riemann Zeros*, Springer LNM 1995 ·
Bombieri–Lagarias, *JNT* 77 (1999) 274–287 · Li, *JNT* 65 (1997) 325–333 ·
Sekatskii, arXiv:1304.7895 · Coffey, *Proc. R. Soc. A* 464 (2008) 711–731; math-ph/0505052 ·
Csordas–Norfolk–Varga, *TAMS* 296 (1986) 521–541 · Csordas–Smith–Varga, *Constr. Approx.*
10 (1994) 107–129 · Griffin–Ono–Rolen–Zagier, *PNAS* 116 (2019) 11103, arXiv:1902.07321 ·
Farmer, arXiv:2008.07206 · Speiser, *Math. Ann.* 110 (1934) 514–521 · Levinson–Montgomery,
*Acta Math.* 133 (1974) 49–65 · Hinkkanen, *Complex Var.* 34 (1997) 119–139 · Lagarias,
*Acta Arith.* 89 (1999) 217–234 · Goldštein–Grigutis, arXiv:2201.08599 ·
Grigutis–Turčinskas, arXiv:2509.18963 · Dueñez et al., *Nonlinearity* 23 (2010) 2599 ·
Bui–Florea et al., arXiv:2310.03949, 2208.06922, 2106.03057 · Moriya, arXiv:2607.04316 ·
Groskin, arXiv:2607.02828 · Li Z., arXiv:2604.14596 · arXiv:2606.24924.
