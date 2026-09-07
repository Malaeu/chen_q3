# Euler–Gram evaluator of k₂ and the sign of the FULL margin on the plus channel — 2026-09-07

`DIAGNOSTIC_NEVER_A_PROOF`. Float (IEEE double) Galerkin with a residual sandwich, not ball
arithmetic. Scripts `docs/routeB_bus/phase5_codex/euler_gram/`, scratch `~/.claude/jobs/4b35770d/tmp/euler_gram/`.

## 0. Verdict

**𝔪(v₊,T) is NEGATIVE** on the symmetric two-lobe channel, for every T tested:

| T | 𝔪(v₊,T) ≤ (one-sided) | full residual sandwich | old J8 table | Q_sc = −∫\|v̂₊\|²ℓ₂ | 𝔪 − Q_sc ≥ |
|---|---|---|---|---|---|
| 60 | **−0.01008** | [−0.01199, −0.01003] | −0.03082 | −0.08211 | +0.0701 |
| 120 | **−0.00806** | [−0.00999, −0.00801] | −0.02546 | −0.05907 | +0.0491 |
| 240 | **−0.00528** | [−0.00725, −0.00523] | −0.01918 | −0.03583 | +0.0286 |
| 340 | **−0.00397** | [−0.00601, −0.00391] | −0.01616 | −0.02613 | +0.0201 |

Both columns are strictly negative; the sandwich is ≈ 2·10⁻³ wide. The **sign is already decided
by the one-sided column**, which needs only the Galerkin **lower** bound k₂ ≥ k₂ˡᵒ: since
𝔪(v) = (1/2π)∫\|v̂\|²q₂ − ∫\|v̂\|²k₂ with the first term in closed form, any lower bound on k₂
gives an upper bound on 𝔪. That column moved by ≤ 3·10⁻⁴ across four independent parameter
settings, i.e. the margin is 13–33 σ from zero. The old evaluator's plus-channel numbers were
**too negative by a factor 2–4**; its drift toward zero in J was real, its limit is not zero.
`PROFILES_ADDENDUM_INSTRUMENT_2026-09-07`'s "UNRESOLVED (instrument-limited)" is now resolved:
**negative, decaying in T a little slower than 1/T** (T·|𝔪| = 0.60, 0.97, 1.27, 1.35).

Cross-checks that must hold and do: k₂ ≥ 0 everywhere; the HS square 𝔪 − Q_sc ≥ 0 on the plus
channel; 𝔪(v₋,T) ≥ 𝓕(h_T) on the minus channel; minus-channel margins reproduce the old ones.

## 1. What the instrument is

SCALARFLOOR §4 Thm 3 (18)/(21)–(22) is used **after transporting it into the Mellin variable**,
where the semilocal angle inverse never appears and no basis of the Sonin space in physical
coordinates is ever built.

* `P` = cutoff to (0,1), `P' = I−P`, `F = F_∞` (kernel 2cos(2πuv)), `A = PFP`, `Z = (I−A²)⁻¹`,
  `T = PFP'`. Then `TT* = P − A²`, so the archimedean Sonin projector is **explicit**:
  `S_∞ = P' − T* Z T`  (ℋ₀ = ker P ∩ ker Q_∞ = (ran P + ran Q_∞)^⊥, ‖A‖ = α_∞ = 0.9999713763 < 1).
* `ℱ` (Mellin) carries ℋ₀ isometrically onto a subspace ℋ ⊂ L²(ℝ,dξ) with **bounded point
  evaluation**: `w_ξ = S_∞ f_ξ`, `⟨w_ξ,y⟩ = ℱy(ξ)`, `K(ξ,η) = ⟨w_η,w_ξ⟩`, `K(ξ,ξ) = k_∞(ξ)`.
* `U_a` becomes multiplication by `e^{−iaξ}`, hence `B = I − rU_a` becomes multiplication by
  `b(ξ) = 1 − r e^{−iaξ}` and `G = P_ℋ M_{|b|²} P_ℋ`, with `g₀ = (1−r)² ≤ G ≤ (1+r)² = g₁`
  automatically. (18) is then a **one-dimensional variational problem**:

```
  k₂(ξ₀) / |b(ξ₀)|²  =  sup_{y ∈ ℋ} [ 2 Re y(ξ₀) − ∫ |b(ξ)|² |y(ξ)|² dξ ].
```

### 1.1 The archimedean supplier: an off-diagonal kernel (new here)

Expanding `⟨f_η, S_∞ f_ξ⟩` with the regularised Mellin pieces gives, with ϑ = Riemann–Siegel
theta, γ = e^{2iϑ}, Δ = ϑ(ξ)−ϑ(η), φ_n/λ_n the prolate eigenpairs of A, m_n(ξ) = ⟨φ_n, Pf_ξ⟩,
I(ξ) = ∫₀¹ v^{−1/2+iξ}cos 2πv dv:

```
 K(ξ,η) = e^{iΔ} sin Δ / (π(ξ−η))  −  γ_ξ γ̄_η conj(Q)  −  Q  +  γ̄_η R  +  γ_ξ conj(R)
 Q(η,ξ) = Σ_n [λ_n²/(1−λ_n²)] conj(m_n(η)) m_n(ξ)          (= ⟨u_η, Z u_ξ⟩)
 R(ξ,η) = (1/π)[I(ξ)−I(η)]/(i(η−ξ)) + Σ_n [λ_n³/(1−λ_n²)] m_n(η) m_n(ξ)
```

Its diagonal is exactly `q_∞/2π + d_∞`, i.e. the `mellin_d2` evaluator: the Cauchy term alone
gives ϑ′(ξ)/π = q_∞/2π, the prolate sum gives d_∞. Since `c_n(ξ) = λ_n m_n(ξ)` and λ_n² decays
super-geometrically (0.99994, 0.95939, 0.27467, 3.5·10⁻³, 7.5·10⁻⁶, …), **ten prolate modes
suffice**; with the closed-form Legendre Mellin moments the kernel costs ~10 flops per entry.
By-product: the Sonin phase is ϑ₁ = ϑ_RS + π∫₀^ξ d_∞ with ϑ₁ − ϑ_RS = O(23/ξ), and k_∞ ≡ 0 for
|ξ| ≲ 5 — so ℋ is **not** a bare model space K_Θ (an inner function has ϑ′ > 0 strictly): a
non-unimodular isometric multiplier is present, and the phase alone does not fix the kernel.

### 1.2 Galerkin and the sandwich

Trial space = span of the reproducing kernels `E_j(ξ) = K(ξ_j,ξ)` at nodes placed at the local
Nyquist rate of the space, spacing 1/(`over`·k_∞(ξ)):

```
 Γ_{jl} = ⟨E_j,E_l⟩ = K(ξ_l,ξ_j)                          EXACT — the projector identity
 X_{jl} = ∫ 2cos(aξ) conj(E_j) E_l dξ                      quadrature (uniform, step h, |ξ|≤U)
 G      = (1+r²) Γ − r X ,     p_j = K(ξ₀,ξ_j)
 k₂ ≥ |b(ξ₀)|² · pᴴ G⁻¹ p           (LOWER, monotone in the trial span)
```

Using Γ exactly is what makes the quadrature cheap: the non-oscillatory part of the integrand
decays only like 1/ξ² (tail 1/(π²U)) while the `2cos(aξ)`-weighted part converges two orders
faster (X moves by 1.1·10⁻⁶ between U = 800 and 1600). Γ is orthonormalised by eigen-truncation
at 10⁻⁹.

Upper bound = the full-residual form (21)–(22) with `y = G⁻¹w` the Galerkin optimum,
`ψ = 2cos(aξ)y`:

```
 ‖Gy‖² = (1+r²)²‖y‖² − 2(1+r²)r Re⟨y,ψ⟩ + r²‖Pψ‖² ,  ‖z‖² = k_∞ − 2Re⟨w,Gy⟩ + ‖Gy‖²
 k₂ ≤ |b|² ( E(y) + ‖z‖²/g₀ )
```

`‖Pψ‖²` is **not** approximated by (FGF)²: it is computed EXACTLY through the orthogonal
complement. Because ℋ₀ = (ran P + ran Q_∞)^⊥ and the Riesz Gram of `{Ee_k} ∪ {FEe_k}` is
`[[I,A],[A,I]]` with inverse `[[Z,−ZA],[−AZ,Z]]`,

```
 ‖S_∞v‖² = ‖v‖² − ( ⟨m_a,Z m_a⟩ + ⟨m_b,Z m_b⟩ − 2Re⟨m_a, Z A m_b⟩ ),  m_a = Pv, m_b = PFv.
```

For ψ = (U_a+U_{−a})y with y ∈ ℋ₀ the U_a lobe lands in (2,∞) and contributes nothing, so
`m_a(u) = √2 y(2u)`, `m_b(u) = √2 (Fy)(2u)` on (1/2,1) only; F ℋ₀ = ℋ₀ with
`F w_ξ = γ(ξ) conj(w_ξ)`, so no second construction is needed and the physical reproducing
vectors on (1,2) come from the same spectral data (`pperp.wphys`). A composite Nyström grid with
the break at u = 1/2 keeps the jump of m_a, m_b at a panel boundary; it reproduces α_∞ = 0.9999713763.

## 2. Validation

| # | test | result |
|---|---|---|
| V1 | diagonal K(ξ,ξ) vs `mellin_d2/d_inf.npz` | ≤ 3·10⁻⁹ for ξ ≤ 5, ≤ 1·10⁻¹⁰ for ξ ≥ 16, 6·10⁻¹³ at 600 |
| V2 | two independent discretisations of K off-diagonal (800-pt Nyström + 22 507-pt dyadic Mellin grid vs 10 prolate modes + closed-form Legendre moments) | 1·10⁻¹⁴ on 10 test pairs incl. near-diagonal δ = 0.005 |
| V3 | projector identity ∫K(ξ,η)K(η,ξ′)dη = K(ξ,ξ′) | residual 4.4·10⁻⁴ (U=300), 1.4·10⁻⁴ (U=800) = the analytic tail 1/(π²U) = 1.27·10⁻⁴ |
| V4 | k₂ ≥ 0 required (true density) | min k₂ˡᵒ = +1.8·10⁻¹⁰ at ξ=0, positive on all 2801 grid points |
| V5 | (19) `\|b\|²k_∞/g₁ ≤ k₂ ≤ \|b\|²k_∞/g₀` | holds on both sides at every grid point |
| V6 | first cosine coefficient of k₂ − k_∞ over whole periods 2π/a; exact target −ar/π = −0.156013 | −0.15199 (27 per.), −0.15358 (60), −0.15416 (55), −0.15455 (44); sine coeff ≤ 7·10⁻⁵. Old J8 on the same windows: −0.1479 … −0.1521 — **the new evaluator is closer to the analytic target on every window** |
| V7 | ∫₀^X d₂ → 0 (Tr D₂ = 0) | lower branch +0.1212 (100), +0.0578 (200), +0.0079 (400), −0.0047 (600), −0.0127 (700); cf. d_∞: 7.32/X |
| V7b | ‖Pψ‖² exact (complement) vs its independent Galerkin lower bound | exact ≥ Galerkin at every point, median relative excess 5.7·10⁻⁵ |
| V8 | completeness ‖P_S w_ξ‖²/k_∞ | 1 − ratio ≤ 2.9·10⁻⁶ on [16,600] |
| V9 | convergence of k₂ˡᵒ over 4 settings (nodes 2117…3599, ranges ±900…±1700, U 1200…2200, h 0.04/0.05, over 1.5/2.0) | spread 2·10⁻⁵ … 7·10⁻⁵ in k₂, monotone in the trial span |
| V10 | minus channel reproduces the converged old margins | see §3 |

## 3. Margins

`h_T = (∂²−¼)(e^{iTx}η₄)`, η₄(x) = (1−(x/δ)²)⁴ on |x|<δ, δ = (log3−log2)/8; the folded weights
`(1∓cos aξ)(|ĥ_T(ξ)|²+|ĥ_T(−ξ)|²)/H` carry 1 − 8·10⁻⁷ of their exact mass 2π on ξ ∈ [0,700].

| T | chan | (1/2π)∫W q₂ | ∫W k₂ˡᵒ | 𝔪 ≤ | old J8 | 𝓕 / Q_sc | residual band |
|---|---|---|---|---|---|---|---|
| 60 | − | +3.429550 | +3.410227 | **+0.019323** | +0.016445 | +0.002417 | [+0.01735, +0.01937] |
| 60 | + | +2.449294 | +2.459372 | **−0.010078** | −0.030823 | −0.082113 | [−0.01199, −0.01003] |
| 120 | − | +3.743901 | +3.731132 | **+0.012768** | +0.011688 | +0.001739 | [+0.01080, +0.01282] |
| 120 | + | +2.763643 | +2.771704 | **−0.008061** | −0.025465 | −0.059068 | [−0.00999, −0.00801] |
| 240 | − | +4.233824 | +4.226624 | **+0.007200** | +0.007008 | +0.001055 | [+0.00520, +0.00725] |
| 240 | + | +3.253567 | +3.258845 | **−0.005279** | −0.019181 | −0.035826 | [−0.00725, −0.00523] |
| 340 | − | +4.534698 | +4.529603 | **+0.005095** | +0.004978 | +0.000769 | [+0.00304, +0.00515] |
| 340 | + | +3.554441 | +3.558408 | **−0.003968** | −0.016158 | −0.026127 | [−0.00601, −0.00391] |

(one-sided column from the largest run, nodes ±1700 / U = 2200; sandwich from the reference run,
nodes ±1300 / U = 1500 — the two one-sided values differ by ≤ 5·10⁻⁵.)

* Minus channel: the old J8 values lie inside the sandwich at T = 120, 240, 340 and 9·10⁻⁴
  below it at T = 60 (where the weight reaches down to ξ ≈ 10, the worst region for the old
  truncation) — the old evaluator was converged on this channel, as claimed. The scalar-floor
  structure 𝔪 ≥ 𝓕 holds at every T with room to spare (band low +0.01735 vs 𝓕 = +0.00242 at
  T = 60; +0.00304 vs +0.00077 at T = 340).
* Plus channel: the whole sandwich is strictly negative at every T, and 𝔪 − Q_sc ≥ +0.020 > 0
  at the sandwich's lower end, so the Hilbert–Schmidt square in (6) is nonnegative — the whole
  chain's sign check passes.

**Honest sandwich width.** One-sided column: limited by the convergence spread over the four
node/quadrature settings, ≤ 3·10⁻⁴ on 𝔪. Two-sided: ‖z‖² comes out **strictly positive at every
one of the 2801 grid points** (min −1.3·10⁻¹¹ at ξ = 0, where k_∞ = 0; median 2.0·10⁻⁵, max
3.2·10⁻⁴), so no clipping and no noise floor is applied anywhere. The resulting k₂ sandwich is
3.5·10⁻⁴ wide (median, max 1.4·10⁻³), giving margin sandwiches of width ≈ 2·10⁻³. Two further
controls: ‖Pψ‖² computed exactly through the complement exceeds its independent Galerkin lower
bound `qᴴΓ⁻¹q` by a median relative 5.7·10⁻⁵ — the correct one-sided order, and small; and
doubling U (1500 → 2500) or halving h (0.05 → 0.025) changes every entry of the sandwich by
less than 10⁻⁵.

*Recorded as it happened.* The first pass produced ‖z‖² < 0 at ~10 % of the points (worst
−5.4·10⁻³ near ξ ≈ 37), impossible for a squared norm. It was insensitive to U and h, which
ruled out quadrature and pointed at a component error: a stray conjugation in the
`m_b = √2 (Fy)(2u)` coefficient vector (`Fb @ c̄` for `Fb @ c`). After the fix ‖z‖² is positive
everywhere; k₂ˡᵒ never used that term and did not change.

## 4. Mechanism of the old evaluator's plus-channel failure

The plus weight `1 + cos aξ` is **maximal (= 2) exactly at the Euler harmonics
ξ = 2πk/log 2 = 9.0647k**, where three things coincide:

1. the truncated Euler multiplier error `(1+r)r^{J+1}` of `A₂^{(J)}` peaks (the phases
   −ξ log β_j form an arithmetic progression, i.e. a Poisson kernel in ξ log 2, of height
   1/(1−r) = 3.41 at those points — `mellin_d2/PROGRESS.md`, 01:00);
2. the dormant near-unit angles of A₂ sit there (the retained-mode truncation
   `|λ| < 1 − 10⁻¹²` in `prod_op.py` drops exactly the modes that carry the compensating mass);
3. `|b(ξ)|² = |1 − r e^{−iaξ}|²` attains its **minimum** (1−r)² = 0.0858, i.e. the true k₂ is
   smallest precisely where the old error is largest.

Measured: mean(d_J8 − d₂ˡᵒ) = **+5.84·10⁻³** for |ξ − 2πk/log2| < 1, against +4.8·10⁻⁴,
+8.7·10⁻⁴, +6.9·10⁻⁴ in the three outer shells. That excess, weighted by 1+cos aξ and
integrated, is −0.0175 at T = 120 — exactly the gap between the old −0.02546 and the new
−0.00806. The minus weight `1 − cos aξ` vanishes to **second order** at the same points, which
is why the minus channel converged in J while the plus channel drifted by −34 % per step.

## 5. Status labels

* **Certified interval:** none — everything here is IEEE double.
* **Structurally one-sided** (would become an enclosure verbatim under ball arithmetic, since it
  is a supremum over an explicit finite-dimensional subspace of the true space):
  `k₂ ≥ |b|² pᴴG⁻¹p`, hence `𝔪 ≤ (1/2π)∫W q₂ − ∫W k₂ˡᵒ`. Its remaining float dependencies are
  Γ (kernel evaluations, ~10⁻¹³) and X (quadrature, U- and h-truncation, ≤ 1.1·10⁻⁶ per entry).
* **Diagnostic:** the residual upper bound on k₂ (float only, but with no clipping and two
  independent controls), hence the lower end of every sandwich.
* **Inherited, not re-derived:** the RESONANCE/SCALARFLOOR conventions (k_S = q_S/2π + d_S,
  𝔪(v) = −∫|v̂|²d₂), Theorem 3 (18), the sandwich (21)–(22); the d_∞ table is a cross-check only
  (the evaluator recomputes d_∞ from its own spectral data).

## 6. Runtime and files

24-core box, `systemd-run --user`. Gram system (nodes 2561, grid 60 000): 82 s; +60 s for the
full two-sided evaluation of 2801 ξ-points. Largest run (nodes 3599, U = 2200): 396 s. All seven
production runs ≈ 28 min wall. The archimedean kernel costs ~0.1 s to set up (10 prolate modes
from a 100×100 Legendre–Galerkin matrix).

`docs/routeB_bus/phase5_codex/euler_gram/`: `arch.py` (k_∞, ϑ_RS, Sonin phase), `ekernel.py`
(K via 800-pt Nyström + 22507-pt dyadic Mellin grid — channel 1), `fastk.py` (K via prolate
modes + closed-form Legendre moments — channel 2), `k2.py` (EulerGram: nodes, exact Γ, X, G,
lower bound, sandwich), `pperp.py` (exact ‖S_∞v‖² through the complement; w_ξ(s) on (1,2)),
`prod.py`/`prod2.py` (production), `margin.py` (h_T, folded weights), `analyse.py`, `checks.py`,
`final.py`. Scratch: `~/.claude/jobs/4b35770d/tmp/euler_gram/{k2_A..G.npz, prod*.log}`.

## 7. What this closes and opens

CLOSES: `PROFILES_ADDENDUM_INSTRUMENT_2026-09-07` — the plus-channel full margin is no longer
instrument-limited: it is negative at T = 60, 120, 240, 340, and T·|𝔪| still grows (0.60, 0.97,
1.27, 1.35), so the negativity does not obviously wash out as T → ∞.
OPENS: nothing new is required from the judge. The natural next step is an arb/ball version of
the same lower bound (Γ from ball kernel evaluations, X from a rigorous oscillatory quadrature)
— it would turn the sign statement into a certificate with no new mathematics.
