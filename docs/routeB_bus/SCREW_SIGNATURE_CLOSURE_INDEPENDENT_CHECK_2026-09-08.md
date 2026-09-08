# SCREW_SIGNATURE_CLOSURE_DICTIONARY_AUDIT — independent check

Target: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_SCREW_SIGNATURE_CLOSURE_2026-09-08.md`
Checker: fresh adversarial agent. Every number below is from my own sympy/mpmath/numpy run in
`/home/chirurgie/.claude/jobs/4b35770d/tmp/sccheck/` (chk1..chk8.py). Repository untouched.
Definitions taken from KERNEL (K6)/(K16)/(K21)/(K23), ALIGN (A22)/(A23), Suzuki (1.11) card.

## Verdict headline

- **`sig(Q̄) = (∞, r)` STANDS** — every algebraic step re-derived independently; it is a theorem
  *modulo three named imports* ((K16) signed explicit formula, (K21)/(K23) separating tests +
  radical, (K14) unconditional positive direction). It says nothing about whether `r > 0`.
- **«negative directions are visible on a finite window» (SC13) STANDS as a statement about the
  source form** (for every `k ≤ r` there is one finite `a` and a `k`-dim subspace of compact tests
  in `(−a,a)` with Gram `≤ −I_k/2`). Its restatement as `n_−(a) = #{negative eigenvalues of A_a}`
  rests on an **undeclared form↔operator dictionary** — see ASSERTED-NOT-DERIVED below.
- No sign of Q is proved anywhere; the supplement says so repeatedly and correctly.

## Per-item results

| Item | Result | My computation |
|---|---|---|
| (SC1) multiplicity as weight, no jet coordinates | CORRECT | Weil formula sums `Σ_ρ h(ρ)` with multiplicity = `Σ_distinct m_λ h(λ)`; no `h'(ρ)`. (K21)/(K22) build one separating test per **distinct** zero by dividing `m` times, so a multiple zero still yields exactly one evaluation functional. |
| (SC2)/A1 pair block inertia | CORRECT | `[[0,m],[m,0]]` eigenvalues `{m,−m}`, inertia (1,1) for every `m>0`; `U^T B U = diag(m,−m)` with `U=(1,1;1,−1)/√2`; at `m=3` the vector `(1,−1)` gives exactly **−6**. Not `(m,m)`. |
| (SC3) normalised separating tests | CORRECT | With `F(λ)=F(jλ)=1/√(2m)`: `Q[e⁺]=+1`, `Q[e⁻]=−1`, `Q(e⁺,e⁻)=0`; distinct orbits Q-orthogonal by disjoint coordinate support. |
| (SC4) `ind₊=s+r`, `ind₋=r`, `rad=0` | CORRECT (logic sound) | Upper bound: the `r` negative coordinates `(u−v)/√2` map to `ℂ^r`; on the kernel `u=v`, each orbit contributes `2m|u|²≥0` and each fixed point `m|F|²≥0`, so a negative-definite subspace meets the kernel unless `dim ≤ r`. Symmetric argument with the `s+r` positive coordinates: on that kernel `v=−u` gives `−2m|u|²≤0`. Lower bounds from (SC3). Random finite models reproduce `(s+r, r)` exactly for 3/3 random multiplicity patterns (e.g. `s=3,r=2,m_fix=[4,5,3],m_orb=[4,5] → (5,2)`). Completion step uses density of compact pole-null tests (KERNEL §2.2) + `|Q|≤(65/3)‖·‖_E²` (K9): standard and correct. |
| (SC5) `sig=(∞,r)`, `RH ⟺ r=0` | CORRECT | `ind₊=∞` is proved **without** counting on-line zeros: `(∂²−¼)e^{±x/2}=0` (checked symbolically) so `(∂²−¼)C_c^∞(J)` is pole-null and infinite-dimensional (injective on compact tests), and (K14)'s floor is real: I recomputed `2∫_d^∞A₀ = 19.5926…`, `c_A = γ+log8π+π/2 = 5.37218…`, floor `= 14.2204… > 1` at `d=2^{−24} < log2`. Off-line quartet = 2 j-orbits → (2,2); the real 4-dim block `4m(u_Rv_R+u_Iv_I)` has eigenvalues `{2,2,−2,−2}` → inertia (2,2). Confirmed. |
| (SC6) `P = 2|M_c|²−2|M_s|²` | CORRECT | Hermitian identity `M̄₊M₋+M̄₋M₊ − (2|M_c|²−2|M_s|²) ≡ 0` (sympy, exact), with `M_c=(M₊+M₋)/2 = ∫f cosh(x/2)`, `M_s=∫f sinh(x/2)`. |
| (SC7)/A3 pole eigenvalues on `(−a,a)` | CORRECT | `∫_{−a}^a cosh²(x/2)=sinh a+a`, `∫ sinh²(x/2)=sinh a−a`, cross term 0 (sympy). `M₊(cosh)=M₋(cosh)=sinh a+a`; `M₊(sinh)=sinh a−a = −M₋(sinh)` ⇒ eigenvalues `2(sinh a+a)` and `−2(sinh a−a)`. Independent numeric (600-pt discretised rank-2 kernel, `a=1.3`): `−0.7967622` / `5.9967622` vs closed forms `−0.7967649` / `5.9967649`; exactly one negative, one positive eigenvalue. Trace `=4a` matches `∫` of the diagonal `≡2`. |
| (SC8)/A4 `−g''_pole` | CORRECT | `g=−4(e^{t/2}+e^{−t/2}−2)` ⇒ `g''=−2cosh(t/2)` ⇒ `−g'' = e^{t/2}+e^{−t/2}`. |
| (SC9) double integration by parts ⇒ `P[f]` | CORRECT | By hand: `∬g(x−y)f̄'(x)f'(y) = −∬g''(x−y)f̄(x)f(y) = M̄₊M₋+M̄₋M₊`. Numeric on a compact bump on `[−2,2]`, 4000-pt grid: LHS `1.3564433660609`, `2M₊M₋ = 1.3564433660401`, **rel. err 1.5e−11**. The `i` in `Df=if'` cancels: `conj(i)·i=1`. |
| (SC10) moment matrix / determinant | CORRECT | `F_{U_tΦ}(z)=e^{zt}F_Φ(z)` ⇒ matrix `c·[[e^{b/2},e^{−b/2}],[e^{−b/2},e^{b/2}]]`, `det = 2c² sinh b = c²(e^b−e^{−b})`, nonzero for `b>0`. |
| `c = F_Φ(±½) = ξ(1) ≠ 0` | CORRECT — **but the directive's hinted value 0.497 is wrong** | `ξ(s)=½s(s−1)π^{−s/2}Γ(s/2)ζ(s)` ⇒ `ξ(1)=ξ(0)=**0.5 exactly**` (mpmath: 0.5000000000000000000001). `0.4971207781883141` is `ξ(½)=Λ_ξ(0)`, a different point. Independent channel: I integrated the explicit (A22) series numerically (using its evenness) and got `F_Φ(½)=F_Φ(−½)=0.5` to 15 digits, `F_Φ(0)=0.49712077818831=ξ(½)`, `F_Φ(1)=0.50873103872632=ξ(3/2)`, and `F_Φ(iγ₁)=6.3e−22` at the first zero. So `F_Φ=Λ_ξ` and `c=½`. The document is right, the directive's parenthetical is not. |
| (SC11) bijection `ℋ/𝒩 → ℰ/𝒩_ℰ`; `P[Φ]=2|c|²`, `Q[Φ]=0` | CORRECT | `Φ, U_{±b}Φ ∈ ℰ` (double-exp decay; `W[U_tf]≤e^{2|t|}W[f]`, `𝒟` translation-invariant); `F_{U_bΦ}(λ)=e^{bλ}Λ_ξ(λ)=0` ⇒ radical by (SC1) + continuity. Surjectivity from the invertible 2×2 system, injectivity because `𝒩 = 𝒩_ℰ∩ℋ` (both directions follow from the same correction). `P[Φ]=2|c|²=0.5>0` while `Q[Φ]=0` ⇒ P does not descend. Sound. |
| (SC12) `n_−(a)<∞`, `n_0(a)<∞` | IMPORTED (from [26]) then CORRECT | Lower-bounded + discrete spectrum ⇒ finite negative part is immediate. The premise is a READ, not derived here. |
| (SC13) monotonicity, `sup_a n_−(a)=r` | CORRECT as a form statement; see ASSERTED-NOT-DERIVED for the operator reading | Monotonicity: a negative-definite subspace of `(−a,a)`-tests is one of `(−b,b)`-tests. Upper bound: §1 codimension argument, which indeed never uses pole-nullity. Lower bound: Gram of `{e_λ^−}_{k}` is exactly `−I_k`; A2's entrywise `<1/(2k)` gives operator-norm error `≤ k·1/(2k) = 1/2` by max-abs-row-sum for Hermitian matrices ⇒ envelope `−I_k/2`. Common cutoff = max of the `k` cutoffs. Honest that no cutoff uniform in `k` is claimed. |
| (SC14) `RH ⟺ n_−(a)=0 ∀a` | CORRECT given (SC13) + (SC5) | — |
| (SC15)/A6 source count | CORRECT | `Spec((−σ)T^{−1}) = {(−σ)/(μ_j−σ)}`; with `σ<min(0,λ_a)` the denominator is `>0`, so `(−σ)/(μ−σ)>1 ⟺ μ<0`, and `=1 ⟺ μ=0`. Multiplicity carried. |
| (SC17) shifted diagonal + `diag(−1,1)`, `σ=−2` | CORRECT | `μ/(μ−σ)`: `−1/(−1+2) = −1`, `1/(1+2) = 1/3`; shifted metric `diag(1,3) > 0`. Sign survives the shift. |
| (SC19) anchor `W_a(i)=2ie^{iθ}b_a` | CORRECT (algebra), one asserted symmetry | From (1.11) at `z=i` the first column dies (`z−i=0`) and the second gives `e^{iθ}·2i·⟨e^{−x},T^{−1}e^{−x}⟩ = 2ie^{iθ}b_a`; `F_a(i)=1` by construction. The equality of the `+` and `−` b-values is asserted from reflection symmetry of `A_a`, not derived. |
| (SC20) `|F_a(z)| ≤ ((|z−i|+|z+i|)/2)√(K_a(z)/K_a(i))` | CORRECT | Each column is `⟨e_z, T^{−1}e^{±x}⟩` with `e_z(x)=e^{−iz̄x}`; Cauchy–Schwarz for the positive `T^{−1}` gives `≤√(K_a(z)b_a)`; divide by `2b_a`; `K_a(i)=∫e^{−2x}=b_a` (checked: `e_i(x)=e^{−x}`). Numeric spot-check in the model (9 (a,z) pairs, incl. `a=3, z=2i`: `|F|=20.036 ≤ 28.405`): holds every time. |
| (SC22)/A7 comparison model | CORRECT | `1+iz=i(z−i)`, `−1+iz=i(z+i)` (sympy, exact) ⇒ both prefactors collapse to `−i`, and `sinh(B+A)−sinh(B−A)=2cosh B sinh A` gives `W_a(z) = −4i sinh a cos(az)`. Numeric quadrature of (1.11) vs the closed form at three `(a,z)`: `|diff| ≤ 2.5e−28`. `b_a=sinh 2a`; `F_a(z)=cos(az)/cosh a`; `F_a(i)=1`; `F_a(2i)=cosh 2a/cosh a` (at `a=3` both give `20.0359960641361`) `→∞`. The refutation of "anchor ⇒ normality" is valid. |
| (SC23)/A8 Herglotz normalisation | CORRECT | `Im m(z)=Im z·‖(L−z)^{−1}u‖²` — I checked that the two variants (`z` vs `z̄`) coincide because `|λ−z|=|λ−z̄|` on real `λ`, so the document's phrasing is not a defect. `m̃(i)=i` verified; Schwarz-after-Cayley bound `|(m̃−i)/(m̃+i)| ≤ |(z−i)/(z+i)|` holds at **200/200** random UHP points for a random 6-atom positive measure. |
| (SC26)/A9 Rouché | CORRECT | If `sup_{∂D}|F/H−1| < 1` then `|F−H|<|H|` on `∂D`, so `F` and `H` have equal zero counts in `D` — impossible for zero-free `F` and `H` with a zero. Threshold exactly 1. Numeric: three zero-free `F` against `H(z)=(z−z₀)e^{0.3z}` on `|z−z₀|=0.3` give `sup|F/H−1| ∈ {4.30, 4.23, 3.30} ≥ 1` and `sup|F−H| ≥ m_D=0.3091`. |
| local simple zero of `X/(X+iX')` and `X/(iX')` | CORRECT | For a zero of order `q`: `X/ξ_s' = (z−z₀)/(iq)·(1+O(z−z₀))` and `X/(X+ξ_s') = (z−z₀)/(iq+(z−z₀))`. Limit of ratio-to-claim `= 1` for `q = 1,2,3,4` (sympy). `z²` of v1 is nonzero at a nontrivial zero. |
| §7.2 `λ_a→−∞ ⇒ σ(a)→−∞` | CORRECT (trivial) | `σ(a) < λ_a → −∞` ⇒ `limsup σ(a) ≤ −∞`. Conditional on [S,(S24)], which I did not re-derive. |

## First ASSERTED-NOT-DERIVED step

**§3, the identification of `n_−(a)` with the form index of `Q` on `C_c^∞(−a,a)`.**
(SC12) imports from [26] that "the window operator `A_a`" is lower bounded with discrete spectrum;
(SC13) then proves monotonicity and `sup = r` by *form* arguments about `Q` restricted to tests
supported in `(−a,a)`. Nowhere is it derived — or even stated as a hypothesis — that `A_a` is the
self-adjoint operator of that form, i.e. that `⟨f, A_a f⟩_{L²(−a,a)} = Q[f]` with `C_c^∞(−a,a)` a
form core. Without that dictionary, the min–max step "a `k`-dim negative-definite subspace of
window tests ⇒ `n_−(a) ≥ k`" and the finiteness transfer both hang. Everything upstream of §3 is
either derived here or explicitly pinned to (K14)/(K16)/(K21)/(K23)/(A22).

Two smaller ones, both in §5.2: `b_a^+ = b_a^-` ("reflection gives equal b-values") assumes `A_a`
commutes with `x ↦ −x`; and `v_{±,a} = T_a^{-1}e^{±x}` is a source-convention import from [S,(S20)],
so (SC19)–(SC21) are theorems about *that* substitution, not about Suzuki's `v_±` unless the
convention is re-verified.

## Tight spots (correct as written, easy to over-read)

1. `ind₊ = s+r` is `∞` for zeta only because `s=∞`; the *unconditional* infinitude comes from (K14),
   not from any zero count. The document is careful; a reader who drops (K14) loses the claim.
2. `sup_a n_−(a) = r` carries **no modulus**: A2 explicitly refuses a cutoff uniform in `k`. For
   `r=∞` no finite window ever sees all of it. "Visible on a finite window" is per-`k`, not global.
3. (SC7) is the inertia of `P` alone. `P` has a negative direction on every window, yet `n_−(a)=0`
   under RH — no contradiction, because (SC1)/(K16) already contains the pole term and applies to
   non-pole-null tests. Worth stating explicitly; the supplement only implies it.
4. `Q[e_λ]=0` off-line does **not** make `e_λ` radical (`Q(e_λ,e_{jλ})=m_λ`). Correctly flagged.
5. The `−I_k/2` envelope is a Gram bound in the chosen basis, not an `L²` operator bound.
6. §7.1 writes `X` where §5.1 wrote `ξ`; the germ algebra is right, the letters drift.

## Adjudication of the three registrations

| Registration | p | My adjudication |
|---|---|---|
| `P_SC_SIGNATURE_MULTIPLICITY_AND_POLE_QUOTIENT_SURVIVE` — (SC4),(SC11),(SC13) | 0.90 | **SURVIVES.** (SC4) and (SC11) survive outright — I re-derived both and found no defect; for those alone I would price ≥0.97. (SC13) survives as a form statement and inherits the §3 dictionary risk. 0.90 is a fair blended price, slightly generous only because the dictionary gap is not disclosed in the claim ledger. |
| `P_SC_SOURCE_ANCHOR_AND_NORMALITY_CONTROL_SURVIVE` — (SC19)–(SC23) | 0.91 | **SURVIVES, and 0.91 is conservative.** Every equation reproduced exactly ((SC22) to 2.5e−28, (SC20) verified as an inequality, (SC23) 200/200). Residual risk is entirely the two source-convention imports named above, not the mathematics. I would price 0.95. |
| `P_SC_LOCAL_TARGET_DEFECT_SURVIVES` — (SC26) + germ qualifications | 0.96 | **SURVIVES.** Elementary Rouché plus a germ computation I confirmed for `q=1..4`. The stated hypotheses (holomorphy on a neighbourhood of `D̄`, `H≠0` on `∂D`, `F_a` zero-free on `D`) are exactly what the proof needs. I would price 0.98. |

## Plain answers

- **`sig(Q̄) = (∞, r)` stands.** Multiplicity enters (SC1) as a weight only; the `2×2` block is
  `(1,1)` for every `m`; the `r`-coordinate codimension argument caps `ind₋` and (SC3) attains it;
  `ind₊=∞` unconditionally by (K14). Conditional on (K16)/(K21)/(K23) as pinned, not re-derived here.
- **«negative directions are visible on a finite window» stands for the source form** — for each
  `k ≤ r` there is a single finite `a` carrying a `k`-dimensional strictly negative subspace of
  compact tests. Its translation into a statement about the eigenvalues of Suzuki's `A_a` is the
  one asserted, underived link in the chain.
- No sign result, no RH claim, and no numerical certificate is created or damaged by this audit.

Failure code NOT raised: I found no first-unsupported *equation*. The gap is a dictionary, not an
identity. If a code is wanted for the §3 link: `SCREW_WINDOW_FORM_TO_OPERATOR_DICTIONARY_ASSERTED`.
