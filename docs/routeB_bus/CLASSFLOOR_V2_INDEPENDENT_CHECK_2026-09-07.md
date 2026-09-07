# CLASSFLOORCHECK2 — independent check of the SECOND judge's CLASS_FLOOR verdict (874-line UPLOADED_VERSION)
Own re-derivation + own computation (mpmath/sympy/numpy). Nothing re-executed from the h4/packet runs.
Files read: v2 verdict; v1 verdict §3–§4 (comparison); CLASSFLOOR_INDEPENDENT_CHECK_2026-09-07 (comparison).

## 1. §2 Theorem 1, the constant, (15)–(18) — **CORRECT**
- `2 + 8/(1−2^{−1/2}) + 64√2 = 18 + 72√2 = **119.823376491** < 128`. The rational route is valid:
  `8/(1−2^{−1/2}) = 16+8√2 ≤ 16+80/7 = 27.4286 ≤ 28`, `64√2 ≤ 640/7 = 91.4286`, so the coefficient
  is `≤ 2+28+640/7 = **121.4286 < 128**`. (16) → (15) since `4 ≤ 128` and `119.82 ≤ 128`.
- (17) `|I| ≤ 2`: `∫₀¹v^{−1/2}dv = 2` exactly. (17) `|I| ≤ 128β^{−1/2}`: the same dyadic split with
  amplitude `y^{−1/2}` gives `2 + (16+8√2) + 64√2 = 18+72√2 = 119.823` — i.e. the *same* total, so
  128 holds with the same slack. Derived, not assumed.
- (18) re-derived: split `∫₀¹|I(βu,ξ)|²du` at `u=1/β`; below, `|I|≤2` gives `4/β`; above, `βu≥1` and
  `|I|≤128(βu)^{−1/2}` give `(128²/β)∫_{1/β}^1 du/u = 128²logβ/β`. Sum `(4+128²logβ)/β`. **CORRECT.**
- Numerics (series `I=Σ(−1)ⁿβ^{2n}/((2n)!(s+2n))`, `J=Σ(−1)ⁿβ^{2n}/((2n)!(s+2n)²)`, dps≥β/2+60,
  cross-checked against `mp.quad`): β∈{1,10,100,1000} × ξ∈{0,5,50,500}, all 16 cells obey (15) and
  (17). Worst ratio to the bound: **J 0.0306, I 0.9045** (the I-worst is β=1,ξ=0 against the bound 2).
  (18) spot-checked by quadrature, e.g. β=10,ξ=0: `‖I‖²=0.9188 ≤ 3772.96`.
- Independent reproduction of the certificate constant: (4) with 256 gives **T = 13.9371046604**
  (matches the recorded value to all printed digits), `T<14`, `4T = 55.7484 < 56`. With the new
  constant 128 the same series gives 12.4712.

## 2. §3.1 (19)–(21) — **CORRECT**
`F_∞B* = F_∞(I−rU_{−a}) = (I−rU_a)F_∞ = BF_∞` from `F_∞U_{−a}=U_aF_∞`; B and (B*)^{−1} are functions
of `U_a`, hence commute, so `B(B*)^{−1}F_∞ = (B*)^{−1}BF_∞ = (B*)^{−1}F_∞B*`. (20): expanding
`(I−rU_a)Σ_j r^jU_{−ja} = Σ_j r^jU_{−ja} − rU_a − Σ_k r^{k+2}U_{−ka} = (1−r²)Σ_j r^jU_{−ja} − rU_a`.
‖A‖<1: `A` compact self-adjoint with ‖A‖=1 gives `f` with `⟨Ef,FEf⟩=±1`, equality in Cauchy–Schwarz
(F unitary) forces `FEf=±Ef`; `G=B*Ef≠0` stays supported in (0,1) (`B*`,`(B*)^{−1}` preserve it) and
`F_∞G=±G`, so the cosine transform of an L¹(0,1) function vanishes on (1,∞) ⇒ `G≡0`. **CORRECT.**

## 3. §3.2 (22)–(24) — **CORRECT**
- Coefficients: RESONANCE/v1 general-p form `β_{−1}=2π/p, c_{−1}=−1/p, β_j=2πp^j, c_j=1−1/p` at p=2
  gives exactly `π, −1/2, 2π2^j, 1/2`. **Consistent.** (Re-derived from `U_cF_∞`'s kernel
  `2e^{−c/2}cos(2πe^{−c}uv)` against (20)'s coefficients `(1−r²)r^j` and `−r`, r=p^{−1/2}.)
- Convergence: `‖I(β_j·,ξ)‖_{L²} ≤ β_j^{−1/2}√(4+128²logβ_j) ≍ 2^{−j/2}√(1+j)`, `Σ = 5.862 < ∞`;
  `|J(β_j,·)| ≤ 128β_j^{−1/2}(1+logβ_j) ≍ 2^{−j/2}(1+j)`, `Σ = 11.657 < ∞`. Uniform in real ξ. ✔
- (23) Riemann–Lebesgue: after `v=e^{−x}`, `I=∫₀^∞e^{−x/2}cos(βe^{−x})e^{−iξx}dx` with a fixed L¹
  integrand (J carries an extra factor x, still L¹) ⇒ →0; vector version by domination
  `|I(βu,ξ)| ≤ min(2,128(βu)^{−1/2}) ∈ L²(0,1)`. ✔
- (24) γ **verified numerically against my own cosine-Mellin derivation**: from
  `∫₀^∞v^{s−1}cos(cv)dv = c^{−s}Γ(s)cos(πs/2)`, `γ_∞(ξ) = 2(2π)^{−1/2−iξ}Γ(1/2+iξ)cos(π/4+iπξ/2)`;
  times the Euler factor `(1−re^{iaξ})/(1−re^{−iaξ})`. At ξ=3: derived `0.84339663646 − 0.537291460576i`,
  claimed formula identical, |diff| **5.1e−41**; also ξ∈{0,1,−3,10}. `|γ| = 1.000000000000` at all.

## 4. §3.3 nuclearity — **CORRECT, but the last paragraph is asserted (see §11)**
The local-Fourier argument closes: on a smooth partition `χ_j(x)k(x+y)χ_k(y)` is smooth and compactly
supported inside a unit rectangle, so its periodic extension is smooth; two derivatives per variable
give coefficients `≲(1+j+k)^{−N}(1+n²)^{−1}(1+m²)^{−1}`; each term is rank one with L²-norm product
`O(1)`; `Σ_{n,m}(1+n²)^{−1}(1+m²)^{−1} < ∞` and `Σ_{j,k}(1+j+k)^{−N} < ∞` for **N>2** (the count of
(j,k) with j+k=s is s+1, so N>2 is exactly right). Restriction to quadrants is by projections. ✔
`v̂m` Schwartz ✔ (v̂ of a compactly supported smooth v is Schwartz on ℝ; m has polynomially bounded
log-derivatives). (25) is the algebraic identity `[T_v,P]FP + PT_vFP = T_vPFP`. ✔
`T_vEA` HS: kernels of the partial sums converge in HS by (22)+`∫|v̂|²<∞`, and `A_J→A` in operator
norm identifies the limit. ✔

## 5. §3.4 THE KEY STEP (26)–(28) — **CORRECT**, verified three ways
- **(27) re-derived.** With `ĥat f(ξ)=∫fe^{−iξx}dx`: `[P,C_b](x,y)=k_b(x−y)(1_{x<0}−1_{y<0})`, so
  `Tr(C_a[P,C_b]) = ∫∫k_a(x−z)k_b(z−x)(1_{z<0}−1_{x<0})dzdx`; substituting `h=x−z` and using
  `∫(1_{x−h<0}−1_{x<0})dx = h` gives `∫h k_a(h)k_b(−h)dh`; and `h k_a(h)` has symbol `ia'`, so
  Plancherel gives `(i/2π)∫a'(ξ)b(ξ)dξ`. **Exactly the verdict's route.**
- **Numerical channel (discrete model, my own).** Unit-spaced positions x=−M..M−1, Toeplitz
  multipliers a,b (2π-periodic), P = projection onto x<0. `Tr(C_a[P,C_b])` vs `(i/2π)∫a'b`:
  smooth symbol pair `−0.0726088430` vs `−0.0726088150` (diff 2.8e−8, finite-difference a'), stable
  in M∈{120,260}; with **exact** trig-polynomial coefficients both sides give `−0.300000000000`,
  diff **0.0**. The spatial sum `Σ_h h k_a(h)k_b(−h)` agrees with the matrix trace to 1e−16.
- **(28).** `T_vRT_v* = C_{a₁}PC_{b₁} − C_{a₀}PC_{b₀}`; since `C_a[P,C_b] = C_aPC_b − C_{ab}P` and
  `a₁b₁ = |v̂|²|m|² = |v̂|² = a₀b₀`, the two `C_{ab}P` terms cancel — this is exactly why the
  "multiplier products agree" remark is load-bearing. Checked numerically on a 9-point model:
  `max|a₁b₁−a₀b₀| = 1.1e−16`, `‖lhs−rhs‖ = 9.5e−16`. Then
  `a₁'b₁ − a₀'b₀ = |v̂|²m'\bar m`, giving `(1/2π)∫|v̂|²q₂`. ✔
- **Sign convention.** `m(ξ)=γ(−ξ)`, `γ'/γ = i q₂` by log-differentiating (24) (digamma reflection
  gives `iReψ(1/4+iξ/2)`, the Euler factors give `−ia·2Σ_{j≥1}r^jcos(jaξ)`), hence `m'/m = −iq₂(−ξ)
  = −iq₂(ξ)` (q₂ even). Numerically at ξ=0.7: `m'/m = 3.345716463i`, `−iq₂ = 3.345716463i`, diff
  2.6e−41; and `i m'\bar m = −3.345716463 = q₂` — **identical to v1's `i m'\bar m = q_S` and to
  RESONANCE's `q_S` at p=2**. No sign conflict.
- **`c_A` verified analytically and numerically.** From `ψ(z) = −γ_E+∫₀^∞(e^{−t}−e^{−zt})/(1−e^{−t})dt`
  and `t→2t`, `q_∞ = 2∫₀^∞e^{−t/2}(1−cosξt)/(1−e^{−2t})dt − c_A` with
  `c_A = γ_E+logπ+(ψ(1)−ψ(1/4)) = γ_E+logπ+3log2+π/2 = γ_E+log(8π)+π/2`. **Exactly (the verdict's
  constant).** Numerics at ξ∈{0,1.3,4}: rep vs true agree to 9e−41 / 3e−16.
- **Weil identification.** `C_v(t)=(1/2π)∫|v̂|²cos(ξt)dξ`, so the j-th cosine in (26) contributes
  `−2ar^jC_v(ja) = −2(log2)2^{−j/2}C_v(j log2)`. Support: `a+2δ = 0.79458 < log3 = 1.09861`, so only
  p=2, j=1 survives and every p≥3 term dies; pole terms die by moment-nullity. ✔

## 6. §3.5 (29)–(32) — **CORRECT; it does close the gap the earlier checker named in v1 §4.4**
- (29) re-derived: `WW* = P+Q`, `(W*W)^{−1} = [[Z,−AZ],[−AZ,Z]]`, `I−Z = −A²Z`, so
  `D = W[I−(W*W)^{−1}]W* = W[[−A²Z,AZ],[AZ,−A²Z]]W*`. **Random finite model** (n=14, k=6, F a real
  symmetric involution `OΣO^T`, P the cutoff, S = I − proj(ran W)): `‖D−WNW*‖` = 7.4e−15, 9.1e−15,
  1.2e−13, 6.0e−15 in four trials (‖A‖ = 0.918…0.996); `‖D−(P+Q−I+S)‖ ≤ 1.7e−16`;
  `‖W[[0,A],[A,0]]W* − (PQ+QP)‖ ≤ 3.6e−16`; `AZ = A+A³Z` to 1.4e−14. ✔
- (31) re-derived by `Tr(NW*T_v*T_vW)` with `T_v*T_v = ∫|v̂|²|e_ξ⟩⟨e_ξ|`: the two diagonal blocks each
  give `−⟨u,Zu⟩` (using `Fe_ξ=γe_{−ξ}`, `|γ|=1`, `u(−ξ)=\overline{u(ξ)}`), the two off-diagonal blocks
  give `γ[t+⟨u,AZ\bar u⟩]` and its conjugate. Matches (31) **with γ, not \barγ** — same as the earlier
  checker found for v1 (23).
- **The gap.** v1 §4.4 stage 1 asserted "diagonal traces follow by an absolutely convergent
  smooth-kernel expansion" (a Fubini/Mercer interchange over the non-L² wave `e_ξ`). v2 §3.5 now
  *names the mechanism*: band-limit in frequency (kernel then continuous on a compact square, its
  double Mellin integral absolutely convergent), approximate by step-function rank-ones
  `e_i=|Δ_i|^{−1/2}χ_{Δ_i}` — `Σ_i⟨e_i,Ke_i⟩ = Tr(E_nKE_n) → TrK` because `E_nKE_n→K` in trace norm
  for trace-class K and `E_n→I` strongly, while the same sum `→∫k(ξ,ξ)` by uniform continuity —
  then remove the band by trace-norm convergence. That is the correct standard argument and it is
  the missing sentence. **Gap closed at referee-sketch level** (the trace-norm pinching lemma itself
  is used but not stated).
- (32) `S=R+D`, `Tr(T_vST_v*) = ‖T_vS‖²_HS = n₂(v)`, `Tr(T_vRT_v*) = L₂(v)` ⇒ `n₂−L₂ = ∫|v̂|²d₂`. ✔

## 7. §3.6 (33)–(35), §3.7 — **CORRECT**
- (33): with `K=P+Q`, `D=K−I+S`, `KS=SK=0`, `S²=S`: `D² = K²−2K+I−S`, so `D+D² = K²−K = PQ+QP`.
  Finite model: `‖D+D²−(PQ+QP)‖ ≤ 7.4e−15` in all four trials. ✔
- (34): `m(h) − F(h) = ∫|v̂|²(ℓ₂−d₂) = Tr(T_vD²T_v*) = ‖T_vD‖²_HS ≥ 0`, using `|v̂_h|² = W_h`. ✔
- (35) **re-derived symbolically**: with `w = e^{−iφ/2}u = X+iY`, `ℓ₂−d₂ = 2⟨w,Zw⟩−2Re⟨w,AZ\bar w⟩
  = 2⟨X,(I−A)ZX⟩+2⟨Y,(I+A)ZY⟩`, and `(I−A)Z=(I+A)^{−1}`, `(I+A)Z=(I−A)^{−1}`. Numerically on three
  random models: `ℓ₂−d₂` vs RHS agree to ≤3.6e−15, all ≥0. Phase-independent. ✔
- §3.7 chain sound: `η_n→η₄` in H³ ⇒ `h_n=(∂²−1/4)η_n→h₄` in H¹; moments stay exactly zero because
  `∫(∂²−1/4)φ·e^{±x/2} = 0` identically for `φ∈C_c^∞(I)`; the log-growth multiplier `k₂=O(log(2+|ξ|))`
  is dominated by the H¹ weight `1+ξ²`, so all three integrals converge. `d₂,ℓ₂` bounded ⇒ L² suffices
  for them. **No unpaid endpoint term.** (v1 used H⁴/H²; v2's H³/H¹ is weaker and still sufficient.)

## 8. §4.1 (36)–(37) — **CORRECT**
`|ℓ₂| ≤ 2|t| ≤ 2T < 28`, `∫W_h = 2π` (lobes disjoint: `2δ = 0.10137 < a = 0.69315`), so
`|N_F(h)| ≤ 2π·28·‖h‖² = 56π‖h‖²`, and `56π = **175.929188601 < 176**` ✔ (with the recorded
T₀ = 13.9371046604 the sharper `4πT₀ = 175.1388` also holds). Polarization ⇒ ‖T‖ ≤ 176 and
`N_F(h) ≥ 1/500 − 176(2ε+ε²)`. Exact rational at ε=10⁻⁶:
`(1/500 − 176(2ε+ε²))/(1+ε)² = 1647999824/1000002000001 = **0.001647996528** > 1/1000` ✔.
Sharp choice: it already fails at ε=5·10⁻⁶ (0.000240) and holds at 2·10⁻⁶ (0.001296).

## 9. §4.4 (43), (44), the diagonal counterexample — **CORRECT**
- (43) **re-derived**. `J = ∫₀^∞g e^{−iξx}dx`, `g = xe^{−x/2}cos(βe^{−x})`, `g(0)=g(∞)=0`, two parts:
  `|J| ≤ (|g'(0)|+‖g''‖₁)/ξ²`. `g'(0) = cosβ` (|·|≤1, sympy-confirmed). `g'' = 2(fc)'+x(fc)''`
  (sympy: difference ≡ 0), with `‖(fc)'‖₁ ≤ ½·2 + β·⅔ = 1+2β/3` and
  `‖x(fc)''‖₁ ≤ ¼·4 + 2β·4/9 + β²·4/25 = 1+8β/9+4β²/25` (using `∫₀^∞xe^{−cx}=1/c²` at c=½,3/2,5/2).
  Total `‖g''‖₁ ≤ **3+20β/9+4β²/25**`, hence `C_β = **4+20β/9+4β²/25**`. **Exactly as printed.**
- Numerics β∈{π,2π,4π,8π} × ξ∈{2,5,20,100}: all 16 cells obey (43), worst ratio **0.1439**.
  Actual `‖g''‖₁` vs the majorant: 2.893 vs 11.560 (β=π), 19.490 vs 56.191 (β=4π) — coarse, valid.
- (44): `|ν| = |w_aℓ₂| ≤ 2·2|t|` and `|t| ≤ (1/2π)Σ_{j≥−1}|J(β_j,ξ)|`; split at J, (43) below and the
  256-tail above. The stated factor 4 = (2 for 2Re)·(2 for w_a≤2) is right. `β_J ≍ √X` does drive it
  to 0: `Σ_{j≤J}C_{β_j} ≍ β_J²` so the first piece is `O(β_J²/X²) = O(1/X)`, and `ε_J = O(X^{−1/4}logX)`.
- Diagonal counterexample: `T = diag(a₁..a_N, −η/2, 0,0,…)` is compact, `Π_NTΠ_N ≻ 0`,
  `‖T−Π_NTΠ_N‖ = η/2 < η`, and `T` has a strictly negative direction. Kills "positive finite head +
  absolute tail ≤ η ⇒ PSD" whenever `η ≥ λ_min(head)`, which compactness always permits. **CORRECT.**

## 10. v1 vs v2 — comparison
- **Theorem 1 is NOT an independent second proof.** v2 (16) derives the same coefficient
  `2+8/(1−2^{−1/2})+64√2 = 18+72√2 = 119.823` as v1 and then reports the rounder 128. Same dyadic /
  van-der-Corput argument, same constants; 120 vs 128 is a reporting choice, no contradiction, but no
  independent confirmation either. (My own re-derivation is the third channel; it agrees.)
- **The source identity IS two genuinely different routes.** v1 §4.3 takes the distributional Fourier
  kernel of P (`½δ + (i/2π)pv 1/(ξ−η)`), cancels the δ, and reads the divided-difference diagonal.
  v2 §3.4 never uses a distribution: it computes the spatial trace `∫h k_a(h)k_b(−h)dh` from
  `∫(1_{x−h<0}−1_{x<0})dx = h` and Fourier-inverts. Both land on `(1/2π)∫|v̂|²q₂`, and my discrete
  matrix model confirms the v2 route to machine precision. An error in one would not propagate.
- **v2 §3.5 does supply what v1 §4.4 asserted** (the Fubini/Mercer interchange over the non-L² wave):
  band projection + step-function rank-one averaging + trace-norm removal. Sketch-level but the
  mechanism is correct and standard.
- **No mathematical contradiction between the two verdicts** was found. Coefficients (p=2 vs general
  p), γ, q₂'s sign convention (`m'/m=−iq₂` ≡ `im'\bar m=q_S`), (29)/(33)/(34)/(35), the H-regularity
  chain and the §4.1 rationals are all mutually consistent and each independently reproduced here.
- **No RESULT code of v2 needs to change.** Q1 PARTIAL_WITH_PRECISE_REMAINDER / Q1_H4
  CERTIFICATE_RATIFIED, Q2 PROVED_ON_CLASS, Q3 PROVED_ON_CLASS, Q4 PARTIAL_WITH_PRECISE_REMAINDER
  are all defensible on what I could re-derive. Q3 rests on §3.5's sketch, but the verdict already
  carries `VERIFIER: PAPER`, `LEAN_KERNEL_VERIFIED: false`, `INDEPENDENT_REVIEW: pending`.

## 11. First step in v2 §3 that is stated rather than proved
**§3.3, last paragraph, first sentence:** *"For each shifted ordinary Fourier term in (20), its trace
norm in (25) grows at most polynomially in |j|: modulation differentiations only introduce powers of j
in the Schwartz seminorms."* No estimate is written. This single sentence carries the trace-norm
convergence of the infinite Euler sum, on which (25), (30) and hence (31)–(32) depend. It is very
likely true — the Schwartz seminorms of `e^{ijaξ}v̂(ξ)m(ξ)` grow polynomially in j and the §3.3 trace
bounds are continuous in finitely many of them — but it is asserted, not derived.
Second (weaker) asserted step: §3.4's *"The trace-class lemma makes this a trace identity rather than
a formal diagonal integral"* — the `Tr = ∫K(x,x)` step for (27). It is essentially covered by §3.3's
own explicit rank-one decomposition (the trace of an absolutely summable rank-one sum is the sum of
diagonal pairings), so I do not count it as a gap.
Third: §3.5's band-projection paragraph uses, without stating, the pinching lemma `E_nKE_n→K` in
trace norm. Standard.

**UNVERIFIABLE here** (out of scope, not re-run): the recorded h4 compact-integral, quadrature and
tail balls, the enclosure [0.0034393622, 0.0035782035], the packet pencil floor vs 1/1000, and the
`EBASE_DEF`/`EBASEM_DEF` receipt question — §1.5/§1.6 are audits of pinned outputs, and I re-executed
nothing. The one recorded constant I *could* reproduce independently, `T = 13.9371046604` from (4)
with constant 256, matches to all printed digits.
