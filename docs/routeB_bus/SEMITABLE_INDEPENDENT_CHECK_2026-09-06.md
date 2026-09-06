# Independent check — PROSHKA_VERDICT_GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_2026-09-06

Own derivations + python3 (numpy/scipy/mpmath). Read only: the verdict, its two parents (definitions),
2006.13771.txt for Lemma D.1. Scripts `chk1.py`…`chk6b.py` in this directory.
a=log2=0.6931471805599453, delta_0=(log3−log2)/8=0.05068313851352056, delta_*=(log3−a)/2=0.2027325540541,
a+2delta_0=0.7945134575869864 < log3=1.0986122886681098.

## 1. Lemma 1 (phase class) — CORRECT

- (2) `A_-=-U_{-a/2}(I-U_a)`: U_{-a/2}−U_{-a/2}U_a=U_{-a/2}−U_{a/2}, negate → U_{a/2}−U_{-a/2}. Exact.
- 2delta<a ⇒ disjoint lobes ⇒ ‖A_-h‖²=2‖h‖² (cross term 0), C_{A_-h}(a)=−‖h‖² (only the
  −|h(x+a/2)|² term survives). Exact.
- −1 eigenspace of the lobe swap: under L²(I_-)⊕L²(I_+)≅L²(−δ,δ)², A_-h ↦ (−h,h), which the swap
  negates; the closure is that whole graph. CORRECT (the "swap" is the translate-by-a exchange,
  not a bare coordinate swap — the verdict's own identification says so; no consequence).
- NOT the −1 eigenspace of U_a on the line: U_a has no L² eigenvector (periodic modulus). CORRECT.
- (3) A_±(v_θ)=(e^{±a/4}+e^{iθ}e^{∓a/4})A_±(h)/√(2H), from A_±(U_ch)=e^{±c/2}A_±(h).
  **Numerically verified** (chk1.py, random complex h = deg-5 complex polynomial × bump, δ=0.15,
  θ=0, 0.7, π, 2.3): |A_± num − A_± formula| ≤ 1.6e-16; ‖v_θ‖²=1.000000000000000 at every θ.
- |e^{a/4}|=1.1892 ≠ |e^{−a/4}|=0.8409 ⇒ numerator never vanishes for real θ ⇒ v_θ pole-null ⟺ h
  pole-null. CORRECT. Even positive h in the minus phase: A_+=−A_-, P_02=−8sinh²(a/4)m²<0. CORRECT.
- (4) h=(∂²−1/4)η_δ pole-null (two integrations by parts); (∂²−1/4) injective on C_c^∞ (solutions
  e^{±x/2} not compact) ⇒ infinite-dimensional. CORRECT.

## 2. Lemma 2 — CORRECT; (5) and (6) numerically confirmed

- a_inf(t)=e^{−t/2}/(1−e^{−2t})=Σ_j e^{−(2j+1/2)t}. CORRECT.
- (5): ∫e^{−βs}C_h(s)ds=(∫he^{βx})(∫he^{−βx})=|∫he^{βx}|² **for real even h** (evenness is what makes
  it a square, hence J_a≥0; the lemma does assume real even). CORRECT.
- (6): C_v(t)=C_h(t)/H+cosθ[C_h(t−a)+C_h(t+a)]/(2H), re-derived term by term; on t>0 only C_h(t−a)
  survives (2delta<a) and C_v(ja)=0 for j≥2 (a+2delta<2a). Hence D(v_θ)=D(h)/H−J_a cosθ,
  C_{v_θ}(a)=cosθ/2, prime sum = w cosθ (w=a/√2), L_2(v_θ)=A_0−(J_a+w)cosθ. CORRECT.

h=(∂²−1/4)η_{δ_0} (chk2.py, chk3.py):

| quantity | value |
|---|---|
| H=‖h‖² | 1.6434228127646e8 |
| j=0 term of (5) | 1.285e-25 (**vanishes**) |
| j=1 term of (5) | 6.380133420775 (**strictly positive**) |
| Σ_j of (5) | 75.53479759015 |
| **J_a(h), series (5)** | **4.5961877250010e-07** |
| J_a(h), t-integral | 4.5961877250673e-07 (rel diff 1.4e-11) |
| D(v_0), direct t-integral of FFT autocorrelation | 8.809289557 |
| D(v_π), same | 8.809290476 |
| **D(v_0)−D(v_π)** | **−9.192375e-07** |
| −2J_a | −9.192375e-07 (ratio 1.000000006) |

**J_a(h)>0 strictly**; j=0 vanishes, j=1 positive, exactly as claimed. The three pole-null phases do
**not** share an archimedean energy: the split is 9.2e-7 against D≈8.81, i.e. 1.0e-7 relative —
below the rounding of a printed table. Grid-converged at N=2^19,2^20,2^21 (7 digits).
This scores the judge's own `P_PHASE_ARCHIMEDEAN_CROSS_TERM_RESOLVED` (p=0.95) TRUE.

## 3. (7) HS-square expansion — CORRECT

n(v_θ)=[2‖Z‖²+2Re(e^{iθ}⟨U_{a/2}Z,U_{−a/2}Z⟩)]/(2H)=n_0+ν_a cosθ (mixed term real for real h);
|ν_a|≤n_0 by Cauchy–Schwarz with ‖U_{±a/2}Z‖=‖Z‖. e=n−L_2 gives (7). (8) is exactly e(v_π)≤0, and
for pole-null h P_02(v_π)=0 so e(v_π)≤0 ⟺ Q(v_π)≥n(v_π). All CORRECT. Scope (stated by the verdict,
not an error): (8) is the real-even slice; R1- quantifies over complex h, where a sine term appears.

## 4. (13)–(14) plant — CORRECT; delta_M = 0.0208661771221494

- Zeros of M_2(s)=(1−2^{3/4−s})(1−2^{−1/4+s}): s=3/4+2πik/a and s=1/4+2πik/a, i.e. centered
  **±d+2πik/a with d=1/4**. Numerically: |M|≤6.6e-31 at four lattice points, M(1/2)=0.03580;
  M(1−s)=M(s) verified; the parent's (23) log-derivative series matches to 2.5e-32 at s=2.3+0.4i.
- (13) re-derived independently by Poisson: with V(z)=∫ve^{zx}, the two lattices give
  Σ_k 2Re[V(d+2πik/a)conj(V(−d+2πik/a))] = aΣ_m 2ReΦ(ma), Φ(x)=e^{dx}∫conj(v)v(·+x),
  = 2a‖v‖²+4aΣ_{j≥1}cosh(dja)C_v(ja). A **second** route (coefficients p^{3j/4}+p^{j/4}=
  p^{j/2}2cosh(jd log p) fed through the rule that produces −2Σlog p·p^{−j/2}C_v in L_S) gives the
  same, j=0 mass 2a included. **Numerically** (chk4c.py, explicit 3-bump v): lattice sum |k|≤800 =
  1.5679514974 vs formula 1.5679514974, rel diff 2.8e-15. CORRECT.
- For v_θ only j=1 survives ⇒ Q_M(v_θ)=2a+2a cosh(a/4)cosθ; at θ=π, Q_M=−delta_M, so
  e_sharp(v_-)=e(v_-)+delta_M, **delta_M=2a(cosh(a/4)−1)=0.0208661771221494**,
  cosh(a/4)=1.01505176512822. CORRECT.

## 5. Theorem 3 — CORRECT in all four parts

- (16) as multipliers, z=e^{−iτa}: (1−rz)/(1−rz^{−1})=(1−r²)/(1−rz^{−1})−rz, one line. Verified at
  τ=0.3,1.7,−4.2,11 to ≤1.2e-31; |multiplier|=1 (U_p unitary; F_∞U_pF_∞=U_p^* gives the involution).
- (18) **derived independently**: from v(x)=u^{1/2}f(u), U_{−ja}: f(u)↦p^{j/2}f(p^ju), so
  U_{−ja}F_∞ has kernel 2p^{j/2}cos(2πp^juv) and the weight (1−r²)r^j·p^{j/2}=(1−1/p) — the r_p^j
  **does** cancel against the Jacobian, as claimed; last term −r·p^{−1/2}·2cos(2πuv/p)=−(2/p)cos(2πuv/p).
- Non-HS resonance: hat(chi·Sigma)(2πp^k)=(1/2)∫chi+(1/2)chi^(4πp^k)+ nonresonant terms whose
  arguments are ≥2πp^k(1−1/p) ⇒ O(kp^{−kM}) for j<k, O(Σ_{j>k}p^{−jM}) for j>k. **Numerically**
  (chk6b.py, ∫chi=1): 0.51435 (k=4), 0.49861, 0.50009, 0.500005, 0.49999986, 0.50000000 (k=9,10,11).
  CORRECT.
- **Implication direction is right**: HS ⇒ L² kernel on (0,λ)² ⇒ locally L² on an interior rectangle
  ⇒ (change (u,v)→(u,uv), bounded Jacobian away from the axes, Fubini) Sigma∈L²_loc ⇒ chi·Sigma∈L¹
  ⇒ Riemann–Lebesgue contradiction. The verdict contraposes the correct direction. CORRECT.
  Corroboration: H_J²=‖A^{(J)}‖²_HS = 0.4050, 0.9600, 1.6344, 2.2886, 3.4687(J=5), 5.0521(J=8),
  7.0691(J=12), increment → 0.5 = 2c_j²I_λ(0) per new frequency. Consistent with, not a proof of, non-HS.
- (19): weighted j-th block has op-norm ≤r^j and HS-norm ≤2λ (its kernel is exactly 2cos(2πp^juv));
  interpolation ‖T‖_{S_q}≤‖T‖^{1−2/q}‖T‖_{S_2}^{2/q} sums to B_q=(2λ)^{2/q}[(1−r²)/(1−r^{1−2/q})+1]
  (the "+1" over-bounds r^{1+2/q}). B_q(2,1)=14.741 (q=2.5), 8.862 (3), 5.859 (4), 3.521 (10).

## 6. Theorem 4 — CORRECT; no gap found; reference confirmed

- Trace-class lemma: the off-diagonal blocks of [C_h,P_b] have kernels ±h(±(s+t)), s,t>0 (Hankel).
  Unit-square partition + two integrations by parts per variable in a cosine basis gives coefficients
  O(k^{-2}l^{-2}) times rapid decay in the block index n+m; Σ_{n,m}(1+n+m)^{-M}<∞ for M>2, and
  Σ|c_{kl}| bounds each block's trace norm. Valid; retained boundary terms carry the same decay.
- **Reference confirmed**: 2006.13771 App. D, Lemma D.1, pp.51–52 — for f∈S(Ĉ), [H,f] is an
  infinitesimal of infinite order, hence trace class; the proof reduces to PK(1−P) with K a
  convolution with Schwartz kernel and P a sharp half-line projection, and Remark D.2 offers the
  direct Schwartz-kernel estimate, i.e. the verdict's own proof. Citation accurate.
- F_p=C_mR, RP_bR=I−P_{−b} ⇒ F_pP_bF_p=I−C_mP_{−b}C_m^*, so R_0=C_mP_{−b}C_m^*−P_b=
  [C_m,P_{−b}]C_m^*+(P_{−b}−P_b); (20) checked by expansion. hat(f)·m Schwartz (gamma quotient smooth
  with polynomially bounded derivatives; Euler factor bounded since 1−r_p>0). CORRECT.
- Archimedean: 2cos(2πuv) Taylor-expands into rank-ones with trace norms summing to 2λcosh(2πλ²);
  D_∞ trace class; S_∞=R_∞+D_∞; T_fS_p=B(T_fS_∞)G^{-1}S_∞B^* since T_f commutes with B;
  T_fD_S=T_fS_p−T_fR_0. CORRECT. The absolute-convergence corollary uses Σ_n|⟨e_n,Xe_n⟩|≤‖X‖_1. CORRECT.
- Inherited premises, UNVERIFIABLE here: S_p=BS_∞G^{-1}S_∞B^* (parent Lemma 4 via CCM23 Thm 4.13)
  and the imported C26 (22) trace identity.

## 7. Lemma 5 (21) — CORRECT

- R_p−R_∞=Q_∞−CQ_∞C^*; conjugating by F_∞ (F_∞T_fF_∞=T_{f~}, F_∞CF_∞=C^*) gives Tr(T_{f~}(P−C^*PC))
  and P−C^*PC=[P,C^*]C. CORRECT.
- Elementary trace: [P,U_d]U_e=(P−U_dPU_{−d})U_{d+e}; P−U_dPU_{−d}=1_{x≤0}−1_{x≤d}, integral −d;
  diagonal kernel f(−d−e); Tr=−d f(−d−e). CORRECT.
- c'/c=2ia_pΣ_{j≥1}r_p^j cos(ja_pτ) by direct differentiation. The Fourier form and the elementary sum
  agree because Σ_{d+e=s}γ_dε_e=δ_{s,0} (C^*C=I). **Numerically** (chk5.py, J=90 shifts, two-Gaussian
  f): −0.8637962298104191 and −0.8637962298104211 vs closed form −0.8637962298104214 (2e-15).
- Tail (1+r)r^{J+1}(1+a(J+1)+ar/(1−r)) reproduces Σ_{j>J}(1−r²)r^j(1+ja) exactly:
  J=5 1.4579307339, J=10 3.8846296805e-1, J=20 2.0310392185e-2 (both sides identical).
- **Cross-check the verdict does not make explicit**: with f=k_v*k_v^*, (21) equals
  −2Σ_j(log2)2^{−j/2}C_v(jlog2) — exactly the prime-2 term of L_S in the parent's (14), right sign
  and coefficient. Two independent routes agree.

## 8. (22)–(25) — CORRECT

- s_n≤B_q n^{−1/q} from n·s_n^q≤Σs_m^q; every β<1/2 is an upper exponent, no β>1/2 can be (Σs_n²=∞).
- (23): rho_J≤tau/10 ⟺ J+1≥log(10(1+r)/tau)/log(1/r). (24): Weyl, both inclusions correct.
- (25): n_λ(tau)≤#{s_n(A^{(J)})>tau−rho_J}≤H_J²/(tau−rho_J)². CORRECT.
- I_λ(t)=Si(2πtλ²)/(2πt), I_λ(0)=λ²: vs dblquad at t=0,1,3,7 → 1.000000000000 / 0.225705833395 /
  0.080534202916 / 0.035197872098 (12 digits). H_J² reproduces a direct grid HS norm (J=0,2,5:
  0.405037/0.405036, 1.634384/1.634383, 3.468652/3.468649). CORRECT.
- Worked numbers (p=2, λ=1): tau=1e-2 → J=21, rho_J=8.34e-4, H_J²=11.571, n_λ≤1.38e5;
  5e-3 → J=23, H_J²=12.571, n_λ≤5.98e5; 2.5e-3 → J=25, H_J²=13.571, n_λ≤2.58e6. Since H_J²≈0.5J,
  the bound carries an extra log(1/tau) over tau^{−2} — worth knowing before budgeting, not an error.
- The remark on the observer's grid rank floor(λ√(2N))+1 is UNVERIFIABLE here (no table read).

## 9. §1 scoring repair — CORRECT

Yes: P1 registered P_SIGN_HOLDS_ON_TABLE for support-matched **pole-null** tests and added the guard
"Raw positive bumps and canonical cutoffs are NOT substituted for pole-null tests when scoring
P_SIGN_HOLDS_ON_TABLE", so non-pole-null bumps and the canonical quintic cutoffs fall outside the
frozen event's class and can only leave it UNRESOLVED.

## Verdict on the RESULT codes

No error found that touches any RESULT code. Every derivation I could redo (items 1–8) is correct,
and five were confirmed by an independent computational route: the random-h check of (3); the
FFT-autocorrelation D(v_0)−D(v_π) against the series (5); the Poisson lattice sum against (13); the
lacunary resonance limit; the elementary shift-trace against (21). Q1/Q3
PARTIAL_WITH_PRECISE_REMAINDER and Q2 PROVED_ON_CLASS stand as stated. Residuals are inherited, not
defective: parent Lemma 4 (S_p=BS_∞G^{-1}S_∞B^*, via CCM23 Thm 4.13) and the imported C26 (22)
identity are premises here; all statements about tables TA/TB/TC are UNVERIFIABLE from this desk.
Two presentational nits with no consequence: "one-prime Fourier involution" in Theorem 3 is the
semilocal S={∞,p} involution U_pF_∞, and (8) is the real-even slice of the complex class R1-
quantifies over — both are stated correctly elsewhere in the same document.
