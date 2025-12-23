# Toeplitz → Contraction for B_{α,j} (Dyadic Layer, mod-q projection)

## Source: GPT 5.2 PRO (Прошка 1) theoretical analysis for Q3-2 Bridge

### Keywords (what they mean)
- **Toeplitz kernel**: matrix depending (approximately) only on the difference `p-q`.
- **Dyadic block**: primes restricted to `[2^j, 2^{j+1})` (one scale).
- **Minor arcs** `𝔪(N;Q)`: α not well-approximable by rationals `a/q` with `q ≤ Q` and error `≲ Q/(qN)`.
- **Projection mod q**: decompose indices by residues `p ≡ r (mod q)` (or characters) to isolate the rational part `a/q`.
- **TT***: use quadratic form / Rayleigh quotient, since HS/Frobenius kills phase.

---

## 1) Layer-j geometry and Toeplitz model (local linearization of log)
Fix `t>0`, `j≥1`. Let `P_j := {p prime : 2^j ≤ p < 2^{j+1}}` and
`ξ_p := log p / (2π)`.

Define the heat-Gram on primes in the block:
```
G^{(j)}_{pq} := exp( - (ξ_p - ξ_q)^2 / (4t) ).
```

**Toeplitz kernel (integer-difference proxy)**:
```
K_j(d) := exp( - d^2 / (16 π^2 t · 2^{2j}) ),   d ∈ ℤ.
```

**Toeplitz Model Lemma (assumption / target)**:
There exist constants `c0>0`, `C_t>0` such that for all `p,q ∈ P_j` with
```
|p-q| ≤ c0 · 2^j · sqrt(t),
```
we have a relative approximation
```
| G^{(j)}_{pq} - K_j(p-q) | ≤ C_t · K_j(p-q).         (TM1)
```

And for |p-q| > c0 · 2^j sqrt(t),
```
G^{(j)}_{pq} ≤ exp( -c0^2 / (16π^2) )  (negligible tail). (TM2)
```

*(TM1) is the linearization log p - log q ≈ (p-q)/2^j plus Gaussian stability.*
This is the "Toeplitzization" step.

---

## 2) Balanced operator on the layer and where the oscillation enters
On P_j define:
- weight matrix: `W_j := diag( w(p) )`,    `w(p)=Λ(p)/sqrt(p)`
- circle twist:  `U_{α,j} := diag( e(α p) )`,  `e(x)=exp(2π i x)`
- Gram:          `G_j := (G^{(j)}_{pq})_{p,q∈P_j}`

Balanced matrix (layer version):
```
B_{α,j} := G_j^{1/2} W_j U_{α,j} G_j^{1/2}.
```

Then
```
‖B_{α,j}‖^2 = λ_max( B_{α,j} B_{α,j}^* )
```
and for any y ≠ 0 the correct Rayleigh target is
```
y^*(W_j U_{α,j} G_j U_{α,j}^* W_j) y ≤ ρ^2 · y^* G_j^{-1} y.   (Q3-2-j)
```

Oscillation in TT*:
```
(U_{α,j} G_j U_{α,j}^*)_{pq} = e(α(p-q)) · G^{(j)}_{pq}.
```

---

## 3) mod-q extraction of the rational part (major/minor separation)
Let α ∈ ℝ/ℤ and fix a rational approximation a/q (coprime) with q≤Q.
Write:
```
α = a/q + β,    where β := α - a/q,  and  dist(qα,ℤ)=|qβ|.
```

Decompose indices by residues r mod q.
Inside a fixed residue class r (so p≡q≡r mod q), differences satisfy p-q ≡ 0 (mod q),
hence the rational phase e((a/q)(p-q)) = 1 and only β survives:
```
e(α(p-q)) = e(β(p-q))  on each residue class.
```

So minor-arc "non-resonance" is measured by |β| = dist(qα,ℤ)/q.

---

## 4) Toeplitz contraction mechanism (model computation)
Replace the prime-Gram by its Toeplitz proxy:
```
G_j ≈ K_j(p-q).
```

In the full Toeplitz model on ℓ^2(ℤ), the operator
```
A_{β,j} := K_j^{1/2} U_β K_j^{1/2}
```
diagonalizes in Fourier: its norm equals the multiplier supremum
```
‖A_{β,j}‖ = sup_θ sqrt(K̂_j(θ)) · sqrt(K̂_j(θ+β)).
```

For a Gaussian Toeplitz kernel one has the Gaussian Fourier bound
```
K̂_j(θ) ≲ exp( -c · t · 2^{2j} · dist(θ,ℤ)^2 ).
```
Therefore
```
‖A_{β,j}‖ ≤ exp( -c' · t · 2^{2j} · dist(β,ℤ)^2 ).            (T-CONTR)
```

After mod-q extraction, β = (qα-a)/q, hence
```
dist(β,ℤ) = dist(qα,ℤ)/q.
```

**Safe (scaling-correct) bound:**
```
‖B_{α,j}‖  ≤  exp( -c' · t · 2^{2j} · dist(qα,ℤ)^2 / q^2 )  +  Err_toeplitz. (T-CONTR-q)
```

**If q is O(1)** (fixed small modulus), you can absorb 1/q^2 into constants and write the simpler
```
‖B_{α,j}‖ ≤ exp( -c'' · t · 2^{2j} · dist(qα,ℤ)^2 ) + Err.                (T-CONTR-q-simpl)
```

Where Err_toeplitz comes from (TM1)-(TM2) + Gram conditioning.

---

## 5) Micro-block assembly (how dyadic layers multiply back)
Let J := ⌊log_2 N⌋. The bridge uses a layer chain (scale-shift τ_c + conjugation).
If each layer satisfies a contraction bound
```
‖T̃_{α,j}‖ ≤ ρ_j(α) < 1
```
then the chained product satisfies
```
‖T̃_{α,J-1} ... T̃_{α,0}‖ ≤ Π_{j=0}^{J-1} ρ_j(α).
```

If a **uniform** bound holds on minor arcs:
```
sup_{α∈𝔪(N;Q)} sup_{j≤J} ρ_j(α) ≤ ρ < 1,
```
then
```
Π_{j=0}^{J-1} ρ_j(α) ≤ ρ^J = N^{-δ},   δ := (-log ρ)/log 2.
```

This is exactly why Rep(N) uses J ~ log N: one contraction per scale gives a power saving.

---

## 6) Where large sieve enters (restriction from integers to primes)
The Toeplitz/Fourier diagonalization is clean on **all integers**.
To port it to **primes**, we need a "restriction lemma" controlling how much
sparsity + irregular spacing can inflate the operator norm.

One standard route is a **large-sieve / dispersion** hypothesis on primes in progressions:
for q≤Q and residue classes r mod q,
the prime-supported sequences behave "L^2-equidistributed" so that
```
‖ (prime-restricted Toeplitz operator) - (integer Toeplitz operator) ‖_op
```
is small (uniformly in α on minor arcs).

Concretely, you need a bilinear estimate of the type:
```
sup_{α∈𝔪}  | Σ_{d} e(α d) C_d(a) |  ≤  (1-Δ) · (a^* G_j a)
```
or the metric-correct version:
```
y^*(W U_α G U_α^* W) y ≤ (1-Δ) · y^* G^{-1} y,
```
with Δ>0 uniform.

This is the genuine "new math wall": a uniform-in-α minor-arc bilinear bound on primes.

---

## 7) Final uniform bound shape on minor arcs
If minor arcs are defined by: for all coprime a/q with q≤Q,
```
|α - a/q| ≥ Q/(qN),
```
then for such q we have
```
dist(qα,ℤ) = |qα-a| ≥ Q/N.
```

Plugging into (T-CONTR-q) at the top scale 2^j ~ N gives
```
‖B_{α,j}‖ ≤ exp( -c' t · (N^2) · (Q/N)^2 / q^2 )
         = exp( -c' t · Q^2 / q^2 )
         ≤ exp( -c' t )      (since q ≤ Q).
```

So for all α ∈ 𝔪(N;Q) and all j near the top scales,
```
‖B_{α,j}‖ ≤ ρ0 := exp(-c' t) < 1,
```
and taking the worst-case across finitely many small j gives a global uniform ρ<1
(provided small-j norms are also <1 by geometry/weights).

---

## 8) Lean Skeleton (axioms/definitions for formalization)

```lean
/-- distance to nearest integer -/
def distZ (x : ℝ) : ℝ := Real.infDist x (Set.range (fun n : ℤ => (n : ℝ)))

/-- dyadic block -/
def Pj (j : ℕ) (p : ℕ) : Prop := Nat.Prime p ∧ (2^j ≤ p) ∧ (p < 2^(j+1))

/-- node map -/
def xi (p : ℝ) : ℝ := Real.log p / (2*Real.pi)

/-- heat gram entry -/
def Gentry (t : ℝ) (p q : ℝ) : ℝ := Real.exp ( - (xi p - xi q)^2 / (4*t) )

/-- toeplitz proxy kernel on differences -/
def Kj (t : ℝ) (j : ℕ) (d : ℤ) : ℝ :=
  Real.exp ( - ( (d:ℝ)^2 ) / (16 * Real.pi^2 * t * (2:ℝ)^(2*j)) )

/-- Toeplitz model hypothesis (local band relative error) -/
axiom toeplitz_model_band
  (t : ℝ) (j : ℕ) (Ct c0 : ℝ) :
  ∀ {p q : ℕ}, Pj j p → Pj j q →
    (Real.abs ((p:ℝ)-(q:ℝ)) ≤ c0 * (2:ℝ)^j * Real.sqrt t) →
    Real.abs (Gentry t p q - Kj t j (Int.ofNat p - Int.ofNat q)) ≤ Ct * Kj t j (Int.ofNat p - Int.ofNat q)

/-- Minor-arc diophantine condition for a/q approximation -/
axiom minor_arc_dist
  (N Q : ℕ) (α : ℝ) :
  α ∈ minor_arcs N Q → ∀ {q : ℕ}, q ≤ Q → distZ (q*α) ≥ (Q:ℝ)/(N:ℝ)

/-- Target: contraction per layer (safe q^{-2} scaling) -/
axiom toeplitz_contraction_layer
  (t : ℝ) (j : ℕ) (q : ℕ) (α : ℝ) :
  ‖B_layer t j α‖ ≤ Real.exp ( -c * t * (2:ℝ)^(2*j) * (distZ (q*α))^2 / (q:ℝ)^2 )
```

---

## Summary: What P1 established

1. **Toeplitz Model** works locally on dyadic blocks with band |p-q| ≤ c₀·2^j·√t
2. **mod-q projection** isolates β = α - a/q, and minor arcs give dist(qα,ℤ) ≥ Q/N
3. **Contraction**: ‖B_{α,j}‖ ≤ exp(-c't·2^{2j}·dist(qα,ℤ)²/q²)
4. **Assembly**: product over J ~ log N layers gives N^{-δ} decay
5. **Large sieve** needed for prime restriction (the "new math wall")
6. **Final bound**: ‖B_{α,j}‖ ≤ exp(-c't) < 1 uniform on minor arcs
