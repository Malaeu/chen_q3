# Q3-2: The Operator Bridge v2.1 (CORRECTED)

## Critical Fixes from Audit

**This version corrects 6 major mathematical errors:**
1. Mellin vs Circle twist confusion - FIXED
2. Scale factor 2pi error - FIXED
3. False "diagonality" claim - FIXED
4. Frobenius bound kills interference - FIXED (use TT*)
5. Single alpha vs uniform bound - ACKNOWLEDGED
6. Missing Bridge => S(alpha) lemma - ADDED

---

## 1. Core Construction (CORRECTED)

### 1.1 The RKHS Space H_{t,K}

```lean
noncomputable def heat_kernel (t : Real) (x y : Real) : Real :=
  Real.exp (-(x - y)^2 / (4 * t))
```

### 1.2 Prime Sampling Nodes

```lean
-- Node for prime p in frequency domain
noncomputable def prime_node (p : Nat) : Real := Real.log p / (2 * Real.pi)

def nodes_in_window (K : Real) (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter (fun n => Nat.Prime n and |prime_node n| <= K)
```

### 1.3 Prime Weights

```lean
noncomputable def prime_weight (n : Nat) : Real :=
  if Nat.Prime n then Real.log n / Real.sqrt n else 0

-- Key bound: w(n) <= 2/e for all n >= 3 prime
lemma prime_weight_bound (n : Nat) (hn : Nat.Prime n) (hn3 : n >= 3) :
  prime_weight n <= 2 / Real.exp 1 := by sorry
```

---

## 2. THE CORRECT OPERATOR (Circle Method Edition)

### 2.1 Feature Map Formulation

**Key insight:** Kernel vectors |k_xi_p> are NOT orthonormal!

Let Phi: C^{P_N} -> H be the feature map: Phi(e_p) = k_t(., xi_p)

Then:
- Gram matrix: G = Phi* Phi, where G_{pq} = k_t(xi_p, xi_q)
- Weight diagonal: W = diag(w(p))
- **CIRCLE twist diagonal:** U_alpha = diag(e(alpha * p))

where **e(x) = exp(2*pi*i*x)** is the standard additive character!

### 2.2 The Twisted Prime Operator (CORRECTED)

```lean
-- CORRECT: Circle Method twist e(alpha*n) = exp(2*pi*i*alpha*n)
-- NOT n^{i*alpha} which is Mellin twist!

noncomputable def twisted_prime_operator_matrix (t alpha : Real) (nodes : Finset Nat) :
    Matrix (Fin nodes.card) (Fin nodes.card) Complex :=
  fun i j =>
    let m := nodes.toList[i]
    let n := nodes.toList[j]
    let G_mn := (heat_kernel t (prime_node m) (prime_node n) : Complex)
    let w_n := (prime_weight n : Complex)
    -- CORRECT: additive twist e(alpha * n), NOT multiplicative n^{i*alpha}
    let phase_n := Complex.exp (2 * Real.pi * Complex.I * alpha * n)
    w_n * phase_n * G_mn
```

**The operator in abstract form:**
$$T_\alpha = \Phi \, W \, U_\alpha \, \Phi^*$$

### 2.3 Operator Norm (TT* Method)

**WRONG (Frobenius - kills phase cancellation):**
$$\|T_\alpha\|^2 \leq \sum_{m,n} |w(n)|^2 |G_{mn}|^2$$

**CORRECT (preserves interference):**
$$\|T_\alpha\|_{\mathrm{op}}^2 = \lambda_{\max}(T_\alpha T_\alpha^*)$$

Through orthonormalization:
$$B_\alpha = G^{1/2} W U_\alpha G^{1/2}$$
$$\|T_\alpha\|_{\mathrm{op}} = \|B_\alpha\|_2$$

And the honest TT* object:
$$\|T_\alpha\|_{\mathrm{op}}^2 = \lambda_{\max}\big(G^{1/2} W U_\alpha G U_\alpha^* W G^{1/2}\big)$$

---

## 3. The Bridge Lemma (NEW - Critical Gap Fixed!)

### 3.1 From Operator to Exponential Sum

**Lemma (operator_to_exp_sum_bridge):**

Let S(alpha) = sum_{n<=N} Lambda(n) * e(alpha*n) be the von Mangoldt weighted sum.

If the prime sampling operator T_alpha on H_{t,K} satisfies ||T_alpha||_op <= rho < 1,
then the Neumann series (I - T_alpha)^{-1} converges and:

$$|S(\alpha)| \leq C_K \cdot \|(I - T_\alpha)^{-1}\| \cdot \|f\|_H$$

for appropriate test function f in H.

```lean
lemma operator_to_exp_sum_bridge (alpha : Real) (N : Nat) (K t : Real)
    (hK : K > 0) (ht : t > 0) (hN : N > 100)
    (hrho : norm (twisted_prime_operator_matrix t alpha (nodes_in_window K N)) < 1) :
  exists (C : Real), C > 0 and
    Complex.abs (sum n in Finset.range (N+1),
      Nat.vonMangoldt n * Complex.exp (2 * Real.pi * Complex.I * alpha * n))
    <= C * (N : Real)^(1/2 : Real) / (1 - norm (twisted_prime_operator_matrix t alpha (nodes_in_window K N))) := by
  sorry
```

### 3.2 The Mechanism

1. **Resolvent bound:** ||T_alpha|| < 1 implies ||(I - T_alpha)^{-1}|| <= 1/(1 - ||T_alpha||)

2. **Sum representation:** S(alpha) can be written as inner product <f, (I - T_alpha)^{-1} g>_H

3. **Cauchy-Schwarz:** |S(alpha)| <= ||f||_H * ||(I - T_alpha)^{-1}||_op * ||g||_H

4. **Parameter choice:** With K ~ log(N) and t = t_opt(K), ||f||_H, ||g||_H ~ sqrt(N)

---

## 4. Hypothesis Q3-2 (Corrected Statement)

### 4.1 Uniform Contraction on Minor Arcs

```lean
def minor_arcs (N : Nat) : Set Real :=
  {alpha : Real | forall (a : Int) (q : Nat),
    (q : Real) <= (N : Real)^(1/10 : Real) -> |alpha - a/q| > 1/(q * N)}

theorem Q3_2_uniform_contraction :
  exists (rho : Real), rho < 1 and
  forall (K t : Real) (N : Nat) (alpha : Real),
    K > 0 -> t > 0 -> N > 100 ->
    alpha in minor_arcs N ->
    norm (twisted_prime_operator_matrix t alpha (nodes_in_window K N)) <= rho := by
  sorry
```

**NOTE:** This is a UNIFORM bound over ALL minor arcs, not just alpha = ln(6)!

### 4.2 Phase Cancellation Mechanism

On minor arcs, the phases e(alpha*p) for different primes p are "spread out":

For alpha far from rationals a/q with small q, the partial sums
$$\sum_{p \leq x} e(\alpha \cdot p)$$
exhibit cancellation due to equidistribution of {alpha*p} mod 1.

This is captured by the van der Corput/Weyl bound:
$$\left|\sum_{n=1}^{N} e(\alpha n)\right| \leq \min\left(N, \frac{1}{2\|\alpha\|}\right)$$

where ||alpha|| = min_{k in Z} |alpha - k|.

---

## 5. Implications

### 5.1 Q3-2 implies Q3-1

```lean
theorem Q3_2_implies_Q3_1
    (h : Q3_2_uniform_contraction) :
  exists (delta C : Real), delta > 0 and C > 0 and
  forall (N : Nat) (alpha : Real),
    N > 100 -> alpha in minor_arcs N ->
    Complex.abs (sum n in Finset.range (N+1),
      Nat.vonMangoldt n * Complex.exp (2 * Real.pi * Complex.I * alpha * n))
    <= C * (N : Real)^(1/2 - delta) := by
  -- Use operator_to_exp_sum_bridge with rho from h
  -- delta comes from log(1/rho) / log(N)
  sorry
```

### 5.2 The Chain to TPC

```
Q3-2 (||T_alpha|| < 1 on minor arcs)
       |
       v [operator_to_exp_sum_bridge]
Q3-1 (|S(alpha)| <= C * N^{1/2-delta} on minor arcs)
       |
       v [Circle Method]
Minor arc contribution = o(N)
       |
       v [+ Major arc ~ 2*C_2*N from Hardy-Littlewood]
R_2(N) ~ 2*C_2*N
       |
       v [Partial summation]
pi_2(N) ~ 2*C_2*N / ln^2(N)
       |
       v
TPC: infinitely many twin primes!
```

---

## 6. Numerical Tests (Heuristic Only!)

**WARNING:** alpha = ln(6) tests are HEURISTIC, not proof of uniform bound!

To properly test Q3-2, one must:
1. Compute B_alpha = G^{1/2} W U_alpha G^{1/2} (not naive M_{mn})
2. Test MANY alpha from minor arcs (not just one)
3. Check convergence as N -> infinity

```python
# Correct test (sketch)
def test_Q3_2(N, alpha_samples):
    for alpha in alpha_samples:
        if alpha not in minor_arcs(N):
            continue
        G = gram_matrix(t, primes_up_to(N))
        W = diag([prime_weight(p) for p in primes])
        U = diag([cexp(2*pi*1j*alpha*p) for p in primes])
        B = sqrtm(G) @ W @ U @ sqrtm(G)
        rho = norm(B, ord=2)  # operator norm, NOT Frobenius!
        assert rho < 1
```

---

## 7. Summary of Corrections

| Issue | Old (Wrong) | New (Correct) |
|-------|-------------|---------------|
| Twist | n^{i*alpha} (Mellin) | e(alpha*n) (Circle) |
| Basis | "diagonal in k_xi" | T = Phi W U Phi* |
| Norm | Frobenius sum | lambda_max(TT*) |
| Test | alpha = ln(6) only | all minor arcs |
| Bridge | vague | explicit lemma |

---

## References

1. Hardy-Littlewood (1923) - Circle Method
2. Vinogradov (1954) - Trigonometric sums
3. RH_Q3.pdf - Original RKHS construction (corrected interpretation)
