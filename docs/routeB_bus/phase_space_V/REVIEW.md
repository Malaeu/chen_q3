# Independent review of the phase-space V implementation

Scope: formulas, normalization, and finite-control interpretation only.
Source: Proshka commit `f73901ce86043a9aa98c3882497a405c58c0a146`,
`docs/routeB_bus/proshka/PROSHKA_VERDICT_PHASE_SPACE_V_2026-11-02.md`.
Reviewed local `v_forms.py` and `shake.py`. No cofinal bound, Lyapunov law,
RH implication beyond the inherited consumer, or interval certification is asserted.

## Formula verdicts

**CONFIRMED — physical basis and correlations.**
The physical orthonormal basis is

`φ_n(x)=d_n(−1)^n cos(2πnx/L)/√L`, `|x|≤L/2`,
`d_0=1`, `d_n=√2 (n>0)`, extended by zero.
With `y=x/L+1/2`, this is exactly `d_n cos(2πny)/√L`.
Thus the shifted-y moments in the code already include the physical `(-1)^n`;
inserting another alternating sign would be incorrect.
For `0≤s≤L`, `q_even(s,i,k)` is the symmetrized correlation
`∫[φ_i(x)φ_k(x+s)+φ_k(x)φ_i(x+s)]dx`.
For `s>L`, that physical correlation is zero.

**CONFIRMED — positive archimedean energy, including the constant.**
With `j(s)=exp(−s/2)/(1−exp(−2s))`, the reference matrix is

`A_ik=∫₀ᴸ j(s)[2δ_ik−Q_ik(s)]ds + 2δ_ik∫ᴸ∞j(s)ds`.

In `v_forms.py:55`, off-diagonal entries are precisely `−∫j Q_ik`.
For diagonals, define
`I_n(L)=∫₀ᴸ [exp(s/2)(1−s/L)cos(2πns/L)−1]/sinh(s) ds`.
The diagonal formula is

`A_nn=c_*−C_WR(L)−I_n(L)+sinmom_n/(πn)`

(last term omitted at n=0), where
`c_*=γ+log(8π)+π/2` and `C_WR(L)=γ+log(4π tanh(L/2))`.
Its constant is correct because

`∫₀∞[2j(s)−1/sinh(s)]ds = ψ(1/2)−ψ(1/4)=log2+π/2`,

and both finite-L constant expressions have derivative `−1/sinh(L)`.
The infinite archimedean tail has therefore not been dropped by the finite-s
quadrature or absorbed into an unreported frequency cutoff.

**CONFIRMED — position energy and pole.**
The spatial matrix in `v_forms.py:57` is
`∫log(1+x²)φ_i(x)φ_k(x)dx`; the product-to-sum factor `d_i d_k/2` is correct.
It uses physical x, without division by L.
The pole vector in line59 is exactly

`p_n=<√2 cosh(x/2),φ_n>`
`=4√2 d_n L^(3/2)sinh(L/4)/(L²+16π²n²)`.

**CONFIRMED — source signs and balance on the even carrier.**
Writing `P=Σ_n Λ(n)n^(−1/2)Q(log n)`, the even full source is

`K=A−c_*I−P+ppᵀ`.

Consequently every unit exact eigenvector satisfies

`V=λ+c_*+<P>−|pᵀf|²+M_x`.

The plus sign of the pole in K and its minus sign in the V balance are correct.
The conversion from the earlier `j_+=exp(−5s/2)/(1−exp(−2s))` convention uses
`j−j_+=exp(−s/2)` and `c_0=4−c_*`; the even pole kernel is
`2cosh((x−y)/2)`. This recovers the earlier full continuum compensation.
The rank-one pole representation here is specific to the real even carrier;
it must not silently replace both pole sectors on general complex/odd tests.

## Independent sampled physical-integral check

Ran `python validate_forms_independent.py`: m=N=8, 90dps, GL48 per panel.
The reference uses direct physical-basis integration, an alternative
difference/sum-frequency antiderivative, and an independent infinite-tail
quadrature. It does not reuse `q_even` or the arch-moment formula as reference.
Entries checked: `(0,0),(0,1),(1,1),(1,3),(3,3),(3,8),(8,8)`.

Maximum sampled absolute discrepancies:

| Quantity | Discrepancy |
|---|---:|
| positive arch | `2.946e−90` |
| position matrix | `3.682e−91` |
| pole vector | `4.910e−91` |
| correlation at s/L=.13,.37,.91 | `4.910e−91` |

These are working-precision floating checks, not rigorous error bounds.
They provide a separate normalization check, not a full independent eigenpair audit.

## SHAKE interpretation and limits

**V itself is arithmetic-independent.** Its two fixed physical quadratic forms
contain no prime data. Arithmetic affects V only through the vector selected
by the source eigenproblem. Holding the vector fixed holds V fixed under SHAKE.
This is appropriate for an observable intended to diagnose confinement.

`shake.py` recomputes the minimum eigenvector after perturbing K, so it tests
an actual finite bottom of each perturbed matrix, rather than applying V to a
fixed baseline vector. Shifting `log(2^j)` to `j(log2+ε)` while holding weights
`log2/√(2^j)` fixed is a broken-arithmetic control, not another literal CCM cell.

The two edge conventions are different controls:

1. **Physical clipped:** a valid positive atomic measure perturbation coupled
   to the same zero-extended finite carrier. For m=2^J and positive ε, the atom
   at n=m has zero correlation both at L and after its shift beyond L.
2. **Analytic continuation:** a symmetric finite matrix obtained by evaluating
   the inside-window formula beyond its physical domain. For example
   `Q_00(L+δ)=−2δ/L`, while the physical correlation is zero there. It is not
   the restriction of that physical atomic-translation form.

For the endpoint atom alone their leading matrix difference is

`K_analytic−K_clipped = (2ω_m Jε/L) ddᵀ + O(ε²)`.

Both remain legitimate *labeled finite matrix controls*; only the clipped case
is a physical compact-carrier correlation control. Baseline source balance is
literal. The same algebraic balance survives in the continued matrix, but its
prime term must be called continued rather than literal physical correlation.

If broken bottoms retain modest V, this shows that modest finite V alone
does not distinguish the literal arithmetic source at those cells. If V rises,
the finite sensitivity is informative but does not prove a source-specific
cofinal bound. Neither outcome establishes or refutes the proposed dyadic
summable-drift law. Near-degenerate finite levels additionally require precision
and residual evidence, as in the root computation; this review adds no interval gate.
