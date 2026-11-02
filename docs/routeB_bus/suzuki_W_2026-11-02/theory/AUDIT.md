# Suzuki W: source, version and discretization audit

2026-11-02. Definition/source audit and independent algebra; no proof of the conjectural limit or RH. Numerical W built below is a Galerkin diagnostic until its convergence and operator-domain correspondence are controlled.

## Primary version pins

Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096. The actual primary HTML and PDFs were read, rather than relying on a secondary summary:

|version|Corollary1.6 target, with s=1/2−iz|stated convergence domain|source location|
|---|---|---|---|
|v1|z² ξ(s)/ξ'_s(s)|ordinary compact-uniform over C|[HTML](https://arxiv.org/html/2606.09096v1), lines214–218; [PDF](https://arxiv.org/pdf/2606.09096v1), p6, text lines465–473|
|v2|ξ(s)/(ξ(s)+ξ'_s(s))|ordinary compact-uniform over C|[HTML](https://arxiv.org/html/2606.09096v2), lines219–223|
|v3|ξ(s)/(ξ(s)+ξ'_s(s))|compact-uniform in Im z>0, with φ analytic there|[HTML](https://arxiv.org/html/2606.09096v3), lines220–224; [PDF](https://arxiv.org/pdf/2606.09096v3), p7, text lines472–479|

Thus the user's target is historical v1, not the current v3 target. V3 explicitly permits λ=λ(a)<λ_a and θ=θ(a). Its convergence hypothesis says “uniformly on every compact subset of the upper half-plane.” This is a conditional sufficient criterion; the limit is not proved by Theorem1.5. Section7's motivation assumes RH (v3 lines764–767).

## Operator and deficiency-vector contract

V3 definitions (1.9)–(1.10), HTML lines196–205; §6.2–6.4, lines712–741:

    λ_a=inf spec(A_a),  λ<λ_a,
    T_a=A_a−λI,
    ||v||_T²=Q_W(v)−λ||v||_L2²,
    H(T_a)=completion of C_c^∞(−a,a) in this norm,
    mathscr D_a=i d/dx on C_c^∞(−a,a), adjoint in H(T_a).

For e_z(x)=exp(−izx), the paper's Riesz vectors satisfy

    v_z=T_a^−1 e_z,
    mathscr D_a^* v_z=z v_z.

Therefore v_+∝T_a^−1 exp(+x), v_-∝T_a^−1 exp(−x), for the respective deficiency eigenvalues+i,−i. The user's exp(∓x) ordering swaps these labels for D=i d/dx. The transform convention is ∫v(x)exp(izx)dx. With ||v_+||_T=||v_-||_T, Theorem1.5 uses

    W(a,λ,θ;z)=(z−i)∫v_+(x)e^{izx}dx
                 +e^{iθ}(z+i)∫v_-(x)e^{izx}dx.

It is entire and its zeros are real for the exact operator construction (v3 lines203–208). θ parametrizes the self-adjoint boundary extension; it is not an extra spectral variable. Changing relative phases of v_± changes the numerical θ label. A common nonzero scale changes no zeros. V3 suggests θ=π as a natural limiting choice (line229); this is motivation, not a theorem fixing θ(a). Reflection-compatible real normalization gives a reproducible convention.

## Independent Galerkin translation

Let ψ_j be the **full**, both-parity physical basis; M_ij=<ψ_i,ψ_j>_L2 and K_ij=Q_W(ψ_j,ψ_i), with the sesquilinear convention used consistently. Let b_±,i=<ψ_i,exp(±x)>_L2. The weak resolvent equations are

    (K−λM)c_±=b_±.

In a physical orthonormal basis M=I. If T0 denotes the physical mass matrix in other coordinates, K−λT0 is correct there; replacing I by an unrelated covariance matrix changes the problem. If A_coord=M^−1K is used, its right-hand-side coefficient vector is M^−1b_±, not b_±. Equal energy normalization uses c_±^*(K−λM)c_±, not Euclidean coefficient norm.

Suzuki's P_a subtracts the mean in the **derivative/screw-G formulation**, not in T_a^−1 exp(±x) above. A P meaning ordinary Galerkin projection is appropriate when implemented by the loads b_±. A mean-zero or quiet-space projection is another problem. The derivative variable u=Dv instead has pencil G_a−λK_a with K_a=(−Δ_N)^−1; see v3 §8.5, lines1081–1091. This explains a nonidentity mass without changing the physical operator shift.

Parity is essential. Reflection-invariant T gives r_+=r_even+r_odd and r_-=r_even−r_odd. The two energy norms then agree. Even-only projection replaces both loads by cosh(x), loses the sinh component and does not compute the two deficiency vectors. The full source also retains the negative odd pole; the even-only positive pole formula cannot be reused for the odd block.

A finite sum of compactly supported modal transforms is entire. Its scalar W_N need not inherit the exact all-real-zero theorem: finite projection can destroy the differentiation/boundary-form identities used in that theorem. In particular, a spurious nonreal zero of W_N is a discretization discriminator, not a counterexample to Theorem1.5. Solving the finite equations accurately is necessary but does not establish the continuous deficiency equation.

## Independent admissible-shift bound

A Ritz minimum is an upper bound on the continuous form bottom. Consequently λ<λ_min(K,M) alone does **not** establish λ<λ_a. There is a coarse source bound that does: in the full parity space on[−a,a], write c*=γ+log(8π)+π/2 and

    B_a=c*+2Σ_{n≤exp(2a)}Λ(n)/sqrt(n)+2sinh(a)−2a.

The positive arch jump integral and even pole may be discarded for a lower bound; |Q_f(log n)|≤2||f||²; the negative odd pole has norm-square ||sqrt2 sinh(x/2)||²=2sinh(a)−2a. Thus Q_W(f)≥−B_a||f||² and any λ<−B_a is source-admissible. This elementary bound is independent of RH, but it does not justify λ=0 or a near-bottom asymptotic choice. A sharper admissibility claim needs its own lower estimate.

## Independent gauge and pole checks

Put X(z)=ξ(1/2−iz). The prime in the paper differentiates with respect to s, so ξ'_s(s)=i X'(z). The diagnostic targets are therefore

    H_v1(z)=−i z² X(z)/X'(z),
    H_v3(z)=X(z)/(X(z)+i X'(z)).

Confusing the s and z derivatives changes the phase or denominator, not just notation. Near0 the historical target vanishes, while H_v3(0)=1.

The historical H_v1 is meromorphic: derivative critical points between real zeros of real X yield genuine poles wherever X≠0. Its z² factor does not remove those nonzero poles. Ordinary locally uniform approximation on **all C** by finite holomorphic-gauged W cannot hold across genuine poles. Pole-deleted compact tests or spherical/meromorphic convergence would be modified questions, not the literal historical all-C wording. V1/v2 also do not explicitly impose the analytic-gauge hypothesis that v3 makes explicit. Use current v3 for the primary theorem-facing test, while retaining the requested historical target under an explicit label.

In v3, φ must be holomorphic on the entire upper half-plane for each admissible a; it need not extend to an entire function. exp(φ) is holomorphic and zero-free there. The exact W also has no upper-half-plane zeros. Thus a nonzero locally uniform limit is holomorphic and zero-free there by the standard uniform-limit/Hurwitz argument. A genuine target pole inside the domain obstructs ordinary compact-uniform convergence; a target zero there also obstructs a nonzero zero-free limit. These are global analytic requirements, not removable by changing a finite normalization constant.

On the other hand, on any simply connected patch where a chosen target and W are holomorphic and zero-free, φ=log(target/W) forces exact agreement. Fitting this φ to the target pointwise or on a grid is therefore tautological. A reproducible numerical probe must restrict and declare its normalization before testing, for example a scalar anchored at one fixed nonsingular point. Success in that restricted gauge is finite evidence only; failure cannot refute the corollary's unrestricted existential analytic φ. Neither a fitted φ nor an assumed λ=0 supplies the missing global limit.

## Independent fixed-shift limitation

W depends on λ (v3 line225); the paper's heuristic setting uses λ=0 and expects that choice eventually (line227 and §7). A fixed negative shift must not silently be treated as the same infinite-space construction. **Conditional on RH** and the full zero-side/Parseval representation, λ=−1 changes the norm to

    Q_W(f)+||f||²=Σ_gamma m_gamma |F(gamma)|²
                  +(1/(2π))∫_R |F(t)|²dt.

The extra term is continuous Lebesgue spectral weight. This conditional calculation explains why a fixed-shift finite experiment can probe a different limiting geometry; it does not establish an unconditional infinite-space representation, a particular zero-density law, or convergence of the computed W. Changing θ alone does not remove this metric change. An observed window-frequency spacing near2π/L would require comparison with its own baseline, not identification with zeta zeros by default.

## Repository-summary gap

The requested `claude/SUZUKI_EXTRACTION_2026-11-02.md` was not located at the supplied refs. Direct attempts covered root claude/, docs/claude/, docs/routeB_bus/claude/, and the mirrored closure/claude/ path; relevant root and routeB directory listings and the934-entry proshka subtree were inspected. Only older2026-09 Suzuki kernel reports were found there. Default-branch code search returned no extraction hit. This is a bounded search finding, not a claim that every historical branch was exhausted.

The exact K6(0.5,0.6) source likewise remains unlocated. The canonical fake-world verdict §9 mentions bets0.6 and0.55, which must not be substituted silently for the requested pair. This audit proceeds from actual primary versions and records the missing repository summary rather than inventing its hypotheses. No conclusion here upgrades a repository report or the conjectural limit to a proof.
