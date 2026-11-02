# Source conventions for the signed complement ledger

Independent identity/normalization review, 2026-11-02. No new bound or proof claim.

Pinned source: [KERNEL_ORTHOGONALITY at c31645a3efd410417f6e2027b4474711bd443348](https://github.com/Malaeu/chen_q3/blob/c31645a3efd410417f6e2027b4474711bd443348/docs/routeB_bus/proshka/PROSHKA_VERDICT_KERNEL_ORTHOGONALITY_2026-11-02.md), blob `98380adf97aab19a900e332b6583c8f731b6d3f6`. Its actual equation numbers are (2.2) at line 94, (2.4) at 110, (2.5) at 114, boundary (3.3) at 139, bulk derivative (3.4) at 145, and the joint unpaid object (6.1) at 227. It mentions numbers (5), (6), (7) as labels inherited from a request; it contains no displayed equation (12). Do not silently attach a new meaning to those user labels.

Referenced [PRIME_COMPLEMENT_FLOOR at a4ab9e92bf080ee3bcfd729af067ade6fc6392fc](https://github.com/Malaeu/chen_q3/blob/a4ab9e92bf080ee3bcfd729af067ade6fc6392fc/docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_COMPLEMENT_FLOOR_2026-11-02.md), blob `88de1569443ba35acdeefdeb64ace9bbb43c47e8`: §3, (3.1)–(3.3), gives pole/continuum compensation; (4.2)–(4.3) isolates primes and squares; (5.1)–(5.2) gives Abel and the moving boundary. Its source metadata SHA256 is `3a827900de98c45d02ce617f606c4a0ab1fa7b337ed846ea12f7eb9db301b3fa`.

## One physical vector for every ledger entry

Use the actual normalized minimum eigenvector of the compressed complement operator, lifted by an orthonormal synthesis U into the physical even carrier. Thus f=Uy, ||y||=||f||=1. Evaluate **every** component on this same f; the sum of separate component minima is not the complement bottom. For an eigenvalue cluster, record the selected vector or an invariant cluster-level alternative explicitly. For nonorthonormal Riesz-kernel coefficients c, physical normalization is c^T G c=1, not c^T c=1; G=EE^T in the pinned source. The final source-weighted sum equals the selected Rayleigh quotient (the complement bottom when y is its minimizing eigenvector), not necessarily the full-carrier bottom.

Let L=log m, b=L/2, and Q(s)=2∫_{-b}^{b-s}f(x)f(x+s)dx for 0≤s≤L, zero afterwards. Then Q(0)=2 and Q(L)=0. Endpoint atoms n=m contribute exactly zero.

## Direct original-source ledger

For zeta define positive jump energy H_z=∫_0^∞ j_z(s)[2−Q(s)]ds, j_z=e^{-s/2}/(1−e^{-2s}), and signed constant contribution c_z=−c*=−γ−log(8π)−π/2. The pole contribution is O_z=|<sqrt(2)cosh(x/2),f>|². Write raw arithmetic sums P_r=Σ_{n in sector r} Λ(n)n^{-1/2}Q(log n), with sectors p, p², p^k (k≥3). Then

    λ_z = H_z + c_z + O_z − P_p − P_p² − P_p^k≥3.

Report both raw P and its signed ledger contribution −P, or use column names that make the minus sign explicit. A positive coefficient does not force a positive P: Q can have either sign.

For DH use H_D=∫_0^∞j_D(s)[2−Q(s)]ds, j_D=e^{-3s/2}/(1−e^{-2s}), c_D=−γ−log(8π/5)+π/2, and **O_D=0**. Use b(n) from −F'/F, not reciprocal coefficients. Partition n uniquely into p, p², p^k (k≥3), and non-prime-powers. Within each sector split b(n)>0 and b(n)<0 (zero coefficients are omitted). Define P_{r,±}=Σ_{n in r, ±b(n)>0}b(n)n^{-1/2}Q(log n), retaining b's sign. Thus

    λ_D = H_D + c_D − Σ_{r,sign} P_{r,sign}.

These are exact original-source ledgers with no artificial main term. DH non-prime-power atoms must remain: for example b(6)=(1+tan²θ)log6. A split by coefficient sign is not a split by the sign of each evaluated summand. If a report also splits evaluated summands by sign, give it separate column names.

## Zeta compensated ledger: a different arch kernel

The source's H_m in KERNEL_ORTHOGONALITY (2.4) is H_+, **not H_z**. Put

    j_+=e^{-5s/2}/(1−e^{-2s}),   H_+=∫_0^∞j_+(s)[2−Q(s)]ds,
    I_L=∫_0^L e^{s/2}Q(s)ds,    R_−=∫_0^L e^{-s/2}Q(s)ds.

Exactly H_z=H_++4−R_− and O_z=I_L+R_−. Therefore

    S=P_p+P_p²+P_p^k≥3−I_L,
    λ_z=H_+ +(4−c*)−S.

For the joint source target involving only primes and squares, set S_12=P_p+P_p²−I_L=S−P_p^k≥3. Its unpaid Rayleigh quantity is S_12−H_+. Thus

    λ_z=(4−c*)−(S_12−H_+)−P_p^k≥3.

The compensated constant is 4−c*, while the original constant is −c*. Mixing H_+ with the original constant/pole/arithmetic ledger double-counts the compensation. Keep direct and compensated tables separate and cross-check their final sums.

## Abel boundary/interior conventions

For zeta let Ψ_z(x)=Σ_{n≤x}Λ(n), E_0(x)=Ψ_z(x)−(x−1), and a_z(s)=e^{-s/2}E_0(e^s). Define three raw remainder components

    T_z = ∫_0^L a_z(s) Q(s)/2 ds,
    Bulk_z = −2∫_0^L a_z(s)∫_{−b}^{b−s}f(x)f'_int(x+s)dx ds,
    Boundary_z = 2 f(b)∫_0^L a_z(s)f(b−s)ds.

Then S=T_z+Bulk_z+Boundary_z exactly. This is (2.2), (3.3), (3.4) of the pinned kernel source. A two-column notation can unambiguously use

    mathcal B=Boundary_z,    mathcal I=T_z+Bulk_z,
    S=mathcal I+mathcal B.

If the user's mathcal I means only the interior **derivative**, report Bulk_z under that name **and retain T_z separately**. Do not lose the Q/2 term. In the compensated eigenvalue ledger these contributions occur with a minus: λ_z=H_++4−c*−T_z−Bulk_z−Boundary_z. In S_12−H_+, their signs are plus, followed by −P_p^k≥3−H_+. Boundary is not intrinsically positive and need not vanish on the complement.

Equivalently Q'(s)=2∫f(x)f'_int(x+s)dx−2f(b−s)f(b). The second term is the moving-boundary term; differentiating the zero-extended carrier as if it were globally smooth loses it. E_0(1)=0 and Q(L)=0 pay both Abel endpoints. Using Ψ_z−x changes the expression by an explicit +2 in the final identity for S; it is not the same convention.

## DH Abel split without inventing a continuum

There is no DH pole and no canonical x−1 arithmetic main term in this model. Define instead

    Ψ_D(x)=Σ_{2≤n≤x} b(n),    a_D(s)=e^{-s/2}Ψ_D(e^s).

For the entire raw DH arithmetic P_D=Σ b(n)n^{-1/2}Q(log n), Abel gives

    P_D=∫_0^L a_D(s)[Q(s)/2−Q'(s)]ds
       =T_D+Bulk_D+Boundary_D.

The definitions of the three components are exactly those above with a_D replacing a_z. Consequently

    λ_D=H_D+c_D−T_D−Bulk_D−Boundary_D.

This is an arithmetic identity, not a new DH continuum cancellation. It can be applied sector by sector, including each coefficient-sign sector, by using its own cumulative coefficient staircase. If one deliberately subtracts a reference x−1 in DH for an additional experiment, its continuum must be separately added back, clearly labeled as an arbitrary reference; it cannot be presented as a pole-cancelled main term or compared directly with ζ's S.

## Numerical comparisons and scope

The ζ and DH complement bottoms generally have different minimizing vectors and possibly different complements. Their two ledgers describe those respective minima; subtracting entries is descriptive, not a common-vector operator comparison. State the κ cutoff, zero census/orbit convention, rank and normalization of each complement. For a common-vector comparison explicitly choose the common carrier vector and evaluate both sources on it.

These decompositions localize exact signed contributions. Neither finite identity matching, a small boundary term, nor a finite positive complement bottom establishes the pinned source's uniform upper bound (2.5), its downstream floor requirement, or RH.
