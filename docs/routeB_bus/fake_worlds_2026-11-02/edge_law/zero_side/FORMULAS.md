# Exact endpoint identity and zero-side conventions

DIAGNOSTIC_NEVER_A_PROOF. These finite-vector identities do not establish the proposed cofinal EDGE_LAW.

Let f=Σ_{n=0}^m c_n phi_n in the literal even carrier, L=log m, b=L/2, omega_n=2πn/L, Omega=omega_m, d_0=1,d_n=sqrt2, and phi_n=d_n(−1)^n cos(omega_n x)/sqrtL on[−b,b]. Put e=f(b)=Σd_nc_n/sqrtL. Away from modal frequencies, the exact physical transform is

    F(z)=2sin(bz)/sqrtL Σ_n d_nc_n z/(z²−omega_n²)
        =2e sin(bz)/z + R_f(z),
    R_f(z)=2sin(bz)/(sqrtL z) Σ_n d_nc_n omega_n²/(z²−omega_n²).

Apparent poles at modal frequencies are removable in the **whole** transform; use the stable shifted-sinc formula there. The endpoint term alone also has a removable origin.

Define C_f=Σ|d_nc_n|omega_n²/sqrtL. For real t>Omega,

    |R_f(t)| ≤ 2|sin(bt)| C_f/[t(t²−Omega²)].

A sharper computable bound keeps each denominator t²−omega_n². The code uses the displayed simpler valid bound. Consequently, for E(t)=2e sin(bt)/t,

    |2F(t)²−2E(t)²| ≤ 2[2|E(t)| B_f(t)+B_f(t)²],

where B_f is the remainder bound. For a finite real-zero block(T,Y], there is also the exact signed square expansion

    2Σ F(gamma)² = 2Σ E(gamma)²
                   +4Σ E(gamma) R_f(gamma)+2Σ R_f(gamma)².

The cross term need not have a positive sign; only the last term is nonnegative. The CSV saves all3 pieces and their closure error. This bounds a finite prefix sum by summing its right-hand side. It is **m-dependent**. At T=1.1Omega, neither Omega/T nor the denominator correction tends to0 merely because m grows. Thus the fixed-m t→infinity asymptotic F(t)~2e sin(bt)/t cannot by itself prove a uniform edge coefficient at this moving cutoff.

For complex z=gamma+i delta with |delta|≤a and gamma²>a²+Omega²,

    |R_f(z)| ≤ 2cosh(ba) C_f/[gamma(gamma²−a²−Omega²)].

For zeta one may use a=1/2 without RH, since all nontrivial zeros lie in its critical strip. DH needs its own wider zero-strip bound; the zeta a=1/2 cannot simply be reused for all DH zeros. These elementary bounds are finite-vector control, not a zero-density estimate.

## All-zero Weil form versus known real-zero prefixes

The full source identity pairs over **all** completed zeros:

    K(f,g)=Σ_rho conjugate(F_f(conjugate(z_rho))) F_g(z_rho),
    z_rho=i(rho−1/2),

with multiplicity, using the unconditional explicit formula. For real even f, the diagonal summand is F(z_rho)². Reality/functional-equation symmetries make the total real; they do not turn off-line terms into absolute squares.

At a positive **critical-line** ordinate gamma, the ±gamma pair contributes2F(gamma)². Therefore 2Σ_{0<gamma≤X}F(gamma)² is the exact contribution of the listed real spectral nodes. Identifying its infinite version with the **entire** source without accounting for off-line zeros would assume the disputed location property. The present finite computations do not do so. They retain the source-minus-known-prefix as a labeled difference, not an unconditionally positive infinite zero tail. Zeta's finite node list is numerical input; no new census/simplicity certificate is supplied here.

At one generic off-line quartet with positive-height nodes gamma±i delta, let F(gamma+i delta)=a+ib and let nu denote the zero multiplicity. Then

    Weil_quartet=4nu(a²−b²),
    ordinary_2G_quartet=4nu(a²+b²),
    metric_correction=−8nu b².

The negative-square **term** in the Weil quartet is−4nu b². The source's special interpolating witness has F(z0)=i, hence a=0,b=1, and its quartet contribution is exactly−4nu. A generic computed minimizing vector need not have either value. In particular, **nu means multiplicity, never a negative-energy statistic**.

For a positive-height table containing both reflected nodes, define G_pos=Σ_nodes|F(z)|² and M_im=Σ_nodes(ImF(z))², with each actual multiplicity. Then

    K_prefix=2G_pos−4M_im.

This is the same−8nu b² correction per quartet. `quartets.csv` gives each listed quartet's a,b and contribution rather than replacing it by−4nu. Listed multiplicity1 is the numerical dataset convention, not a new proof of simplicity. On-line nodes have M_im=0.

## Far-tail endpoint heuristic: coefficient2, not automatically4

If one additionally assumes a complete critical-line zero census in the relevant tail and replaces sin²(bt) by its phase average1/2, the leading positive-zero density dN(t)≈log(t/(2π))dt/(2π) gives

    Σ_{gamma>X} 2[2e sin(b gamma)/gamma]²
      ≈ [2e²/π] [log(X/(2π))+1]/X.

This is explicitly a phase-averaged **heuristic**, not an error-controlled evaluation. Its leading coefficient relative to e²log(X)/(πX) is2. The proposed observed coefficient near4 for a moving family could involve rational near-band corrections, below-cutoff contributions, or phase correlation; it is not explained by discarding the remainder. A proof needs those terms and all-zero accounting. The saved-vector finite sums measure these discrepancies without assuming RH above400.

The physical Erow implementation was read directly in `capacity_matrix_2026-11-02/capacity.py`, lines8–17. The full source was checked against CONFINE (1.3)–(1.4), lines119–157, Git blob`1879347b72d1aa55cf506f5387de37059f929122`; it retains both poles and all prime powers. For the even carrier the odd pole vanishes, while the even pole remains.

Source conventions match `ledger_diff/SOURCE_CONVENTIONS.md`, `NORMALIZATION_DH.md`, the pinned CONFINE/HARDBREAK full-Weil normalization, and the canonical FAKE_WORLD_EFZ_DH_BEURLING special-witness discussion §6.1. No source inequality is promoted by this decomposition.
