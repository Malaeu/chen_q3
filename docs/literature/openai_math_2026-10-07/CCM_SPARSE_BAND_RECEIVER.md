# Conditional off-critical witness on a sparse band of the original CCM matrix

2026-10-08. Root derivation, independent read-only sparse_band_receiver audit PASS on the complete payload. The production matrix is still literal K_m with N=m,L=log m. Only a test subspace is restricted. No prime spectral bound or RH is proved; the active full-SP phase is not silently changed.

## Claim and source

Fix any alpha in (0,1), M=floor(m^alpha), and let H_(m,alpha) be the subspace of the ORIGINAL coefficient carrier supported on |j|<=M. Let P_(m,alpha) project onto its subspace satisfying the original three equations b*c=v_+*c=v_-*c=0. Original b has 2m+1 coordinates and v_± are the original Fourier coefficients of exp(±t/2) on [0,L]. Padding by zero identifies the equations with the corresponding truncated vectors, with the constant vector rescaled to unit norm. This does not create a new production matrix or change the m schedule.

Conditional on a fixed zero xi(1/2+w)=0, w=delta+i gamma, delta>0, there are c_(w,alpha)>0 and a starting m such that EVERY later original cell has

    lambda_min(K_m restricted to ran P_(m,alpha))
            <=-c_(w,alpha) m^delta L^(-2delta).                (1)

All constants may depend on fixed w,alpha and selected fixed derivative order. They do not depend on m. No uniform assertion as alpha tends to zero, nor any polylogarithmic-band assertion, is made.

Use the already checked normalized derivative-filtered source pair in CCM_RESTRICTED_PRIME_RECEIVER.md: its two Laplace moments vanish, its full Weil value is -2r m^delta L^(-2delta), and its L2 norm stays bounded. Cut off inside [-L/2,L/2] with the same fixed-width smooth transition and translations h=L/2-log L. Every FIXED derivative L1 norm stays bounded; cutoff-form error is O(m exp(-cL²)). Both zero-extension strips remain part of the projection estimate below.

## Sparse Fourier projection: actual form norm

The general fixed-q estimate in PROSHKA_NEGATIVE_BOTTOM_NORMING_INLINE_2026-10-06.md equations(2),(3), inherited by NEGATIVE_BOTTOM_GROWTH_AUDIT_2026-10-06.md, applies with Omega_M=2pi M/L. Let e=f-f_M be the Fourier tail of the cutoff source, q>=2 a FIXED integer. It gives

    ||e||_E <=C_q[sqrt(m)Omega_M^(1/2-q)
                   +Omega_M^(3/2-q)+Omega_M^(1-q)] =: E_q.    (2)

Indeed the L2, derivative-L2 and endpoint sup bounds are respectively proportional to Omega_M^(1/2-q), Omega_M^(3/2-q), Omega_M^(1-q); insert them into ||e||_E²<=(m+16)a0²+2a1²+8ainfinity². The m factor comes from the original window weight exp(|t|), not from the number of retained modes. Endpoint jumps are paid; no whole-line H1 claim is used.

The cutoff source has ||f||_E<=C sqrt(m). Full Weil continuity therefore gives

    |W(f_M)-W(f)|
      <=C_q[m Omega_M^(1/2-q)+sqrt(m)Omega_M^(3/2-q)
                +sqrt(m)Omega_M^(1-q)+E_q²].                 (3)

Choose once and for all an integer q>1/alpha+2. The three displayed powers of m are 1+alpha(1/2-q), 1/2+alpha(3/2-q), and 1/2+alpha(1-q), all strictly negative. Their fixed logarithmic factors do not change convergence. E_q² also tends to zero. Thus (3) is o(1). The exact same centered-window form equals the quadratic form of the padded vector in K_m; translation to [0,L] preserves the full Weil form.

## Sparse-band correction of the three constraints

Let v_(±,M) be the original v_± truncated to |j|<=M and b_M the normalized constant vector on that band. The explicit exponential coefficients give

    ||v_(+,M)||²=m(1+O(L/M)),
    ||v_(-,M)||²=1+O(L/M),
    |<vhat_(+,M),vhat_(-,M)>|=O(L/sqrt(m)+L/M),
    |<b_M,vhat_(±,M)>|=O(sqrt(L/M)).                          (4)

Terms O(1/m) in the norms can be absorbed because M<m. For the cross term, full inner product is L and the omitted tail product is O(sqrt(m)L/M); division by normalized scales gives (4). The b_M estimates follow by pairing conjugate denominators and sum (1/2)/(1/4+omega_j²)=O(L). Since M/L tends to infinity, the normalized three-vector Gram matrix tends to I and is >=I/2 eventually.

With q as above, repeated integration by parts gives full Fourier coefficients |c_j|<=C_q L^(q-1/2)|j|^(-q). The truncated L2 tail has size O(L^(q-1/2)M^(1/2-q)). Endpoint value zero implies sum of all coefficients zero, so the normalized b_M constraint residual has that same order. The zero Laplace moments before cutoff, the super-small cutoff remainder, and Cauchy-Schwarz against the omitted exponential coefficients give the same order for both normalized v constraints; the ratio of full to truncated exponential norms stays bounded by (4).

Therefore, if c_M is the padded Fourier vector and z=P_(m,alpha)c_M,

    ||z-c_M||<=C_q L^(q-1/2)M^(1/2-q)
                                      +m^C exp(-cL²).        (5)

The full original ||K_m||<=40sqrt(m)L and bounded ||c_M|| pay its quadratic-form correction by

    C_q sqrt(m)L^(q+1/2)M^(1/2-q)
                                      +m^C exp(-cL²)=o(1).   (6)

The unchanged source pair's negative signal diverges as m^delta/L^(2delta). Combining (3),(6) and cutoff cost leaves that signal intact; ||z||² stays bounded, and its negative form ensures z is nonzero. Normalizing proves (1).

## Exact remaining arithmetic consumer

The two exponential equations still annihilate the original growing rank-two kernel, and the endpoint equation still uses the original b. Consequently

    P_(m,alpha) K_m P_(m,alpha)
       =P_(m,alpha)(Aarch-cA I-Aprime)P_(m,alpha).             (7)

Here Aprime=sum_(2<=n<=m) Lambda(n)Q(log n)/sqrt(n) retains every prime power and the original Q; Aarch is the original archimedean compression. The inherited bound ||Aarch-cA I||<=50L+8 is equation(12) of CCM_RESTRICTED_PRIME_RECEIVER.md; its equation(11) gives the cancellation used above.

Thus a subpolynomial upper bound for the actual prime matrix on this smaller space would suffice to exclude every fixed off-critical zero. Such a bound is OPEN. Membership in a smaller band supplies neither independent primes nor a sign. Old full SP/G1/G3 are not thereby proved. A fixed alpha is enough for this conditional receiver; alpha cannot be tuned with m inside this theorem.
