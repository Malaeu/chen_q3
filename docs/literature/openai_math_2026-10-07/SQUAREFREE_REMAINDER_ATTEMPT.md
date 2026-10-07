# Exact squarefree remainder: conductor test and the cost of termwise bounds

2026-10-07. Own attempt after Q1. Source: pinned paper.tex SHA256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, especially definitions 3348–3412, exact mixed sum in PROSHKA_Q01_AUDIT_EXTRACT.md, and Poisson transform 3725–3761. This is a partial treatment of n=1 and squarefree s, not the whole N_eta. Independent squarefree_conductor_check audit PASS: exact phases/masks, primitive modulus, uniform Poisson bound, physical exponents and conditional termwise budget checked. Source locators: character definitions 627–643; Gauss magnitude 766–799; CRT 1041–1051; fixed xi 3349–3378; scales 6860–6870 and 8073–8081.

## Conductor, including the shared-prime mask

Put g=gcd(c,s), c=g c0, s=g s0, with c,s squarefree; g,c0,s0 are pairwise coprime and avoid S. Define the full normalized Gauss scalar kappa_s=q_s^(-1/2)g_chi_s(s,1). Since chi_s is primitive, |kappa_s|=1. Retaining its CRT phases, the exact inner m-factor is

xi(m) chi_c(m) q_s^(-1/2)g_chi_s(s,-m)
 = kappa_s bar chi_s(-1) psi(m) 1_((m,g)=1),
psi=xi chi_c0 bar chi_s0.

The zero-extended psi is primitive modulo bstar*c0*s0: at each good prime exactly one nontrivial sextic factor survives, while xi is nonprincipal at each fixed bad prime. Write R=q_bstar*q_c0*q_s0. Do not replace kappa_s by a product of local gamma factors without their CRT phases. If psi is nontrivial on global units, the radial element sum vanishes exactly; otherwise retain the sum below.

For E_psi(Q;g)=sum_(m!=0) Omega(q_m/Q)(q_m/Q)^(-iv) psi(m)1_((m,g)=1), expand the mask over f|g. Substitution m=fz produces psi(f) times the same annular character sum at U=Q/q_f; its character conductor is still R, since (f,bstar*c0*s0)=1.

Primitive Gauss magnitude sqrt(R), planar Poisson and smooth radial Fourier decay imply, for every integer N>=1 and Q/(R*q_g)>=1,

|E_psi(Q;g)| <= C_(N,Omega,F) (1+|v|)^(2N+4) d(g) sqrt(R) (Q/(R*q_g))^(-N).

Constants here are uniform in the primitive character and moving modulus; the factor sqrt(R) is essential. Indeed the prefactor U/sqrt(R) and sum of (1+U*q_h/R)^(-N-2) over nonzero h give sqrt(R)*(U/R)^(-N-1) when U/R>=1. The zero frequency is absent. This extends the mechanism of Q1 to a low-conductor subset, without claiming the whole remainder is long.

## The physical scale fails in the upper c block

For s~Y_J and Q=q_bstar X_J Y_J, exactly R*q_g=q_bstar*q_c*q_s/q_g. Thus

Q/(R*q_g) ~ X_J*q_g/q_c.

For any fixed tau>0, the subregion q_c/q_g <= X_J*Z^(-tau) permits arbitrary power saving after polynomially bounded parameter counts on a Gaussian cutoff. This statement only covers the specified squarefree block; the Gaussian tail and other n,s sectors must be retained in the full probe.

On q_c~T_D, the coprime ratio is Z^(-13/16). Even allowing the maximal possible q_g<=q_s~Y_J gives

Q/(R*q_g) << X_J Y_J/T_D ~ Z^(-1/3-d),  0<=d<=1/6.

Hence shared primes cannot put this whole upper block in the long-character-sum range. This is a failure of that sufficient Poisson argument, not a lower bound on the actual sum. The diagonal c=s,n=1 is already inside Q1's negligible sector; its presence in the formula is consistent.

## Why individual square-root cancellation would still be insufficient

Diagnostic hypothesis ONLY: suppose the entire relevant squarefree inner sum satisfied |E_psi(Q;g)| <= Q^(1/2)*Z^epsilon uniformly, stronger than anything proved here in the short range. Test a dyadic q_c~C~T_D and q_s~Y_J, and take absolute values in c,s and slot tuples. Since n=1, D|c; counting multiples of D gives O(C/q_D), and sum c^(-1/2) costs O(sqrt(C)/q_D). The normalized s average costs O(1), Q^(-1/2) cancels the hypothetical square-root m estimate, and tuple count is O(Z^(1/6)). Thus the resulting upper-bound budget is

Z^(1/6) q_Rslot^(-3/2) sqrt(T_D)/q_D
 ~ Z^(7/12-d),

where q_Rslot~Z^d and q_D~Z^(1/6-d). In particular the d=0 bound is Z^(7/12), worse than the source's full low bound Z^(3/16). The gap is 19/48. This is only the output of termwise absolute summation, not proof that any square-root estimate or the true sum is inadequate. Additional cancellation in c,s or across subsets can change it.

## Next exact target

A useful Q2 must preserve and exploit the c,s coefficients jointly, or demonstrate that this apparently expensive block is absent/cancelled after the actual subset recombination. Merely improving each m sum, dropping CRT/eta/G phases, or redoing complete character orthogonality is not enough. The full target remains an improvement of the exact normalized N_eta compatible with the reciprocal-L high-side domain; no exponent improvement or Q3 Schur bridge has been established.
