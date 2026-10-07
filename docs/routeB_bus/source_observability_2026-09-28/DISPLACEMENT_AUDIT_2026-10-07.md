# Q7 displacement: source audit, 2026-10-07

Verdict: PAPER identities and stated local bounds accepted; displacement mechanism STALLED at joint distinct-zero correlations. No new Schur sign, exponent, SP, G1/G3 or RH result.
Source: `PROSHKA_DISPLACEMENT_INLINE_2026-10-07.md`, same living chat `6ac58a1c-1568-83ed-95d0-857526e2b6cb`, answer `029ac519-36f7-401b-8b92-e012630a8aa5`. Full preview Q07 read in the original UI, including proof budgets and return section. Q8 unsent.

## One bounded independent pass

- growth_symbol_attempt checked §1: finite kernel, Bernoulli interior identity, prescribed endpoint values rho(0)=1, rho(L)=-1, first anchor signs, and middle-band bound 128(1+L)^3/sqrt(m) for integer m>=16. The n=m atom is retained. This is entrywise, not an operator bound.
- causal_algebra_audit checked §2 and §4: two resolvent actions, asymmetric two-source kernel (both mixed terms), and exact projected HC/H²C return including feedback. No hidden deletion of the continuous compensator.
- answer10_pair_audit checked §3: source row pack lines2161–2169 and2373–2382; inline equations14–18. With w†=-conj(w), z=conj(w)/(i*kappa), t=sqrt(L)sin(pi*z)/pi, z†=conj(z), t†=conj(t). Parseval is for the exact row product, with absolutely summable omitted Fourier tails. The four same-pair tail terms are 2i Im(t² sum_tail(z-j)^-2), giving precisely -i*r_w Im(...) after the negative r_w/2 factor. The bound is 4*r_w*L*m^(delta-1)/pi², only for |gamma|<=Omega/2. Distinct-pair coefficient is 4i sqrt(r_p*r_w), with all four tails retained.
- Root checked full-preview return and scope. DLMF24.8.2 at n=0 gives the Bernoulli sine identity only on the open interval; endpoints come from the finite kernel, not evaluation of its interior series. Primary source: https://dlmf.nist.gov/24.8#E2 .

## Exact remaining object

Use C=L0*, positive row matrix Pcal, Gc=C*C, Pi=I-C Gc^dagger C*. With E0=-Nnear+Wtail-(K-H0),
H0=Pcal*Pcal-CC*+E0, Omega=Pcal C,
Bscr=Pi(Pcal*Omega+E0 C), Wscr=Pi(Pcal*Pcal+E0)Bscr.
For v=Cz: q0=z*(Omega*Omega-Gc²+C*E0 C)z; b=Bscr z; w=Wscr z.
M=||b||², c=<b,w>+epsilon*M, e=||w||²+2epsilon<b,w>+epsilon²M,
Gamma=M||w||²-|<b,w>|².
For every eta>0 on original unbounded good cells, the sufficient source test remains
Gamma <= g{(q0+r||v||²)(gc+e)-Mc}, g=r-epsilon>0, r=C_eta*m^eta.
The b=0 diagonal case remains separate. No nonzero Tb=0 case survives T>=2cA I.

Same-pair whole-interval overlap vanishes exactly; finite carrier overlap is a tail. Distinct ordinates give an oscillatory cosh-sinh integral, not zero. Most retained rows can lie outside the middle band (retained height mL²). Therefore the local bound does not control Omega or Bscr/Wscr jointly.

## Return and decision

All seven signed source words, F10, endpoints and actual projector remain. Exact formulas have zero approximation error; they are not norm estimates. Any use of truncated source must pay Delta10 and 4epsilon4 times ||v||||J_r v||, and the Q6 nonlinear moment error ledger with fixed actual Pi. Neither the entrywise anchor estimate nor the same-pair estimate is an admissible replacement operator error. ||J_r v|| is not uniformly bounded by ||v||.
Finite floating checks reported by Pro are diagnostic generic parameters, not certified actual-zero witnesses. No Lean run was needed for these identities.

Return through alias-hunt before selecting a new mechanism: see `docs/literature/mixed_zero_gram_2026-10-07/README.md`. Exponential divided differences currently provide a conditional partial analogue, not a signed supplier. Next bounded test: track the exact source weight under cluster renormalization; require a quantitative uniform mixed-Gram estimate before asking Q8.
