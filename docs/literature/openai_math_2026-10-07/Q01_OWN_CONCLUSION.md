# Q1 own conclusion — original joint probe

2026-10-07. Full rendered Proshka attachment was read. The local answer record is PROSHKA_Q01_AUDIT_EXTRACT.md, explicitly a normalized mathematical extract rather than original bytes. Browser download events failed; no byte-exact archive is claimed. Source and request hashes are recorded in that extract.

## Root check

The source definitions at paper.tex 3348–3365 give xi of order dividing six, primitive modulo fixed bstar, and Xi(A)=xi(A)chi_A(bstar). On A=c*a^6,s=c*r^6 this yields chi_s(bstar)/(xi(s)Xi(A))=xi(c)^(-2), without discarding the target eta phase. The fixed-ray identity R(c*a^6,c*r^6)=chi_c(-1) cancels the Gauss sign. The source gamma1(c)gamma2(c)=mu(c)alpha(c)G(c) cancels alpha(c) and G(c), leaving exactly mu(c)eta(c)[baralpha(a)eta(a)]^6/xi(c)^2.

The Ramanujan factor q_r^3 from the sixth-power denominator cancels the q_r^3 in sqrt(q_s). Together with the source Y_J^-1*(q_s/Y_J)^(-1/2) and completed 1/sqrt(q_c), this gives 1/(sqrt(Y_J)*q_c), not a residual power of r. Substitution m=(r^6/e)z gives exactly E_v(Q_J*q_e/q_r^6;c*a). This remains valid when a and c share primes because the coprimality indicator is on rad(c*a).

The fixed-character Poisson argument pays the coprimality divisor sum once T/q_rad(c*a)>=Z^(1/96) up to fixed constants. On the retained Gaussian range the source geometry gives this bound for every subset: the worst d=1/6 has exponent 1/96. The omitted Gaussian range costs exp(-(log Z)^2/1024) times a fixed polynomial; sum_a q_a^-2 converges over ideals. These calculations support the rapid-decay claim with all original coefficients retained. Independent bounded audit by mobius_source_audit: PASS, no exact mismatch under the fixed-data and slot-scale assumptions. Checked local boundary cases, shared primes, unit projector, coefficient xi(c)^(-2), Poisson derivatives, every subset and the Gaussian tail. This is a checked paper-level lemma, not Lean admission or an audit of the whole manuscript.

## Important distinction from the exploratory root mask

The mask in RESONANCE_SUBTRACTION_PRINCIPAL_TEST.md is NOT the exact complement of the good-principal sector. For distinct good primes p,q, the allowed algebraic pattern s=p, c=p*q, n=1 is nonprincipal at q but the mask deletes it because of p. Conversely s=r^6,c=n=1 has no valuation-one s prime and survives that mask, yet lies in the good-principal sector. These are coefficient-support tests, not claims that particular primes populate every physical annulus.

Hence Q1's removal of the entire small sector preserves the original probe up to a proved error if accepted; our mask changes further nonprincipal terms and requires its own new low bound. Its checked local signal, reflection formulas and tail estimates remain exploratory results. They cannot be substituted for the exact remainder in Q1 equation (24).

## Next mathematical target

Use the original signed nonprincipal remainder N_eta(Z), including all subset signs, prime-power masks, target phases and unchanged scale. A new exponent for its normalized value must meet the common-signal consumer and coexist with a compatible high-side domain. No such exponent is established. A primitive character's complete-period mean zero does not pay the allowed n=1, coprime c,s block: its averaging-to-conductor ratio is Z^(-13/16).

Do not continue optimizing the root mask by absolute-value bounds unless a new hypothesis changes its unfavorable budget. Do not identify the small primal good-principal sector with the nonzero Poisson u=1 detector. RH/SP/G1/G3/Schur/scalar reserve remain OPEN.
