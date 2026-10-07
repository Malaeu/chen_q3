# Second-transform phase and finite-ray-only obstruction

Q4 is already pending; this calculation is not another message or a new route. It checks the exact proposed receiver for Q3(32), retaining all other source obligations.

## Composite squarefree phase

Independent mobius_source_audit PASS on Q3(32), for coprime squarefree primary good h1,h2. CRT gives tau_(h1h2)(bar chi_h1 chi_h2)/sqrt(q_h1 q_h2)=R(h1,h2)gamma_-1(h1)gamma1(h2). Conjugation gives bar gamma_-1(h2)=chi_h2(-1)gamma1(h2). The source identities gamma2^3=mu alpha and gamma1 gamma2=mu alpha G yield gamma1^2=mu alpha G^2 gamma2. Squaring the conjugation identity yields gamma_-1^2=mu baralpha barG^2 bargamma2. These give exactly Q3(32), including all orientations and the chi_h2(-1) factor.

Source: pinned paper.tex definitions642–643, reciprocity934–963, signal965–969, composite CRT1041–1051, conjugation10774–10775. SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3. No statement for nonprimary associates or noncoprime pairs is smuggled into this domain.

## A specific receiver that cannot work

The canonical source coefficient (paper7289–7295) is a0(h)=baralpha(h)gamma2(h) times a fixed finite ray character and puncture. The regenerated one-column coefficient in Q3(32) is a1(h)=mu(h)alpha(h)G(h)^2 gamma2(h). Since squarefree good Gauss coefficients are nonzero, their ratio is

r(h)=a1(h)/a0(h)=mu(h)alpha(h)^2G(h)^2.

Claim: r is not any function of a fixed finite residue/ray class on all squarefree primary good h. In particular no finite combination of fixed ray characters absorbs this ratio.

Proof. Given any proposed finite modulus m, choose a positive rational integer L divisible by3 with L O contained in m AND in a defining modulus for G. Include any fixed puncture in the finite set to avoid. Dirichlet's theorem supplies distinct rational primes p,q congruent to−1 mod L outside that set. They are congruent to2 mod3, so t^2+t+1 has no root over F_p or F_q (a root would give a nontrivial element of order3); hence (p),(q) are prime ideals in O=Z[omega]. Thus h1=−p and h2=pq are primary good squarefree generators, both congruent to1 mod L O. Both have alpha(h_i)^2=1 and G(h_i)=G(1)=1, while mu(h1)=−1 and mu(h2)=+1. Their ratios differ in the same residue class. Both indices can be arbitrarily large, so omitting finitely many indices does not repair the mismatch.

The use of Dirichlet is the standard infinite-primes-in-coprime-progression theorem, with residue L−1 coprime to L; its formal statement is documented at https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html . This paper argument does not claim a fresh Lean build.

Scope: the fixed-finite-ray-only receiver is ruled out on the full stated coefficient family. The actual dyadic joint sum might have cancellation, and other factors could interact with this ratio. No lower bound for the physical sum, no exclusion of moving twists or a new automorphic construction, and no full route death follows. Inert prime ideals are valid source indices; silently restricting to split primes would change the receiver domain and require separately paying the omitted sector.

Independent mobius_source_audit checked both the phase identity and the two-index obstruction. Keep the original signed sums and physical complement; compare this bounded mismatch with Q4 when its terminal answer arrives. Do not send a second question while Q4 runs.
