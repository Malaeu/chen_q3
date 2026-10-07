# Sextic large sieve: bounded source audit

2026-10-07. Source: OpenAI math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex, SHA256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3. Scope: lemma sextic-large-sieve and its explicit proof, lines 4707–5180. Root inspection plus independent mobius_source_audit: bounded PASS; not a certification of the full manuscript or of RH.

D_j has squarefree rows and columns; E_j permits arbitrary good evaluation rows, j in {1,2,4}. The paired Poisson estimate is Q_j <= (MN)^epsilon ||lambda||_2^2 [M+(M/N) max_{H <= (MN)^epsilon N^2/M} E_j(H,N)]. The unit-class split makes the paired character unit-trivial; its primitive conductor, zero extension and Gauss phases are explicit (4772–4876). Mellin separation keeps the two coefficient vectors fixed over the row sum; coprimality detection costs a divisor factor (4887–4959).

Opening E_j by gcd d and Mobius divisor r gives the displayed norm reflection (4991–5008). The sum of residual coefficient masses is bounded by a divisor-square weight (4970–4986); no independently chosen row-dependent coefficients are inserted. The additive sieve initial estimate is D_j(M,N) <= O(M^2+N), via separated reduced fractions (5018–5034). The stated near-monotonicity uses prime multiplication with its bad-prime coefficient mass explicitly controlled (5036–5065).

The sixth-power decomposition selects the larger X_1 or X_2, yielding min{M^(1/3),(M/X_l)^(2/3)} (5077–5104). The j -> 2j mod 6 cycle stays inside {1,2,4}. Starting from D_j <= (MN)^epsilon (M^alpha+N+(MN)^(2/3)), the reflection gives

D_j <= (MN)^epsilon [M+M^(1-alpha)N^(2alpha-1)+(MN)^(2/3)].

With h=2-3/(3alpha-1), near-monotonicity below M=N^h improves alpha to beta=2-2/(3alpha-1). Finite iteration from alpha=2 approaches 4/3 with arbitrary positive loss. Symmetry and dyadic sums produce K+D+(KD)^(2/3). No unsupported recursion inequality was identified in this bounded audit.

Citation applicability: BGL, L-functions with n-th-order twists, https://arxiv.org/abs/1112.1650, Theorem 1.3 and section 3, gives the analogous arbitrary-coefficient shape. Its introductory ambient assumption d>phi(n) does not directly cover d=phi(6)=2 here. The verdict therefore rests on the pinned manuscript's specialized derivation, not on a blanket BGL citation transfer. The additive sieve and arithmetic preliminaries remain dependencies; this is not a fresh end-to-end proof of every source lemma.

Consumer: the existing high-row count may continue to use this source estimate subject to its other hypotheses. This audit supplies no stronger exponent, no new low estimate for N_eta, and no Q3 positivity/Schur bridge. RH/SP/G1/G3/scalar reserve remain OPEN.
