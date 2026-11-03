# Q1 normalization crosswalk

DIAGNOSTIC_NEVER_A_PROOF. No fitted factor is used.

External certificate `L` is physical half-width a: supp f⊂[-a,a]. Its autocorrelation support length is ℓ=2a. Our CCM window length is ℓ=log m, hence a=log(m)/2. The semilocal **upper** script instead calls the full autocorrelation length `L`; its `11147/10000` means ℓ=1.1147, not a=1.1147. The lower scripts use half-width.

Both use F(t)=∫f(x)e^{itx}dx, Plancherel (2π)^{-1}∫|F|²=||f||², and the real Weil form

Q[f]=2F(i/2)F(-i/2)+(2π)^{-1}∫|F(t)|²[Re ψ(1/4+it/2)-logπ-Σ_{log n<ℓ}2Λ(n)n^{-1/2}cos(t log n)]dt.

Both poles are retained: positive rank-one on real even f, negative rank-one on real odd f. Prime powers remain; semilocal P means base prime p≤P, not integer n≤P. Source scalar products use Lebesgue dx and L2-unit vectors. The independent Fourier carrier has modes -N..N and sectors dimensions N+1,N; external lower certificates use N Legendre modes **per parity**, so their numerical N is not our N.

In physical form j(s)=e^{-s/2}/(1-e^{-2s}), c=γ+log(8π)+π/2, C_f(s)=∫f(x)f(x+s)dx:

Q[f]=∫_0^∞ j(s)(2||f||²-2C_f(s))ds-c||f||²-2ΣΛ(n)n^{-1/2}C_f(log n)+2A_+A_-.

For zero extension outside the window, the archimedean tail is exact:
∫_ℓ^∞j(s)ds=atanh(e^{-ℓ/2})+atan(e^{-ℓ/2}). It must be multiplied by 2||f||². This explicit tail and the negative odd pole are included in the independent witness replay.

Support ±31/32 gives full length31/16=1.9375 < log7=1.945910149... . It alone does not cover log7. The repository instead uses the separate P5 lower certificate at a=.973 (full length1.946); at log7 the active positive-weight atoms have prime bases≤5, with the atom7 at birth having zero overlap. The P5 certificate was fetched, not independently rerun in this bounded quickcheck.
