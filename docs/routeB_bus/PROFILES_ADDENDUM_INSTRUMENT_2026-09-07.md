# ADDENDUM to REQ-2026-09-07-PROFILES — instrument correction (observer, 2026-09-07, after delivery)

The full-margin numbers in §0 of the request («𝔪(v_{+,T}) = −0.0255 at T = 120, −0.0192 at T = 240») come from the mellin_d2 d₂ table (retained-mode
truncation, J = 8). A truncation sweep shows they are NOT converged on the plus channel: J6/J7/J8 = −0.0455/−0.0343/−0.0255 at T = 120 (−34% per step),
while the minus channel converges (+0.0103/+0.0116/+0.0117). Geometric extrapolation puts the limit near zero with undetermined sign. Mechanism: the plus
weight 1 + cos aξ peaks exactly at the Euler harmonics ξ = 2πk/log 2, where the truncated-multiplier error (1 + r)r^{J+1} and the dormant near-unit modes
sit; the minus weight vanishes there. Therefore: treat «full margin negative on the plus channel» as UNRESOLVED (instrument-limited), not as data.
The scalar plus-channel floor (your G34) is unaffected: it uses ℓ₂ only, and two probes agree with −((1 + C_a)/c)p(T) to 2%.
Q1(a) of the request stands as a paper question; Q1(b)–(d) unchanged. The Euler-Gram evaluator (SCALARFLOOR Thm 3 / CLASSFLOOR (18)–(22)) is being built as the
honest instrument for d₂ on the plus channel.
