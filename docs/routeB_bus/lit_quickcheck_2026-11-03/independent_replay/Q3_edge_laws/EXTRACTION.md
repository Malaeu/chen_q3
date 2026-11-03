# Q3: source extraction, not theorem acceptance

Source: AlexGenusCore/weil-edge-laws commit `1c250f83343bb175311c0a7c46614bf7deb429a9`, paper/main.pdf, v0.2.0 (52 pages), accessed 2026-11-03. DOI endpoints were unavailable through the web tool; the GitHub PDF was downloaded and read. All claims below remain untrusted external statements. Page numbers are printed/PDF pages, which agree. Text licensed CC BY 4.0 by the repository; attribution Johann Alexander Botha.

Write a for their halfwidth L, ell(r)=log(1/r), and A±=lim_{r↓0} sqrt(ell(r)) ψ(±(a−r)). Functions are normalized eigenfunctions of the full continuous localized form, not eigenvectors of our moving compressed matrix.

* Edge: Thm4.1 p14 states continuity with zero endpoint values and ψ(±(a−r))=A± ell(r)^−1/2+O(ell(r)^−1), uniformly on stated compact parameter sets. Thm7.1 p25 sharpens to A± ell^−1/2+O(ell^−3/2), and, at fixed nondegenerate window, A±(ell−D)^−1/2+O(ell^−5/2), D=λ+log(2π)+γ. Second-order constants can degenerate as 2a approaches log n.
* Hadamard: Thm5.6 p18, sector-simple normalized continuous eigenbranch, dλ/da=−(A+²+A−²)=−2A², including prime activations. It is a derivative, not λ itself. Under our dilation τ, da/dτ=a, so dotλ=−2a A²=−log(m) A².
* Kink: Thm7.3 pp25–26. At a generation-k point z, ψ(z−d)−ψ(z)=[(k+1)W+−kW−]/(2k+1) ell(d)^−k−1/2+O(ell^−k−3/2); the right coefficient is [−kW++(k+1)W−]/(2k+1). Generic first-generation point a−log n has coefficients (2/3)c_n A+ and −(1/3)c_n A+, c_n=Λ(n)/sqrt(n). The sign is not universally positive on both sides.
* Second kink: Thm7.5 p27, Dψ(z;d)=Ω_k(ell−D)^−k−1/2+Ω_(k+1)ell^−k−3/2+O(ell^−k−5/2). Chains include nonminimal chains and both shift directions. Cor7.6 p27 gives 1/ρ_n=ell−D−β_n+O(ell^−1), with β_(p^j)=log p[(j−1)+Σ_{i≥1,p^(j+i)<exp(2a)}p^−i] under its no-opposite-edge-chain condition.
* First tail: Thm8.8 p31. With h(γ)=F(γ)F(−γ), actual complex source zeros and multiplicities retained, Z(T)=Σ_|Imρ|>T h(γρ). The assertion is |πT Z(T)−(A+²+A−²)|≤C(A²+|A|B)/log T+CB²/log²T. If A=0, Z(T)=O(B²/(T log²T)); if sector-simple, πT Z(T)=|λ′(a)|+Oψ(1/log T). The source explicitly limits the relative estimate to log T much larger than B/A.
* Second tail: Thm9.2 p32, smoothed Z_ν(T)=2m1(ν)/T [A²+(λA²+c_X A+A−)/log T]+O(|ν|(R)/(T log^(3/2)T)), c_X=Λ(X)/sqrt X, X=exp(2a). Thus normalized Υ_ν=1+(λ+εc_X)/log T+O(log^−3/2 T). Thm9.3 p33 only removes the cross term on average; sharp-cutoff second order remains open. It cannot be replaced by a pointwise sharp asymptotic.

These statements were extracted from the PDF, not reconstructed from the brief or accepted from the README. No proof audit of their Wiener–Hopf or tail estimates is claimed.
