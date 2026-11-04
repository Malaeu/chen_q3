# Independent audit of Lemma 2 geometry

DIAGNOSTIC_NEVER_A_PROOF. Verdict: **bounded PAPER PASS for (3.1)–(3.5), conditional on the stated external Montgomery–Vaughan inequality (0.1)**. No fatal counterexample found. This audit does not validate the external theorem from its original paper, Lemma1, the finite tail certificate, or the downstream zero-count transfer. It does not promote Route B or any export.

Input: `INPUT_VERDICT.md`, especially lines225–286. The requested counterexample marker is not emitted because no counterexample was found. No source matrix was changed or regenerated and no spectral scan was run.

## Exact full Fourier trace, (3.4), lines229–232

Use the literal truncated shift `(S_a f)(x)=1_I(x+a)f(x+a)` for x∈I and Fourier mode `e_j(x)=L^(-1/2)exp(2πijx/L)`. For a composition S_a S_b, its support in x is the interval intersection defined by x,x+a,x+a+b∈I. Its length is

`[L−(max(0,a,a+b)−min(0,a,a+b))]_+`.

The diagonal Fourier matrix element is this length divided by L, times `exp(2πij(a+b)/L)`. Consequently opposite orientations a=u,b=−v and a=−u,b=v have length L−max(u,v) and phases ±(u−v). Same orientations have length (L−u−v)_+ and phases ±(u+v). Summing |j|≤m produces precisely the factor2/L and the two Dirichlet terms in (3.4). This is the full trace of the *uncompressed square*, not the Frobenius square of a finite compression. In particular no intermediate Π has been silently inserted.

A useful exact endpoint test is L=1, u=1/2, coefficient1: S_u+S_−u is the periodic half-turn up to null endpoints. It preserves the Fourier band. Thus full energy=2m+1, even compressed Frobenius square=m+1, zero leakage. Formula(3.4) gives2(2m+1)(1−1/2)=2m+1, as required. A single u=L atom is exactly zero in both constructions.

## Circular separation, (3.5), lines238–247

For ordinary neighbors among integers2,…,m,

`log(n+1)−log n ≥1/(n+1)` and `log n−log(n−1) ≥1/n`.

All other ordinary distances are larger. The wrap distance is `L−log(m/2)=log2`; after normalization it is log2/L, which exceeds1/((n+1)L) for every n≥2. Therefore δ_n=1/((n+1)L) is admissible on the full node set; restriction to a prefix can only increase minimum distances. The endpoint n=m is x=1 modulo1, while no node n=1 is present, so there is no duplicate node. Keeping its zero atom in the node set is harmless.

Writing D_m as `(exp(iπd x)−exp(−iπd x))/(2i sinπx)` invokes(0.1) twice, with coefficients multiplied by exp(±iπd x_n). Each has unchanged absolute coefficients, and the factor1/2 cancels the two bounds. Thus the prefix constant is3L/2, not3L. Integrating the prefix weight L−max(u_n,u_k) and then multiplying the half-trace factor1/L gives exactly3W/2.

For the same-orientation term, put r=w/L. The elementary bound |sinπr|≥2min(r,1−r) gives `(1−r)/|sinπr|≤1/(2r)` for r≤1/2, and≤1/2 otherwise. Since w≥2log2, the former is≤L/(4log2). The printed b_L=1+L/(4log2) safely covers both cases, including the zero-overlap endpoint.

## Reflection/parity, lines257–267

Reflection commutes with the sum of positive and negative truncated shifts and with Π. Therefore the even uncompressed energy is one half the full energy plus one half the reflection trace, exactly as written. Each of the four oriented compositions remains a single shift restricted to an interval K. Its reflection trace is the printed `L^(-1)∫_K D_m(2π(2x+a)/L)dx`, with an immaterial orientation convention for a.

Integrating the finite cosine series gives the length term |K|/L≤1 plus the difference of two sine sums divided by2π. The quoted uniform sine-sum bound1+π therefore bounds the trace by `1+(1+π)/π=2+1/π<4`. Four orientations and the half-trace factor give at most8C_0² as claimed. This is a genuine parity payment; the even trace is not identified with half the full trace.

## Leakage, lines269–285

For an interval indicator, |hat(1_K)(r)|≤1/(π|r|). For fixed nonzero frequency difference r, exactly min(|r|,d) input Fourier modes leave the band. Summing both signs gives

`(2/π²)[sum_(r=1)^d 1/r+d sum_(r>d)1/r²]`.

Using H_d≤log d+1 and the integral bound d sum_(r>d)r^−2≤1 gives β_m exactly as printed. Each truncated shift is an interval multiplier times a periodic unitary shift; that unitary preserves Π. Minkowski in Hilbert–Schmidt norm over both orientations and all coefficients gives squared leakage≤4β_m C_0².

The even leakage really is no larger than this full-band leakage: on even input, B remains even, so its component inside Π but outside Π_E is zero. Thus `(1−Π_E)BΠ_E=(1−Π)BΠ_E`. The Pythagorean identity in lines282–284 is valid for the self-adjoint real-coefficient B. There is no missing odd-mode leakage term.

## Consequences (3.1)–(3.3)

Combining the three independent payments gives exactly E_B. For a single atom the first part of(3.4) has no off-diagonal node pairs, so there is no W payment. The same-orientation term is≤b_L c_n², parity≤8c_n² and leakage≤4β_m c_n². Summing proves E_D as printed, and subtracting the arithmetic diagonal gives(3.3). No silent repair or constant enlargement was required.

## Explicit falsification attempts

`geometry_checks.py` independently applies each truncated shift to Fourier modes and integrates their piecewise amplitudes, then constructs the compressed matrix by exact exponential antiderivatives. It does not call the source engine or use the asserted trace identity to construct the left-hand side. The checks include arbitrary shifts and signed coefficients, the half-turn endpoint example, and logarithmic nodes n=2,…,m for m=2,…,20. Separate single-atom checks test(3.2), including n=m.

The JSON records floating-point diagnostic residuals and bound comparisons. These numerical tests are not interval certificates and are supporting falsification attempts; the algebraic derivations above provide the bounded paper audit. The initial JSON serialization hit a NumPy boolean API issue, corrected without changing any mathematical formula.

Input SHA256: `8eab38983c7aa4c12efca4f3f95f57d5e83a4b9a9851ff09f73ccb6d33f63a6a`. Completed72 joint/shift cases and190 single-atom cases. Maximum absolute(3.4) diagnostic residual1.28e−13; maximum parity-identity residual6.40e−14. Every tested(3.1),(3.2),(3.5), parity bound and leakage bound passed.
