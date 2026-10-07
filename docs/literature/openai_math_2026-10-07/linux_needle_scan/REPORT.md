# Full-corpus mechanism search: a bounded CCM receiver

2026-10-07. Linux complementary research; Mac retains main Q3 execution.
Q3 baseline: `2138e29c9cb9be900ed9b701f109899280e6c90c`.
OpenAI source: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Status: research candidates only; SP OPEN; CHALLENGER_NOT_RH; PX_RH_CLAIM: NOT_MADE.

## Coverage and limits

All 7,729 TeX files in 722 manuscript directories were downloaded and checked against Git blob hashes (zero mismatches). See `integrity.json`, `tex-sha256.json`, and `mechanism-screen.json`. Full-text mechanism screening is not a proof audit of 722 papers. No external Lean code was executed. Existing Mac results in `../REPORT.md` and `../DIRECT_Q3_THEOREM_TRANSFER.md` are not new discoveries here. Repository `ask.sh` searches had an incomplete semantic index, so they cannot certify absence of previous work.

## Best next operation: moment growth independent of moment order

Source: [Ramanujan graphs, early.tex](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Deterministic-nonbipartite-Ramanujan-graphs-in-every-fixed-degree-September-23-2026/build/sections/early.tex), lines 1030–1060, 1315–1322.
Exact source phrase: “a constant C_*, independent of every sufficiently large even order p”. The high-moment lemma uses

`Z_p = 1 + F_p + kappa_p D_p`,
`E Z'_p <= (1 + C_*/l + u_l) Z_p`, with summable `u_l`.

The useful operation is asymmetric weighting of two coupled nonnegative accounts: forward leakage `C_p F_p/l` is controlled by choosing `kappa_p C_p <= 1`; reverse leakage `C_p D_p/(kappa_p l²)` is summable for each fixed p. Each account's own nonsummable drift still needs an order-independent bound. The paper assumes a constrained pairing process, bootstrap estimates, conditional averaging, and selection of a next pair. These are NOT available for deterministic prime-driven CCM merely by analogy. The external proof has not been certified here.

For the literal full matrix K_m, N=m, L=log m, bounds

`Tr((K_m^-)^p) <= C_p m^c (log m)^(A_p)`

for arbitrarily large fixed even p, with c independent of p, imply SP: take p-th roots and then choose p large relative to a given eta. This criterion alone is a reformulation, not a new estimate. Using `Tr(K_m^p)` instead would additionally control the positive spectrum. The negative part has no established entrywise prime expansion. Negative control: diag(-m^(3/8),0,...) has moment m^(3p/8), so a fixed-power zero-free floor does not supply the required uniform exponent.

## Actual source calculation: where compensation is needed

Primary definitions: `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean:40–101` and `CCMFiniteWeilSourceMatrix.lean:20–41`. Fix N, keep all modes -N,...,N, replace log m by continuous L>0 and the prime cutoff by q<=exp L. This defines an auxiliary interpolation K_N(L), agreeing with the literal source at integer m. It is not a new definition of the production family N=m.

At L0=log q, for a prime power q, the literal kernel satisfies

`Q_L0(n,k;L0)=0`,
`partial_L Q_L(n,k;x)|_(L=x=L0)=2/L0`.

Proof: on the diagonal differentiate `2(1-x/L)cos(2*pi*n*x/L)`; at x=L the cosine is 1 and the prefactor vanishes. Off diagonal differentiate `[sin(2*pi*k*x/L)-sin(2*pi*n*x/L)]/[pi(n-k)]`; both cosines are 1, leaving 2/L. Thus the matrix is continuous, while its one-sided derivative jump is

`[K_N']_L0 = -2 Lambda(q)/(L0 sqrt(q)) * 1 1*`.

The pole and archimedean terms are smooth locally for L>0: their only integration endpoint singularity at x=0 is removable, with a smooth extension in L. No other cutoff atom changes there.

For p>=2 put M_p=Tr((K_N^-)^p). The scalar function max(-x,0)^p is C1, including at zero. The finite-dimensional trace derivative gives

`M_p' = -p Tr((K_N^-)^(p-1) K_N')`,
`[M_p']_L0 = 2p Lambda(q)/(L0 sqrt(q)) * 1* (K_N(L0)^-)^(p-1) 1 >= 0`.

This is an elementary PAPER calculation, not a Lean theorem or a gain in SP. It identifies the exact order-p prime input a coupled-account construction must pay. Smooth motion includes the older prime terms as well as pole and archimedean terms. On the actual N=m schedule, adding modes and their cross couplings must also be paid; fixed-N differentiation does not solve this. At m -> m+1 the new boundary atom has value zero, but all older entries change with L.

## Other candidates and failed direct receivers

* [Matrix Lieb–Thirring, trace.tex](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/build/sections/trace.tex), lines 25–45, 286–288, 383–390: exact signed trace identity with nonnegative square remainders. Requires `(sI-B)^2+V >= bI` for all real s and a derived matrix N>=0. Setting B=0,V=K_m assumes positivity at s=0 and is circular. Q3's high-frequency kinetic growth is logarithmic, not quadratic; signed prime translations are not a pointwise potential. Useful identity pattern, no imported floor.
* [Polynomial differences at primes, descent.tex](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-October-5-2026/build/sections/descent.tex), lines 152–172, 356–481: exact progression-fiber identity and positive-density good assignments yield a contracting recurrence. Missing for Q3: an exact full-source fiber identity, admissible cycle and positive good-assignment proportion. The source yields a fixed power saving, not every-eta SP.
* [Ashkin–Teller, 04-spectral.tex](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-joint-scaling-limit-of-critical-Ashkin-Teller-currents-September-25-2026/build/sections/04-spectral.tex), lines 63–110, 205–213: local positive Gram matrices construct a positive contraction and positive spectral measure. No such representation established for arithmetic signed jumps. Positivity of a shifted function alone does not survive inverse shift: for F=1-cos t>=0, the zero-initial-data solution of G''=exp(ht)F'' changes sign for h>0. Thus this is not a free downshift of Psi_(3/8).

## Concrete next test and stopping condition

Attempt a deterministic pair of nonnegative accounts for the actual full CCM negative moments and the boundary channel `1*(K_N^-)^(p-1)1`. Derive their exact evolution before estimating absolute values. A successful receiver must (1) pay the displayed prime derivative jumps using actual signed source relations, (2) include old-entry L motion and new-mode couplings on N=m, and (3) make every nonsummable growth coefficient independent of p. Dependence on p in fixed prefactors or summable errors is allowed. A mere bound C_p/l in the main drift fails this test; so do random pair selection, assumed positivity, or a fixed power saving. If no second-account identity can be obtained, record this receiver as stalled rather than claim that the moment criterion advanced SP.

No new Proshka question was sent. The owner subsequently requested commit/push for Mac intake; NEXT.md receives only a handoff pointer, preserving the active route. The search yields a prioritized mechanism and an exact source input, not a proof that a usable needle must exist.

## Independent check

Native reviewer `/root/needle_final_check` checked report bytes SHA256 `647f6630390481c2924088bf73905a5ebee9be5577d958f9d5f79f03e00449b3` before this review receipt and owner-authorized handoff wording were added. One pass: no substantive findings. Independently confirmed the kernel derivative, rank-one jump, negative-moment trace chain rule (including zero eigenvalues), removable archimedean endpoint, and faithful conditional use of the Ramanujan mechanism. This checks the local PAPER calculation and source mapping, not the external full proofs or SP. Mac retains ownership of mathematical integration.
