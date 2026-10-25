# Q17 — resolvent terminal pairing survives; no arithmetic power gain

2026-10-25. Q17 completed naturally (UI: worked30m58s); Original file downloaded
and read completely, all1251 lines including six embedded files. Archive:
PROSHKA_CCM_ZERO_SELECTIVE_PAIR_Q17_VERDICT_2026-10-25.md,
89445bytes,1251LF, SHA256
5d6616bd696887491170b847d09f1afd4d84f8581498264929c505732e73b35b.
Byte-identical to Downloads; original unchanged. Request126407bytes/1919LF,
seven complete sources. Original N=m,L=log m,M=floor(m^epsilon), SAME P,
0<epsilon<1/32; both time signs, separately normalized actual separators,
all prime powers and all mixed/boundary terms retained. RH and goal OPEN.

## Root bounded mathematical check

Fix the hypothetical zero w=delta+i gamma,0<delta<1/2,multiplicity r,
and v=-conjugate(w). All zero-selective claims below are CONDITIONAL on it
and on the accepted full Weil/source receiver, not numerical evidence of a zero.
F0=(partial²-1/4)G, c_z=d_z(z²-1/4). The partner has its own c_v.
The stable inverses are causal for w, anti-causal for v with factor(-1)^r.
Their L2 costs delta^(-r)||F0||/|c_z| are constants for fixed w, not uniform
as delta tends to zero. The finite terminal polynomials in original(3.5)
follow by differentiating their horizon and checking horizon zero.

Finite forcing integrals are in the radical of the FULL Weil form.
The last division at w removes a zero of order r and has removable value1.
Hence the actual terminal terms satisfy W(E_w^A,E_v^B)=r, while their
self-pairings vanish. Expanding the four pairings loses none: the other
three are zero by the full radical, not by separate prime cancellation.
The translated/phased terminal pair has W=-2r exp(2delta a).
Derivative transfer gives -partial+conjugate(w)=-(partial+v): one resonance,
not two coercive conditions. The homogeneous solution is fixed by actual
normalization, not eliminated by zero forcing or an unweighted decaying tail.
Thus L2 convergence does NOT justify improper radical transfer (4.9).

For the finite prime cutoff, L2 continuity does justify both inverse integrals.
Their beta convolution gives order2r and coefficient
kappa=(-1)^r/(conjugate(c_w)c_v):
 J(a;m)=kappa integral_0^infty u^(2r-1)/(2r-1)! exp(-conjugate(w)u)
        H_m(2a+u)du,
 H_m(y)=sum_(n<=m) Lambda(n)/sqrt(n)[R0(y-log n)+R0(y+log n)].
R0 is the correlation of the ONE actual F0. Both signs and every prime power
are inside the integral. Replacing H_m by its absolute norm gives only
 |J|<=12||F0||² sqrt(m)/(|c_wc_v|delta^(2r)).
This is a completed price, not a lower bound on the actual signed source.
The finite-cutoff tail beyond U=L-2a+2log L is o(1), but its bulk is unpaid.

The absolute infinite-prime interchange obstruction (7.1) is unconditional:
R0(0)>0 and continuity give a positive neighborhood; the opposite-time
correlation tends to zero. Near u=log n-y, even the sum of both time signs
therefore has modulus bounded below. Its integral costs at least
c Lambda(n)n^(-1/2-delta)(log n)^(2r-1). The series diverges since
sum_(n<=x)log n <= x sum_(d<=x)Lambda(d)/d and the left side/x grows.
No PNT or hypothetical zero is needed for this absolute-integrability test.
It excludes only this absolute interchange, NOT conditionally convergent
signed cancellation or any actual spectral upper/lower bound.

## Original-P return and complete consumer budget

The entire pair is cut off, Fourier-truncated and corrected by the same P.
All cutoff commutators are retained before projection; P is not presumed to
commute with the differential inverses. One fixed q>1/epsilon+2 makes
1+epsilon(1/2-q),1/2+epsilon(3/2-q),1/2+epsilon(1-q) negative.
The inherited full-form, contact and direct-prime errors are uniformly o(1).
For the terminal discriminator choose A=log L/4. Its profile centers remain
3log L/4 from the window edge, so the full cutoff cost is
m^C exp(-c L^(3/2))=o(1). The same Fourier/contact estimates apply.
After return y_m belongs to original P, ||y_m||²<=C_w L^(-delta/2), but
 y_m* K_m y_m=-2r m^delta/L^(2delta)+o(1).
This is an inherited conditional adverse witness with its terminal price
made explicit, not a new favorable theorem. Small L2 norm does not pay it.

The sharper already-existing averaged price remains
 average K >= -C_w[sqrt(m)/(L T)+L+1]-rho_S, rho_S=o(1).
At T comparable to L this is O_w(sqrt(m)/L²+L), whereas the adverse signal
is comparable to m^delta/L^(2delta+1). The power deficit1/2-delta remains.
Archimedean cost D_w(50L+8) is charged ONCE. No short-sector fee is added
to direct K; only if recovering T_>R from S add the old short fee once.
Uniform fallback: PK_mP >= -[12sqrt(m)+50L+8]P.
Conditional3/8 still depends on ZF78; unchanged, not used here.

## Disposition and next admissible fork

Stop the improper radical-inverse shortcut and automatic absolute interchange.
Do not stop the CCM route or infer actual half-power spectrum from these prices.
Rollback before zero-selective division to finite theta-forcing H_m, or to
original one-sided S_m. H_m is a representation, NOT a newly supplied bound.
Any next attempt must name an independent directed arithmetic inequality,
retain finite m, both times, phase and terminal polynomial, and improve its
FULL return before invoking norms. Reoptimizing inverse horizons, repeating
the adverse identity, or renaming B_T is not a new mechanism.
No automatic Q18; no new numerical zero, Lean/Arb or full spectral run.

## Independent audit and replay

Independent read-only q17_verdict_audit: bounded PAPER PASS, no material defect.
Reviewer independently derived anti-causal sign, joint beta factor, four-term
terminal pairing and scoped absolute-divergence proof, then checked fixed-q
powers and the changed 3log L/4 cutoff margin in original-P(8.4). Arch paid
once; all prime powers and cross terms retained. This accepts inherited
S4-S6 inputs, not a new audit of the entire Q3 lineage or proof of RH.
q17_replay extracted the six supplied files without source edits and executed
both scripts with existing riemann_env Python / SymPy1.14.0. Both exited0;
354 exact local controls PASS. results.json and source_verification.json
are byte-identical to the supplied JSON (root also compared both). All seven
frozen source byte counts/hashes match. No dependency installation.
These finite controls test the implementation, not universal asymptotics.
Expected bodies, executed scripts and actual outputs: q17_verdict_checks/.

Q17 fully processed; no Pro response remains pending. Remove ccm-q17 monitor.
One scoped cycle commit preserves all foreign changes; no automatic Q18.
The general mathematical goal remains OPEN.
