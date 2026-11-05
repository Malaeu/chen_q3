# Intake: the raw finite-source Mellin EDGE is excluded

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; RAW_FINITE_COFINAL_EDGE_OBSTRUCTION_ONLY.
Unchanged global target: original full V>=0 on every finite complex row in I,
with the exact RH/Weil consumer. No full-V sign or RH claim is made.

## Exact delivery and source

- Request: REQ-2026-09-16-MELLINEDGE; commit
  6ecf5f173cdf6c7273727c8eaa6a7a558ab0e1a2; SHA256
  4f91d16d58e4914dffb41157512bb38393bda49e0d604f95ef63da1469a3adb8.
- Complete response: c63b1ea7c75a4f1da0a74d29414ac4b758951dd0,
  docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_MELLINEDGE_2026-09-16.md;
  blob 246767843cb6f750a19bef3bbd4428ca16818773; SHA256
  94f91b169de680aade287684c3ca61fbd070fc99aee801be1ef54cb1503feaf8;
  47542 bytes, 530 LF. Read completely, retained without changes.
- Its sole-parent commit is 964c8430fc174646a0726f15dd78f65e268f4380;
  the response commit adds exactly the assigned file. The isolated research
  checkout was advanced by fast-forward only, with no canonical changes.
- The exact-path watcher completed successfully; it was not restarted.
  The user also supplied the matching publication receipt in the same task.

The context SHA256 58c0dc298bc77c016934dc6806caadf25ad4bb286da551cf79aa73ad5113c6d2
was verified locally at preparation and intake. Proshka explicitly records
that it did NOT independently recompute that context SHA; this limit is
preserved. The controlling request attachment round-trip was independently
hash-matched through the app file preview before the reply arrived.

## Accepted mathematical scope

For the literal raw finite density
T_N=sum_(n=1)^N Gamma(2,1)/(pi*n^2) and
M_N(s)=integral_0^infinity t^(s-1)r_N(t)dt, the response proves

    exists N0, for every integer N>=N0 and every T>0,
    exists s with 11/8<Re s<2, Im s>T, and M_N(s)=0.   (I1)

Thus no unbounded subsequence of these finite M_N can be zero-free on the
whole half-plane Re s>5/4. This rejects EDGE itself, not just its stronger
all-N version. No explicit numerical N0, root coordinates, or first bad N
are asserted. N=1,2 retain the previously proved zero-free regions.

The exact preflight identity is retained:

    M_N(s)=4 pi^(1-s)Gamma(s)D_N(s),
    D_N(s)=sum w_Nn n^(2-2s)(s+d_Nn),
    w_Nn=(N!)^4/[(N-n)!^2(N+n)!^2],
    d_Nn=n(H_(N+n)-H_(N-n))-3/2.

Neither the harmonic terms nor the multiplicative relations between phases
of composite integers are omitted in I1.

## Parent reproduction of the new argument

1. ME3-ME5: the factorial product gives w_Nn<=exp(-n^2/N), and on
   n<=2L, L=sqrt(N), its Gaussian approximation has uniform log error
   (4n^3+2n)/(3N^2)<=16/L for N>=16. The former controls the whole tail.

2. ME7-ME10: assign chi_N(p)=+1 up to Y=sqrt(2L), and -1 above it,
   extending completely multiplicatively. No n<=2L contains two prime
   factors above Y, including repeats. Therefore the exact count is
   floor(x)-2 sum_(Y<p<=x)floor(x/p). The elementary Chebyshev and
   factorial proof of the Mertens estimate supplies the uniform scaled
   mean 1-2log(2), with no RH or prime number theorem hypothesis.

3. ME12-ME15: partial summation pays the interior weighted error. The
   singular endpoint costs at most 8 delta^(1/4); the entire outside-window
   sum costs at most exp(-4)/4+1/L after normalization by N^(1/8).
   The strict limiting margin is below -229/1728<-1/8. Hence the claimed
   eventual negative bound is justified, not inferred from sampled values.

4. ME16-ME17: w_Nn<=w_N1 and sum_(n>=2)n^(-2)<=3/4 give
   P_N^chi(2)>=w_N1/4>=1/16. The intermediate value theorem then supplies
   an actual real zero of the phase polynomial in (11/8,2). This polynomial
   is not the original positive real Mellin integral.

5. ME18-ME23: unique factorization gives rational independence of log p
   and arbitrarily high simultaneous phase returns. For each FIXED N the
   full local-uniform error is

       C_(N,K) epsilon_N(tau)
       +(R_K C_(N,K)+J_(N,K))/|tau|,

   where J includes every |d_Nn|. The strict Rouché margin transfers the
   phase zero to a genuine zero of D_N, then M_N, in the stated strip.
   Multiple roots are allowed; no uniform return time in N is assumed.

The external Mertens attribution is supplementary: the response includes
the complete elementary derivation of exactly the two prime estimates
it needs. Gamma nonvanishing is the standard verified DLMF 5.2(i) input.
No theorem about the zeros of this D_N was imported from literature.

## Comparison with the already published parent result

The parent report
docs/Codex/REPORT_2026-09-16_MELLINEDGE_COFINAL_OBSTRUCTION.md,
SHA256 5748be3691ff3308ae700a9697046bbdd3ef4d688cb36cabd0d4c21836319129,
uses a different torus-zero construction: y=N^(2/7), two continuously
variable groups of large-prime phases, mass fraction log(7/4)>1/2, and
stability under the full nonlinear remainder. It gives high zeros whose
real parts approach 11/8. Its proof used unconditional PNT asymptotics.

The response instead uses a single threshold sign, a real sign change,
and an elementary Mertens estimate. Its zeros lie in the open strip
(11/8,2). Both arguments reject the same cofinal global-zero-free interface.
The different constructions do not substitute for checking either proof.
No claim of independent discovery priority is made.

## Decision and next boundary

Accept only ACCEPT_MELLINEDGE_EVENTUAL_RIGHT_ZERO_OBSTRUCTION_ONLY.
The request is answered and this bounded attempt is closed. Preserve the
native full-V/RH goal, all prior source formulas and source-sign counters.

Do not search for another large globally good raw M_N: I1 excludes every
unbounded such subsequence. Do not promote the existence of high finite
zeros to a zero of xi or a negative original V. Local uniform convergence
on fixed compact sets is compatible with the constructed escaping zeros.

The weaker compact-local condition listed in the response remains an unpaid
condition, not the next automatic proof task. Its mere restatement gives
no new source inequality. Before another Proshka dispatch, return to the
existing full-source representations and identify a discriminating source
property and the exact sign mechanism it could supply; semantic similarity
or an invertible new representation is not that mechanism.

No Lean run, canonical admission, full-V sign gain, or RH conclusion.

AUTOPSY: dropped=COUPLING; note=Exact prime-constrained phases produce eventual high zeros of the raw finite Mellin family; local convergence cannot supply global zero-free finite members, and the original full-source sign remains unpaid.

## Independent acceptance

Complete response review SHA256: `0db1bb912fb987fa41358b386319ffe448d25c38d4656a78cd1ac8c0ae6a69ae`.
Complete intake candidate SHA256: `e6b1713c71b2e7a4e630bfc4547bc0725364ab72a4a37e845e83e24fce395329`;
CLEAN_INTAKE review SHA256: `3607404866a8b40e6a2e954a4867e4cdf83491b9c1b81aeb7c4c5032ed530e99`.
Reviewer `/root/sibling5_check` independently checked both exact payloads.
Only the status line and this receipt were added after intake review.
The parent reproduced ME3-ME23, retaining the full harmonic correction,
constrained prime phases, full tails and fixed-N-then-height quantifiers.
