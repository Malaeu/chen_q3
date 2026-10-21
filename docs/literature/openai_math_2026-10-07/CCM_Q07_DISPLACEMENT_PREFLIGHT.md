# Fixed-cell displacement preflight: low rank is not a signed upper bound

2026-10-21. Root own attempt after Q06; independent read-only fixed_cell_displacement_preflight bounded PAPER PASS.
Original L=log m, M=floor(m^epsilon), fixed epsilon, original P and frequencies.
Use the complete actual centered measure
 dnu=sum_(n<=m) Lambda(n)/sqrt(n) delta_log(n)-exp(s/2)ds, 0<=s<=L.
Let A=int Q_L(s)dnu(s), a_j=int sin(2pi j s/L)dnu(s), and
 d_j=2int(1-s/L)cos(2pi j s/L)dnu(s).
Then A_jk=(a_k-a_j)/(pi(j-k)) for j!=k, A_jj=d_j.
All prime powers and source cross terms remain. PA_primeP=PAP-PH_LP
by the accepted continuous identity, ||H_L||<=4. Do not confuse this measure
with Q10's measure which additionally includes exp(-s/2)ds and returns2H.

For J=diag(j), directly
 [J,A]=(1 a^T-a 1^T)/pi, rank<=2.
Since P1=0, P[J,A]P=0. But with E=I-P, exact multiplication gives
 [PJP,PAP]=-PJEAP+PAEJP.
The two leakage terms are adjoints with opposite signs and are NOT zero.
Their rank is at most6 because rank E<=3; their size is not bounded by rank.
Even if they vanished, commuting would only supply simultaneous spectral
coordinates, not an upper bound on the eigenvalues. Adding tI to A preserves
[J,A] and all compressed leakage while shifting PAP by tP. This elementary
relaxed-class counterexample excludes inference from displacement data alone;
it is NOT a claim that the actual arithmetic source permits such a shift.

A source-level warning already exists: the actual static raw shell of
CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md obeys the same displacement identity
and P1=0, yet its compression has a positive c sqrt(m)/log(m)^9 direction.
This is a subsource, not the full centered A; no full-source lower bound follows.

The full divided-difference representation is already Q10§6 equation(21).
Its Hilbert norm transfer is dimension-free and bounds by a scalar twisted
prefix supremum. It already loses precisely the source-dependent sign we
need. Rebranding it as displacement, Loewner or Pick does not supply that sign.
A source-derived one-sided comparison could still work, but neither low rank
nor a presumed Herglotz property is such a supplier. No new full exponent.

Decision: do not implement a low-rank spectral shortcut. At this concrete
impasse request a same-chat strategic backtrack with the complete Q01–Q06
failure map, requiring a non-equivalent source-specific mechanism and full
return, or a precise statement that none was derived. Do not invent three
successful attempts or present a repeated identity as progress.

AUTOPSY: dropped=THEOREM_SHAPE; note=rank-two displacement survives but compressed leakage and diagonal spectrum remain unpaid; generic low-rank-to-upper-bound implication invalid, actual full source open.
