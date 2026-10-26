# Post-Q46: literal centered-generator Bochner preflight

Status: BOUNDED_PAPER_PASS. No new CCM bound.
Scope: test the literal translation-generator transfer of the September
Poisson/Bochner mechanism, not all possible auxiliary compensators.
Sources: docs/Codex/REPORT_2026-09-13_COMPENSATION_COUPLING_HUNT.md
(J1, endpoint conditions and source mismatch), CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md,
CCM_Q09_AUTOCORRELATION_PREFLIGHT.md and CCM_Q46_CONCLUSION.md.

## Exact original source

Keep m>=2, L=log m, original sparse P, f=F c extended by zero.
On s in [0,L] put
 dnu(s)=sum_(2<=n<=m) Lambda(n)/sqrt(n) delta_(log n)(ds)-exp(s/2)ds,
 b=nu([0,L]),
 J_nu=integral (2I-T_s-T_-s)dnu(s).
Both measures are finite. These bounded operators on full L2 satisfy
 C0=P F* (2b I-J_nu) F P,
 <f,J_nu f>=integral ||f-T_s f||² dnu(s).
All shifts, actual prime powers, complex cross terms and cutoff atoms remain.
This is Q28 energy bookkeeping, not new arithmetic progress.

## Specific failed hypothesis of the literal lift

A symmetric positive-jump Markov generator would be L_nu=-J_nu.
Our actual centered measure is not a positive jump measure. This is not only
a missing proof: the literal operator violates the positive maximum principle.
Choose nonzero smooth h<=0, even, supported where a<|t|<b0,
with 0<a<b0<log 2. Then h(0)=0 is a global maximum; all discrete shifts log n
miss its support, while
 (L_nu h)(0)=-2 integral_a^b0 exp(s/2) h(s) ds >0.
Thus the literal centered convolution operator is not a Markov generator.
This test uses the actual arithmetic support, not altered prime masses.
The test h is NOT asserted to lie in original ran P: the conclusion concerns
only a proposed full-space Markov realization before compression. It is not
a positive eigenvalue witness, an original-P no-go or a ban on another realization.

## Full return if only the positive discrete generator is retained

Let Bd=sum Lambda(n)/sqrt(n), Bc=2(sqrt(m)-1), and Ed,Ec be the
nonnegative separate translation energies. Exactly
 <c,C0 c>=2(Bd-Bc)||c||²-Ed+Ec,
 Ec=2Bc||c||²+<c,H_decay c>, 0<=H_decay<=4P.
Dropping Ed therefore gives C0<=2Bd P+H_decay. Consequently
 A_prime=C0-H_decay<=2Bd P<=12sqrt(m)P,
 T_gtR<=(12sqrt(m)+b_div)P,
 PKP>=-(12sqrt(m)+50log(m)+8)P.
This completed transfer retains half-power and is weaker than the inherited
6sqrt(m)+6m^(1/4) allowance, which remains in force. H_decay is not paid twice.
No rounding, finite numerical experiment, Lean or Arb is involved.

## Decision

Do not invoke the September positive-diffusion Bochner identity for this
literal centered generator. Keeping its positive discrete part restores
exactly the old Q28 unpaid energy comparison. The September identity for theta V
still has no mapped source equation for C0. This is a concrete hypothesis
screen attached to an already known mechanism, not three new failed attempts.
A different source-derived state equation must be exhibited before using
Bochner positivity; defining its compensator by the desired bound is circular.
Original all-P goal remains OPEN. No Q47 sent.

Independent q44_bounded_audit: bounded PAPER PASS, no material findings on
pre-status-update SHA256 db077925d01c51642a767477734557cc06ffe2262ea5fd45708c7c4a4ebcdce5.
Checked signed-generator identity, actual-support maximum-principle witness,
limited scope and single H_decay return. Inherited kernel identities assumed.
