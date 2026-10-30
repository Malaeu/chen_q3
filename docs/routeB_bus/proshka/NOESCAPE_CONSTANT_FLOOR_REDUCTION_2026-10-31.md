# Constant lower floor: a stronger consequence of the existing source returns

Status: own PAPER consequence, bounded independent review PASS. RH remains OPEN.
Keep the original even CCM A_m, N=m, L=log(m), physical identity L2 norm
and Fourier projection P_m. No modified operator or carrier is introduced.

## Inputs already proved at bounded PAPER scope

- CONFINE §4.1: an off-critical zero supplies a fixed real even compact smooth
  phi with k[phi]=-nu<0. The separate odd construction is also available.
- CONFINE §4.2, (4.5): t_m=P_m phi converges to phi in L2 and
  k[t_m] tends to -nu on ALL sufficiently late original cells. The estimate
  retains every prime power, both poles, endpoints and the archimedean tail.
- CONFINE §2 density and NOESCAPE L1, (2.1): finite even theta jets are dense
  in even L2, and for EACH FIXED finite combination r,
  s_m=P_m r tends to r and ||A_m s_m|| tends to zero.
  Fixed-order constants are allowed; no increasing-order bound is used.

Original files: PROSHKA_VERDICT_CONFINE_2026-10-30.md and
PROSHKA_VERDICT_NOESCAPE_2026-10-30.md, with their existing audit records.

## Claim: an off-critical zero forces lambda_min(A_m) to minus infinity

Fix an arbitrary C>0. Choose a FIXED finite even jet r with

 ||phi-r||² < nu/(4C).

Only after choosing r let m tend to infinity. Put w_m=t_m-s_m. It is real,
even and lies in the same original finite carrier. Hermiticity gives

 k[w_m]=k[t_m]-2 Re<t_m,A_m s_m>+<s_m,A_m s_m>.

The last two terms tend to zero, since t_m and s_m have bounded L2 norms
and ||A_m s_m|| tends to zero. Thus k[w_m] tends to -nu, while

 ||w_m||² tends to ||phi-r||² < nu/(4C).

For every sufficiently large m, simultaneously

 k[w_m] <= -nu/2,       ||w_m||² <= nu/(2C).

Negative energy ensures w_m is nonzero. The admissible normalized competitor
u_m=w_m/||w_m|| therefore has k[u_m]<=-C. Exact bottom minimality supplies
lambda_min(A_m)<=k[u_m]<=-C. Since C was arbitrary, lambda_min(A_m)→-infinity.
The subtraction is exact in the FULL finite form: the mixed term is bounded
using the full operator residual, not dropped or replaced by a tail norm.
No need to compute a limiting shape of a bottom, and no growing jet order
is interchanged with m. The same proof uses odd derivatives and the separate
odd negative witness in the odd sector.

## Consequence and exact unpaid source inequality

RH is equivalent, at this inherited PAPER scope, to existence of ANY finite
C and unbounded set M of original cells such that

 lambda_min(A_m) >= -C,   m in M.

RH gives nonnegative literal forms by the inherited explicit formula.
Conversely, the divergence just proved rules out this constant floor if
an off-critical zero exists. This improves the required bound from o(1) to
O(1); it does NOT supply that bound or prove RH.

Writing Prime_m[f]=sum_(2<=n<=m) Lambda(n)/sqrt(n) Q_ff(log n), the even source is

 k[f]=H[f]-c_*||f||²-Prime_m[f]+|<p,f>|².

An actual coefficient-level supplier would be a fixed C1 with

 Prime_m[f] <= H[f]+|<p,f>|²+C1||f||²

for every original even carrier f on one unbounded set of cells. All prime
powers and the positive pole stay together; no positivity of Prime_m[f] is used.
The already proved absolute operator majorant grows with m and does not pay
this O(1) target. The displayed source bound is itself RH-equivalent here;
renaming it semiboundedness or Gårding is not a proof or a new supplier.

## Controls and limits

The actual escaping radical trials have k[q_m]→0 and tiny residual. They
are consistent with any fixed negative floor and do not test it. Under the
off-critical hypothesis their excess k[q_m]-lambda_min(A_m) now tends to
+infinity; small residual is especially far from exact minimality in this case.
Abstract control: A_m=-m|e_m><e_m| on l2 converges strongly in resolvent to0,
has a dense finite-sequence core with eventual zero residual, and bottom -m.
The unit trial e_(m+1) has zero energy/residual and excess m. This is not CCM;
it excludes a conclusion from strong-resolvent convergence alone.

This is a conditional source consequence and a simpler sufficient entrance,
not a strict competitor contradicting an actual CCM minimum. Uniform
semiboundedness remains the unpaid estimate. Bounded spectral-window results
cannot handle a bottom escaping to minus infinity without another hypothesis.

## Verification

Read-only localize_radical_audit checked the full draft against CONFINE
§§2,4.1–4.2 and NOESCAPE L1: fixed-r quantifiers, mixed/self terms, normalization,
all-late-m conclusion, constant-floor equivalence, source slack, radical-trial
excess and the separate odd variant. PASS at inherited PAPER scope.
Reviewed draft SHA256: ffc27660ca943bdd931d04ed8baa312fb6ff3bf850af79ecbeb67f8255721caa.
The only subsequent mathematical-notation edit renames the prime quadratic
Prime_m[f] to distinguish it from the projection P_m; no formula changed.
Root independently read the original return estimates and checked the proof.
No Lean or numerical proof is claimed for this quantified consequence.
