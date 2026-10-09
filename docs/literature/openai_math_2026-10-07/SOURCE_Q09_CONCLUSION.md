# Source Q9 — exact centering, identity return; full estimate open

2026-10-09. Source phase9/10, SAME Execute Joint Probe Calculation chat:
https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd .
Terminal response and original attachment observed around02:32UTC. Full982-line
original read. No resend or Answer now; Q10 not sent.

## Evidence

Request PROSHKA_CENTERED_GAUSS_Q09.txt:860793bytes,17820LF,final newline,
SHA25681b4786e16ec7d42735c8888994a2dd53db7ac302cf00f23789709d3ce2195e2.
Baseline7d5dabdabdf0e7d18857c0a4d0cf4ef9cb1e57a3.
Original PROSHKA_VERDICT_CENTERED_GAUSS_Q09.md:88081bytes,982LF,
SHA256c6731c68f31da4ab04cc03dec5fead37d0fab7d3ca435476bf577510c0d42c27.
Pinned paper SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
Original bytes unchanged. Extracted Q09_EXACT_CHECK.py SHA256
4d7c8397ed731736a1086478450dfbaf17833fd0fa4bec66758a0887804b0479.
Root ran venv_djo/bin/python /tmp/Q09_EXACT_CHECK.py on these exact bytes:
195 Fourier,15 Gauss-root,6 CRT,39 principal-mask,4096 cube-pair,
72 phase and12 rational-budget checks:4435 PASS. No analytic certification
follows from finite controls. The identical script is saved beside this note.

## Independent review

Read-only long_positive_alias: scoped PASS for Q9.8, Q9.10–13 and
Q9.25–28. It checked source Fourier conventions (S:9726–9777), completion
(S:7319–7385,9840–9860), exact support, both orientations, d-mask,
normalization, all units/S-prime t values, full identity return and both
independent cube divisor sums. No independent analytic-source certification.

Read-only q05_moment_audit: scoped conditional PASS for §§8–10,13–14.
It checked Q9.15–20 from source S:4707–4725, row-independent coefficients,
exact coprimality expansion, actual scales/external factors, all-ideal
sums, bounded scales and the uniform margin. Q9.32–34 retains the unit
projector, full primitive L-series and finite masked t-polynomial; its
line shift uses source S:1438–1535. Q9.36 profile/tail return is consistent.
Q9.35 is insufficient and Q9.37 is unproved; no full high/SP/RH conclusion.

## Mathematical scope

For r in[28/25,113/100], D=U^r, c=1/10000, H=D^(1+c),
P=(H/U)^(1/6), G=U^(1/100), D U^(-1/100)<=L<=D:

- Q9.8 gives zero for the added formal Gauss diagonal only with the FULL
  annular Fourier kernel and all dual frequencies. The original Mobius
  diagonal remains in the paid Q8 large-gcd range. A frequency truncation
  retains its tail; individual separated modes need not have zero diagonal.
- Q9.10–12 retain all common-prime masks, both character orientations,
  all-ideal t including S, units and the q_d/q_e multiplier. Under full
  divisor inversion lambda_1(d)=1_(d=1), the double transform returns the
  original correlation with coefficient1. This is not a contraction or an
  impossibility theorem for a separate arithmetic bound.
- Both inverse-cube divisor sums are needed in Q9.25–28. Their full product
  kills nonunit completed cube indices; deleting cross terms would replace
  (1-1)^2=0 by1+1=2. Principal completed pairs are not just equal reflected
  indices. No quantitative moving-prime reflection bound is newly admitted.
- Conditional on the source sextic large sieve, Q9.15–20 yield
  |J_(>=B)| << P(UPL)^epsilon B^(-1)[U+L sqrt(U)+(UL)^(2/3)].
  This auxiliary coprimality-divisor tail includes the full g,t,f,a sums.
  At B=U^(27/50), its uniform margin below H U^(-1/200) is at least
  5371/400000, before small divisor/log losses. It is not the whole moment.
- The remaining original correlation has only the previous upper budget
  P[U+U^(1/6)L^(5/6)](UPL)^epsilon. At L=D it misses the proposed target
  by1/200-5rc/6, at least5887/1200000. This is a gap in an upper bound,
  not a lower bound for the actual correlation.

## Exact next candidate

Q9.33 is a finite Gauss-weighted sum B_G(s) of primitive nonprincipal
L-functions, with the exact unit projector, w_P, f divisors and finite
sixth-power t polynomial. No extra S-deletion of its dual rows is allowed.
Ordinary primitive-Hecke continuation/functional equation is an explicitly
separate source premise; the Linux zeta Comparator does not certify it.
Q9.34 returns C_G through Mellin inversion on Re(s)=2/3. There is no division
by an L-function and no assumed zero-free region in this move.

The proposed sufficient input Q9.37 is

    integral |Mellin(tilde rho)(2/3+i tau)| |B_G(2/3+i tau;F)| d tau
      << L H U^(-1/3-1/200+epsilon)(1+T1)^A,

for every required COMMON derivative profile F. It implies Q8(32), then
paid ranges/Sobolev/finite mask return give an inverse moment gain and the
conditional Q7 high transfer. A bound on the full real integral Q9.34 is
weaker and also sufficient. Neither is proved. Separate convexity gives
P U^(1/3)L^(5/3), worse than the existing bound; replacing the finite
t-polynomial by an infinite reciprocal zeta would add an unpaid tail.

## Decision

Do not repeat the unchanged double-Poisson loop or delete a new square's
positive diagonal by appealing to the original centering. The next own
attempt should target coefficient-sensitive cancellation in the exact
joint B_G sum (or the weaker full real integral), preserving all masks and
profile returns. Q10 must follow that attempt, not repeat Q9's representation.
Q8(32), Q9(37), full inverse/high gain and RH/SP remain OPEN. No source
certification, Lean run or Mac Comparator. Deliver this request, unchanged
answer and bounded conclusion in one scoped commit/push, then pause the
response-wait heartbeat. The overall RH goal remains ACTIVE.

AUTOPSY: dropped=THEOREM_SHAPE; note=exact centering removes the formal diagonal but the full double transform has an identity branch of coefficient one; no full moment saving was obtained.
