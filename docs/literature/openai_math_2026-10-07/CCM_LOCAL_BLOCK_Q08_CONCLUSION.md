# Q08 — full local blocks and small-prime sieve

2026-10-21. Source: PROSHKA_CCM_LOCAL_BLOCK_Q08_VERDICT_2026-10-21.md,
77920 bytes,1163 LF,SHA256
b1b1f25c6fb9715da11080648c19a111f908cdbcdc971991856e2d7f04530139.
Natural completion observed12:59UTC; downloaded original equals repository
copy byte for byte. Entire original read. Request sent once12:19UTC.
Native goal ACTIVE; RH OPEN; no PX claim. No full exponent improvement.

## Exact source and paid part

Original N=m,L=log m,M=R=floor(m^epsilon), fixed0<epsilon<1/32,
original three constraints and P retained. E is the full four-mode third
finite-difference basis, G_E=E*E, never the identity metric. All16 mixed
terms in E*Q(s)E retained, including coincident indices.

For primorial p_y, mu_y=mu 1_(d|p_y), Lambda_y=mu_y*log,
r_y(a)=1_(a,p_y)=1, the exact identity is Lambda_y=r_y*Lambda.
Delta_y=Lambda_y-Lambda>=0 coefficientwise, including proper powers and
mixed small/rough factors. Original S=S_y-D_y and Kloc=K_y-Kdelta.

Full-k divisor input ||B_md||<=(40+16Omega)/sqrt(d) rederived, not new.
For y=max(2,floor((epsilon L/8)^2)), the entire auxiliary sector satisfies
||S_y||<=(40+16Omega) product_(p<=y)(1+p^-1/2)
<= (40+16Omega)m^(epsilon/4) eventually. Its power is5epsilon/4.
Thus K_y<=u_y G_E with no inverse-basis surcharge. Absolute-row route
would unnecessarily cost49epsilon/4; it is not used.

## What the negative control actually proves

q=first prime>y,n0=2q: Delta_y(n)=0 for n<n0 and Delta_y(n0)=log2.
A compact profile u=(D^2-1/4)h/||(D^2-1/4)h|| on an interval of length
ell=1/(8n0) has both exact exponential contacts. Translates separated by
log(n0), combined with signs +/- and normalized, have raw D_y form
+/-log2/sqrt(n0), whereas their original prime form is zero.

These profiles must be returned to the original Fourier band and P.
Fixed r=ceil(1/epsilon)+2 and h based on x^(r+3)(1-x)^(r+3) give error
rho<=C_(r,epsilon)L^(3(r-1/2))m^(-epsilon(r-1/2)). Full physical norm
||A_delta||<=4sqrt(m)L restores ALL atoms activated by projection.
Relative error is O(m^(1/2-epsilon(r-1/2))L^(3(r-1/2)+2)) ->0.
Hence actual projected D_y has both signs, magnitude at least
log2/(2sqrt(2q)), on every sufficiently late fixed-epsilon source cell.

This falsifies only free coefficient-order -> Loewner-order transfer.
Its signal is inverse logarithmic; it does NOT exclude a subpower lower
floor for D_y and does not establish a large positive eigenvalue of S.
No source CCM route is killed. No effective onset was computed.

Exact exhaustion Delta_y(n)=0 for all n<=m iff2q>m forces the chosen
absolute divisor price Xi_y(m)>=sqrt(m)/(4sqrt(3)),m>=4.
This is a lower bound on the PRICE, not on the actual operator norm.

## Full budget and rollback

Available return remains S<=[u_y+4sqrt(m)L]P, weaker than old12sqrt(m).
Conditional Q03 power3/8 still depends on ZF78. Scalar T pays the short
return once; direct K pays only50L+8; F2 belongs only to the separate V
formulation. None has acquired eta(epsilon)->0.

Rollback: original fixed-cell joint signed pairing BEFORE scalar coefficient
majorization. Keep E*E if local coordinates help, but do not make individual
rows, positive sieve remainder, phase-uniform estimates or separately paid
shells compulsory suppliers. No Q09 merely renaming the unpaid D_y.
A new attempt requires an independent source-specific quadratic-form
mechanism, with its complete return budget, before another review request.
AUTOPSY: dropped=NO_DERIVATION; note=Cheap auxiliary sieve sector leaves full signed correction unpaid; scalar positivity cannot supply operator order.

## Verification and limits

Extracted scripts and registration preserved in ccm_local_block_q08_checks/.
python3 check_q08.py:3733 exact controls PASS; entire result JSON identical
to original, including registration and script hashes. Existing .venv Python
diagnostic_q08.py:3 mpmath65 cases PASS_DIAGNOSTIC_NOT_INTERVAL; entire
JSON identical. No dependency install, Lean, Arb, large prime sums or full
CCM spectra. Tests check finite identities, not the asymptotic theorem.
Root PAPER audit checked scaling, contacts, Gram return, all-atom error,
cutoff and final expenses. Independent q08_verdict_audit bounded PAPER PASS, bound to the original
SHA256 above and HEAD48bd8096. No material defect found in full-k/smooth
budget, same-P both-sign construction, cutoff or absolute-price barrier.
Inherited Q01/Q10 inputs were checked as inputs, not independently reproved.
