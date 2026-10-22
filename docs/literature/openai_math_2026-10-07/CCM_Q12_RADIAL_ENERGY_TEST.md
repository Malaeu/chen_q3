# Post-Q11 test: retaining radial graph energy still loses the original phase

2026-10-22. Root derivation; independent read-only q12_radial_audit bounded PAPER PASS.
Original integer m, L=log m, M=floor(m^epsilon), fixed epsilon>0,
f=Fc with c in the original three-constraint ran(P). No new source.

## Proposed repair under test

Do not discard the entire Q11 graph energy. Instead use the reverse-triangle
lower bound on each graph square, keeping its radial variation exactly, and
pay the full residual by its pointwise modulus. Allow every measurable
position-dependent Hilbert-valued field v_n(t), sum_n||v_n(t)||²=1 a.e.
This is stronger than Q11's constant-profile cap plus error, but still loses
relative phases. Fields extend by zero outside [0,L]; f is zero-extended too.
Let N be any finite auxiliary graph size, not necessarily polynomial in m.

Write a_d=Lambda(d)/sqrt(d), h=log d, v_n=0 for n>N, and

 kappa_d(t)=sum_(nd<=N) <v_n(t),v_nd(t+h)>,
 sigma_d(t)=sum_(nd<=N) ||v_n(t)|| ||v_nd(t+h)||.

Then |kappa_d(t)|<=sigma_d(t)<=1 on active overlaps. Missing graph edges
have both coefficients zero. D_v[f]=integral sum_n d_N(n)||v_n(t)||² |f(t)|².
Here d_N(n)=log n+sum_(2<=d<=N/n) Lambda(d)/d.
The full original Q11 identity remains S[f]=D_v[f]-E_v[f]+R_v[f].

Define the radial energy over ALL graph edges, including d>=m:

 E_rad[v,f]=sum_(nd<=N) Lambda(d) integral_R
  (||v_nd(u+log(nd))|| |f(u+log(nd))|
   -||v_n(u+log n)|| |f(u+log n)|/sqrt(d))² du.

Reverse triangle gives E_v>=E_rad. Expand this scalar square, without
removing either diagonal, to get exactly

 D_v[f]-E_rad[v,f]
 =2 sum_(2<=d<m) a_d integral_0^(L-h) sigma_d(t)|f(t)||f(t+h)|dt.

The residual is bounded by

 R_v[f]<=R_abs[v,f]
 =2 sum_(2<=d<m) a_d integral_0^(L-h) |1-kappa_d(t)| |f(t)||f(t+h)|dt.

Thus S[f]<=B_v[f]:=D_v[f]-E_rad[v,f]+R_abs[v,f]. But pointwise

 sigma_d+|1-kappa_d| >= |kappa_d|+|1-kappa_d| >=1,

so for EVERY field, graph size and original admissible f,

 B_v[f]>=S_abs[f]:=2 sum_(2<=d<m) a_d integral |f(t)||f(t+h)|dt. (A)

This is a statement about the derived majorant B_v, not a lower bound on S.
The modulus function need not belong to ran P; it is only evaluated as a
nonlinear majorant of an original f. No substitute source is introduced.

## Genuine obstruction on original P, using actual primes

Use exactly the already audited Q03 five-mode unit probe f_e/||f_e||:

 f_e(t)=-3/4+(1+4w²)cos(wt)-(1/4+4w²)cos(2wt), w=2pi/L.

It satisfies endpoint and both exp(+-t/2) constraints. For L>=2pi, the
existing CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md proves uniformly

 2 integral f_e(t)f_e(t+log n)dt / ||f_e||² >= kappa L^-9

when exp(-1/2)m<n<=exp(-1/4)m. Absolute products dominate these real products.
All terms of S_abs are nonnegative. Hence that same fixed-width prime block
and unconditional PNT imply, for all sufficiently large integers m,

 B_v[f_e/||f_e||]>=S_abs[f_e/||f_e||]>=c sqrt(m)/L^9. (B)

Constants/threshold independent of field and graph N. Fixed epsilon ensures
M>=2 eventually. Thus no choice of these fields can make THIS radial-energy
plus pointwise-absolute-defect certificate sub-half-power, even on original P
or a cofinal subsequence. This does NOT prove a lower bound on full CCM,
T_gtR, or S. Negative inter-block/phase contributions were lost in B_v.

The PNT input pi(x)~x/log x was freshly checked in NIST DLMF27.12.5:
https://dlmf.nist.gov/27.12#E5 . No RH assumption or short-interval PNT.

## Exact surviving credit and actual impasse

There is an exact nonnegative phase credit C_v=E_v-E_rad and defect credit
J_v=R_abs-R_v. Therefore S=B_v-C_v-J_v. Explicitly on each active overlap,
with z=conj(f(t))*f(t+h),

 C_v=2 sum a_d integral (sigma_d |z|-Re(kappa_d z)),
 J_v=2 sum a_d integral (|1-kappa_d| |z|-Re((1-kappa_d)z)).

Both integrands are nonnegative. Their sum is
2 sum a_d integral[(sigma_d+|1-kappa_d|)|z|-Re z], exactly B_v-S.
Estimating this credit from below by B_v minus the desired budget is the
original hard inequality, not a new supplier. All mixed mode products remain
in z until the precisely identified radial/modulus step.

Outcome: reject this particular phase-blind joint repair. One substantive
post-Q11 attempt; the credit identity is its diagnosis, not a second attempt.
Rollback before replacing vector squares by radial squares and before taking
absolute defect. A successful new mechanism must exploit relative phases
across actual prime powers/blocks on original P; merely optimizing fields or
requiring the restated lower credit is not progress. No full exponent gain.

## Audit and decision

Independent readonly q12_radial_audit PASS: all edge diagonals, reverse
triangle, full defect, original-P probe, fixed-ratio PNT, uniformity in
fields/N and cofinal scope checked. Requested explicit d_N added above.
No numerical, Lean or Arb run; no new actual source table.
Shelf q12_shelf_joint identified the prior raw-block and cap no-go and
projection-only Mellin test; this extends the certificate obstruction to
position-dependent fields retaining radial energy. It is not a new proof
of the already known raw-block lower bound. ask.sh phase-credit query
returned INCOMPLETE (semantic freshness), not global absence.
Actual impasse: no source-specific lower estimate for combined phase credit.
Owner scenario permits Pro review at this impasse, without fabricating three
attempts. Ask for a quantitatively distinct phase-sensitive mechanism or
a justified rollback, not a renamed credit hypothesis.
AUTOPSY: dropped=COUPLING; note=Radial graph squares and absolute defect lose relative phases and dominate the actual positive modulus form.
