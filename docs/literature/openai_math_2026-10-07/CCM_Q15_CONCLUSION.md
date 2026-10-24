# Q15 — actual Möbius energy and the exact separated-row barrier

2026-10-24. Natural completion 10:15 Europe/Berlin, retrieved after 10:30 poll.
Full original read through all 1294 lines; 73140 bytes, SHA256
ed8c7e4041c5b2a6f871815455262abb4d33c3fcb812b6451499b3945f55e9d9.
File: PROSHKA_CCM_VAUGHAN_JOINT_Q15_VERDICT_2026-10-24.md.
Archive is byte-identical to Downloads. All 12 request source hashes match disk.
Original N=m,L=log m,P and fixed 0<epsilon<1/32 preserved; RH OPEN.

## Reproduction and audit scope

Lossless FILE_BEGIN extraction into q15_verdict_checks/. Ran check_q15.py,
source_replay/check.py and diagnostic_q15.py. All three output JSON files
byte-identical to embedded results (retained as *.expected.json).
7801 new exact controls,8192 inherited formal-log controls,3 noninterval
original-kernel diagnostics at 50 decimal digits. No Lean/Arb/spectral proof.
System Python lacks mpmath; cached `uv run --offline --with mpmath==1.3.0
python .../q15_verdict_checks/diagnostic_q15.py` succeeded without installation.
The original failed test expectation nu_2(4)=1 is preserved in failed_control.json;
correct nu_2(4)=0 and nu_3(6)=1 pass. No original bytes were repaired silently.
Independent read-only q15_verdict_audit: bounded PAPER PASS, no defect found
in §§2.1–2.2,(4.2),(5.1),(6.1),(8.2)–(8.5). Root agrees.
Scope: Hermitian original projected kernels, fixed epsilon, exact hyperbola;
short-sector/archimedean/receiver inputs inherited, not a re-audit of all Q3.
Reviewer checked both orders of noncommuting products and zero-row infima.
Only the separated-row certificate shape is excluded; actual CCM remains OPEN.

## Root calculation

Actual nu_U(a)=-sum_(d|a,d<=U)mu(d), for a>U. The floor and harmonic
LCM identities retain every d,e; subtraction of the a<=U segment is exactly 1.
Totient diagonalization yields 1/(3H_U)<=q_U<=H_U^3. These are coefficient
energy bounds, not signed matrix bounds.
For H_a=sum_(b>V,ab<=m)Lambda(b)A(ab)/sqrt(b), alpha_a=nu_U(a)/sqrt(a),
II=sum alpha_a H_a. Expanding both orders of each product gives exactly
Z_tau E_tau-II^2=sum_(a<a')tau_a tau_a' (alpha_a H_a'/tau_a-alpha_a' H_a/tau_a')^2.
Intermediate P, both time signs, all b,b' and a,a' products remain.
The positive defect is discarded by an explicit inequality, never set to zero.

After ||H_a||<=2 B_a, minimizing ALL positive scalar weights yields
s*=2 sum |alpha_a| B_a. This is a certificate, not lambda_max(II).
For x=sqrt(m)/4, ordinary PNT gives >=x/(2log x) primes in (x,2x].
Distinct ordered pairs have nu_U(p)=-1,Lambda(q)=log q,pq<=m/4.
Their positive certificate mass is >=x/(8log x)>=sqrt(m)/(32log m).
PNT source checked live: https://dlmf.nist.gov/27.12#E5 . No RH-sized error used.
Therefore this precise row-cap certificate cannot have any fixed power<1/2,
even on an unbounded subsequence. This does NOT exclude smaller actual II.

Full return: S=I+J-K+II; B_short=2(40+16Omega)sqrt(U)+12sqrt(V)
+12(12+4Omega)sqrt(UV), power2epsilon. PK_mP>=-[s*+B_short+50L+8]P.
If reporting T_>R, add the old small-divisor price once; not in direct K return.
Old S<=12sqrt(m)P remains stronger. Conditional3/8/ZF78 unchanged.

## Rollback and a bounded follow-through

Stop optimizing positive scalar row weights AFTER independent row caps.
For p!=q>max(U,V), the SAME A(pq) multiplies log(pq)-log(pq)=0;
for p^k, k log p-(k-1)log p=log p. Exact recombination removes the
certificate's rough-semiprime charge. It preserves every mixed mode, since
it occurs at scalar coefficients before a matrix or trace inequality.

Root follow-through: recombine all factors n before any cap. The resulting
coefficient is precisely Lambda(n), so a subsequent ||A(n)||<=2 bound is
2 sum Lambda(n)/sqrt(n)<=12sqrt(m). Thus regrouping passes the packet test
but provides NO exponent improvement. This is a check of the proposed rollback,
not a new identity or a new independent arithmetic attempt counted toward Q16.
The unpaid information is still the sign of the full original weighted kernel.
Next candidate must change that inequality (e.g. retain source autocorrelation),
pass the zero-composite/proper-power test, and pay a complete budget. No Q16
is sent merely to rename this target. Overall goal remains OPEN.

Shelf check after rollback: CCM_CONTINUOUS_RANK_TWO_TEST.md already pays
int A(x)/sqrt(x) dx=-P H_decay P. CCM_C5_CANCELLATION_LITERATURE_AUDIT.md
already tests productwise Abel/PNT and obtains half-power plus band-derivative
cost (subexponential savings only). Recombination followed by that absolute
primitive estimate is not a fresh mechanism or progress. These two documented
checks prevent restarting the same discarded calculation under Q16.
