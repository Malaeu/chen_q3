# ODD2COMPACT intake: two explicit full-source boundary families

Verdict: ACCEPT_AX_AND_DG_BOUNDARY_SIGN_FAMILIES_ONLY.
Status: independently reviewed computer-assisted PAPER result.
Full request: INCOMPLETE; global ODD2, global IC and RH remain open.
No Lean execution or canonical production admission.

## Exact request, receipt and unchanged response

Request REQ-2026-09-12-ODD2COMPACT was delivered to the authorized living
mathematical chat 6aa52001-4094-83eb-9520-01a09f54eff2. Its exact committed
TXT is docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ODD2COMPACT_2026-09-12.txt:
314544 bytes, 5112 LF, final LF, no CR, SHA256
4defaec31ac4dac8d477ae8e75cab1f3dde6181d20dda981bede140c68d1d31a,
commit f56c82b2dff21ac37e8d3bebc183d476cdcc7067.
The parent rechecked the working file against these exact committed bytes.

The natural final response displayed 47m 23s of reasoning. Its whole file is
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2COMPACT_2026-09-12.md:
71971 bytes, 1159 LF, final LF, no CR, SHA256
819511db9d46801e87b54e728faf7c55e7ce21e4e20e48d9d95d49a71b175e07.
The downloaded bytes match the producer's complete receipt and are unchanged.
All 14 source-manifest hashes, sizes and LF counts match current source files.

The intermediate browser assertion about 256 intervals covering [1/2,1]
is NOT an accepted result. The final artifact explicitly supplies only the
following much smaller regions and is the object of this acceptance.

## Accepted source and quantified claims

The exact source remains f=Phi/A, A=||Phi||_2, the full half-line V,
K(s,t)=V(s,t)-V(s,-t), and Delta=K(x,x)K(y,y)-K(x,y)^2.
For calculation, raw F=Phi, Kraw=A^2 K and Deltaraw=A^4 Delta are used.
This is an exact scalar normalization, not a source replacement.

Put I=[1/2,1/2+2^-12], J=[1/2,1/2+2^-20] and Y=2^-8.

1. AX: for every x in I and 0<y<=Y,
   Delta(x,y)>=y^2/(20000000 A^4)>0. The transpose region is included.
   Its constant is uniform as the smaller node tends to zero.
2. DG: for every x,y in J,
   Delta(x,y)>=(x-y)^2/(1000000000 A^4).
   At x=y the determinant is exactly zero; at distinct nodes it is positive.
   The full two-variable square also has local IC C>=125/121>1.

Let a=Kraw(x,x)>0 and b=Kraw(x,y). For all c1,c2 in C the exact form is

    c* K_2 c = A^-2 [a |c1+(b/a)c2|^2+(Deltaraw/a)|c2|^2].

On AX its lower bound is
A^-2[|c1+(b/a)c2|^2/25000+y^2|c2|^2/900].
On DG its lower bound is
A^-2[(43/10^6)|c1+(b/a)c2|^2+(x-y)^2|c2|^2/44000].
The original four-node odd V form is exactly twice this complex form.

## Full-source and cancellation audit

The complete derivative series is

    F^(j)(t)=e^(t/2) sum_{n>=1} P_j(pi n^2 e^(2t))e^(-pi n^2 e^(2t)),
    P_0(z)=4z^2-6z,
    P_(j+1)=(1/2-2z)P_j+2z P_j'.

For t>=0 the n>N remainder is bounded by
D_j exp[-pi(N+1)^2 e^(2t)/2]. The displayed proof supplies D_j
for all fixed orders, with j<=9 used in this certificate. Six computed
theta modes always carry the complete symmetric remainder. Negative
arguments use the exact evenness of F and the parity of each derivative.

The main integral uses 128 complete cells on [0,3], integrated Taylor
through degree 7, and a uniform eighth-derivative remainder on each cell.
The complete v>=3 direct and reflected tails are added. The higher
axis derivative budgets use 256 complete v cells and their own full tails.

On AX the source axis jet is H(x)=k a(x)-b(x)^2, with inherited
k=Kraw_st(0,0) in (0.0864,0.0877). The new bounds are
H>123/10^9, a<9/200000, |b|<19/10000, M03<3/4, M13<171.
Oddness gives errors M03*y^2/6 for Kraw(x,y)/y and M13*y^2/3
for Kraw(y,y)/y^2. The latter follows by sequential Taylor of the
function Kraw_st, even in each coordinate, and integration over [0,1]^2.
The exact mixed terms in the determinant are retained. The resulting
rational lower bound is

    41129489051/536870912000000000 > 1/20000000.

On DG, s and t are independent in J. The reflected weight contains
s-t in [-2^-20,2^-20]; it is not replaced by zero. The certificate gives
43/10^6<Kraw<44/10^6 and
Nraw=Kraw Kraw_st-Kraw_s Kraw_t>2/10^9 on the whole J^2.
Thus C=Nraw/Kraw^2>=125/121. The exact rectangle identity for log K
supplies the (x-y)^2 factor before any lower estimate of Delta.

## Independent reproduction and parent check

Sole independent checker /root/sibling5_check read all 1159 lines, checked
the exact full source, remainder and complex-form derivations, and returned
ACCEPT_AX_AND_DG_BOUNDARY_SIGN_FAMILIES_ONLY for the response hash above.
It reproduced the full embedded code in scratch at precision 40.

The following files are byte-exact extractions of response appendices B,C:

- docs/Codex/certificates/ODD2COMPACT_BOUNDARY_CERT_20260912.py:
  10469 bytes, 230 LF, SHA256
  27c072e2ae3ee548f52c9b01008c3161a968060dd133420fcaeb83892e33eebe.
- docs/Codex/certificates/ODD2COMPACT_BOUNDARY_CERT_20260912.json:
  4602 bytes, 137 LF, SHA256
  f20e3d51914414dc165aacd947c70c5f7754cc74d4f03b5a7ebdebe60cc18c29.

The checker used Python 3.14.7; the producer used Python 3.13.5.
The parent compared every JSON field: only the two recorded Python-version
fields differ. All numerical strings, source hash, exact tests and bounds
match. The parent's separate fractions.Fraction checks reproduced the AX
loss and final rational floor, the DG curvature and determinant floors,
and both complex Schur coefficients. The parent also read the complete
response and code and independently audited the reflection, Taylor
Jacobians and domain quantifiers; it did not merely accept a tool verdict.

Arithmetic relies on CPython Decimal directed rounding and correctly
rounded exp expanded with next_minus/next_plus. The relevant guarantees
were directly checked in the official
[Python decimal documentation](https://docs.python.org/3.13/library/decimal.html#decimal.Decimal.exp).
This implementation dependency is explicit; the calculation is not Lean
kernel verification. No extra package or binary-float sign test is used.

## Remaining consumer and cycle state

Accepted earlier results localize any possible negative pair to
0<x,y<L and max(x,y)>epsilon, with finite existential L and explicit
epsilon from the accepted origin report. AX and DG exclude exactly
(I x (0,Y]) union ((0,Y] x I) union J^2 from that possible-witness set.
They do not supply a full covering or a uniform bound on the rest.
The independent analytic min1/gap3 result is recorded in its separate report.

The current same-obstacle no-delta count is reset from 1 to 0 because
new actual-source consumer sign families passed independent and parent
review. The historical producer count 3 to 4 is not the current count.
The complete ODD2COMPACT request remains incomplete. Higher odd sizes,
the even sector, full V/Q positivity, global IC and RH are not established.
