# Full min1 ODD2 strip: independent PAPER intake

Status: ACCEPT_ACTUAL_THETA_ODD2_MIN1_WHOLE_STRIP_ONLY.
All x,y>=1 and all complex odd two-node coefficients are covered.
Global ODD2, global IC, higher odd/even signs, full V/Q and RH remain open.
This is isolated PAPER evidence; no Lean or canonical admission is claimed.

## Exact delivery and reproduction

Request REQ-2026-09-12-ODD2STRIP, boundary
GOAL058_ACTUAL_THETA_ODD2_WHOLE_REMAINING_MIN1_STRIP, same living chat
6aa52001-4094-83eb-9520-01a09f54eff2. Request commit
7395b1c9c5c2b04d279f8ce51a6716e431e1716d, blob
5b390298153207eed85d7a1a6eaafd500fc10ae8, SHA256
19067af9236aefbd116478b6f09e13ca14ef41554978724a10d5f59642197a0e.
Natural completed reasoning: UI 60m19s; final observed about17:05UTC.
No Answer now, restart or duplicate request was used.

The unchanged complete response is
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODD2STRIP_2026-09-12.md:
108317 bytes,1808LF,finalLF,0CR,valid UTF-8, SHA256
063ecc08ce1671fcaa944c980c36c4899f97caa1d65473c2db974222d27bed3b.
Parent and sole independent checker /root/sibling5_check read all1808 lines.
The parent decoded all23 request source frames and matched their bytes,
LF counts,SHA256 and Git blobs against the manifest and isolated disk.

Exact extraction, with no content edits:

| Artifact under docs/Codex/certificates | Bytes / LF | SHA256 |
|---|---|---|
| ODD2_STRIP_20260912.py | 13862 /324 | f6c03177e0f91e52d1fb6080fcb63d4f71306d3da9d4a7de700a7dbf9268517a |
| ODD2_STRIP_20260912.json | 11068 /128 | d8d8da5f902a122954c972bbc86f003b9f5fa91e7199b0e42ff4cdfbda179bdb |
| ODD2_STRIP_REPLAY90_20260912.json | 648 /16 | e0c969fae600495fd6b2453e6fe176967f8da6ece671be7ce9fe3f832f5242b5 |

The parent executed the unchanged code with STRIP_PREC=90 and verify mode,
without Python -O, in scratch outside production. Exit0, empty stderr,
all4158 leaves,8259 tree nodes,maximum depth16,exact area57,unpaid0.
All25 rational comparisons passed. The entire output is byte-identical to
Appendix D, including both minimum lower endpoints and source/certificate
hashes. Local Python3.14.7/libmpdec4.0.1 differs from producer
Python3.13.5/libmpdec2.5.1; the output still matches exactly.
The final arithmetic is directed Decimal, not Arb/FLINT.

Reproduction from any directory, using appropriate absolute paths:

    STRIP_PREC=90 python3 ODD2_STRIP_20260912.py verify ODD2_STRIP_20260912.json

The JSON retains accepted:false because the executable does not accept its
own mathematics. Acceptance is the separate analytic and reproduction record
here. The checker did not duplicate the parent's numerical run; it performed
the independent full analytic/static-code audit and accepted the combined
evidence. No source theta quadrature or adaptive rebuilding was required.

## Source, theorem and all-complex consumer

Keep f=Phi/A, A=||Phi||_2 and the exact full source integrals

    V(s,t)=integral_0^infinity(s+t+2v)f(s+v)f(t+v)dv,
    K(s,t)=V(s,t)-V(s,-t),
    Delta(x,y)=K(x,x)K(y,y)-K(x,y)^2,
    alpha_z=pi exp(2z), m=(s+t)/2, d=s-t, alpha=pi exp(2m).

With full theta H, c=cosh d, B=H(alpha_s)H(alpha_t), put

    T=2alpha c B K(s,t)/(f(s)f(t)).

The accepted new supplier gives, for every1<=y<=20,0<=d<=3,

    C(y+d,y)=partial_s partial_t log K >=1/1000,
    T(y+d/2,d)>=9/20,
    Dhat(y,d)>=1/2500000.                                  (ST)

For d>0, Dhat=alpha_(y+d)alpha_y Delta(y+d,y)/[f(y+d)^2 f(y)^2 d^2].
For d=0 its exact continuous value is
alpha_y^2[K(y,y)K_12(y,y)-K_1(y,y)^2]/f(y)^4.
The unnormalized determinant remains exactly zero on the diagonal.

Combining(ST) with accepted S20 and min1/gap3 proves, for every x,y>=1,
the original odd two-node matrix is positive semidefinite on C^2, and
positive definite when x!=y. For all such pairs with gap<=3:

    Delta>=gap^2 f(x)^2 f(y)^2/(2500000 alpha_x alpha_y),
    c* K_2 c>=gap^2/[3750000(x alpha_y+y alpha_x)]
                  *[f(x)^2|c1|^2+f(y)^2|c2|^2].             (M)

At x=y the exact form is K(x,x)|c1+c2|^2. For gap>=3 the accepted
xy/[324(x alpha_y+y alpha_x)] coefficient applies instead.
The four-node V form on(x,y,-x,-y), coefficients(c1,c2,-c1,-c2),
is twice this form; its budgets double. No restriction to real coefficients
or to a common complex phase is imposed.

## Independent and parent analytic checks

Both reviews checked the complete mechanism, not just the rational constants:

- T cancels only separable H/f factors before complex estimates. Its full
  integral definition does not assume complex H has no zeros. The curvature
  formula retains c^-2 and the entire mixed quadratic numerator.
- P16 retains both full Laplace terms and the linear reflected multiplier;
  its coefficient 3k-3/2 and all composed m,d derivatives are correct.
- The full theta mode bound treats the reflected small q all the way to zero.
  The exponent inequality in response(4.12) preserves an az/8 integrable
  reserve on every z>=0. All four errors integrate to infinity.
- The direct Taylor remainder is valid on the complete complex ray Re t>=0;
  the reflected remainder is an exact finite resolvent identity, without a
  convergence-radius assumption. Their total rational budget is below1e-9.
- Holomorphic domination and removable c=1 permit Cauchy estimates on the
  radius1/128 polydisks. The six errors are
  1e-9*(1,128,128,32768,16384,32768), including mixed md.
- Jk uses exact c=1 values, a positive full-tail series near1, and a directed
  recurrence farther away. The finite jets enclose every point of each cell.
- Every tree starts at one of57 specified unit rectangles and replaces its
  parent by exact rational halves. Decoding consumes every bit and recomputes
  every leaf. Area57 is an additional check, not the sole coverage argument.
- To integrate C for a pair, the whole square[y,x]^2 is covered: ST below
  min20, accepted E1 above it. Thus y<20<x is retained. The resulting
  Dhat>=81/193600000>1/2500000 gives(M) by positive congruence and det/trace.

Primary operative references were checked against
[NIST DLMF1.9.31](https://dlmf.nist.gov/1.9#E31) for the Cauchy derivative
formula and the [Python3.14 Decimal documentation](https://docs.python.org/3.14/library/decimal.html)
for context-controlled rounding and neighboring representable values.
The arithmetic relies explicitly on Decimal implementation correctness;
it is not a Lean-kernel certificate.

## Sharp combined remaining set

The response's x<2000 description reflects its source packet at dispatch.
It is superseded by two later independently accepted, published suppliers:

- REPORT_2026-09-12_ODD2_SMALL_NODE_TAIL5.md, commit
  59a0936e87619beeb8db7c88d09426bffad98698, SHA256
  088cfa2fcaa28a3d7d17e7e4da7f59722561907f5e177d2dc47b08bff4557766:
  all x>=5,0<y<=1.
- REPORT_2026-09-12_ODD2_MONOTONE_MIXED_AXIS.md, commit
  8671b75bd3b1fde9c2a322279a1f6e9089de265a, SHA256
  b7f054579aba17cf6747b1116bbf3d59bc111deb36580d299abcc5819aae0bc6:
  all x>=2,0<y<=1/4 and all x>=3/2,0<y<=1/256.

Together with the whole origin-quarter square, exact diagonal and(ST),
an ordered outer set for every remaining possible negative ODD2 pair is

    0<y<=1/256,             1/4<x<3/2;
    1/256<y<=1/4,           1/4<x<2;
    1/4<y<1,                  y<x<5.                       (LOW)

Subtract the already accepted AX/DG blocks and add transpose for unordered
nodes. Endpoints1/256 and1/4 use the stated closed strip budgets. The new
all-min>=1 theorem also improves the global max-node cutoff from23 to5:
if max>=5, either min<1 uses tail5 or min>=1 uses(M)/gap3.
This is a consequence of accepted theorems, not a new source computation.

A separate bounded axis-only attempt on[1/4,3/2] stopped after2048 evaluations
and92.68seconds. Its1024 positive panels covered only[1/4,17/64], leaving
all[17/64,3/2] in80 recorded panels. Their rational partition was checked.
It supplies no accepted axis theorem, no finite-y coverage and no witness.
Direct interval bounds on the two determinant terms lost their cancellation;
another finer repetition of that same construction is not the next consumer.

Next exact consumer: all of(LOW), including axis/diagonal limits; a theorem
there would close global ODD2 when combined with the suppliers above.
Higher odd/even sizes and full Weil positivity would remain unpaid.
The accepted whole-strip family is substantive source-sign progress;
the current same-obstacle no-delta count is0. Partial axis panels and
administrative activity are not counted as progress or a reset.

## Exact intake review

The mathematical response has parent and sole-checker acceptance.
The sole checker read the full8676byte/170LF pre-receipt intake, SHA256
3f59bde503f1381a5418e336910e9864005599cf23d5e8201c4420618b80a121,
and returned CLEAN. The three LOW rows, their closed endpoints and the
new max-node cutoff5 were independently checked. Only this receipt changed
after that review; all accepted mathematical statements remain unchanged.
