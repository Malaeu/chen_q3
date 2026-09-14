# Stein pair representation: exact all-order map, full sign still open

STATUS: ACCEPTED_PAPER_STEIN_PAIR_REPRESENTATION_CANONICAL_DIRECTIONS_AND_POINTWISE_LIFT_REFUTATION.
FULL_TARGET: INCOMPLETE. ALL_H_N_PSD: OPEN. H1_PSD: OPEN.
GLOBAL_ODD2: OPEN. GLOBAL_IC: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.
Isolated mathematical evidence only; no Lean or canonical admission.

## 1. Exact receipt and independent verification

REQ-2026-09-12-ODDINFINITY, boundary
GOAL058_ACTUAL_THETA_ALL_ORDER_HANKEL_SOURCE_SIGN, completed naturally in
the same authorized chat6aa52001-4094-83eb-9520-01a09f54eff2. Fresh full AX
first exposed the final downloadable response and idle composer at
19:10UTC on2026-09-12. The UI reports22m10s reasoning; the exact producer
completion timestamp was not observed. No Answer now, duplicate send,
reload or new chat was used during this request.

The complete original download is preserved unchanged at
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODDINFINITY_2026-09-12.md:
70358bytes,1234LF,finalLF,0CR,UTF-8,SHA256
8ca45b2f8a37db52a883be395b3db5e8465883934b6337f70ee60457f6132b85.
The controlling TXT is85386bytes/1772LF, SHA256
e3ad1057d9c2bb3a8a8541942d8c224cc9ee9cefcfe1f0c001f01cc31c50a3d7,
request commit15bd42a61740f8e6c61ea862881dac6537ed9a95
(user-bound in the producer report, not remotely rechecked by the producer),
Git blob28b3900a87f58fdde4d79e1359f07a7b1648b456.

Parent and sole checker /root/sibling5_check read all1234LF of the
response. Parent matched all7 complete source frames, manifest paths,
byte/LF/CR counts, finalLF, SHA256, Git blobs and frame line locations
against the controlling TXT, current owned files and committed HEAD.
The producer reports full semantic reading of these7 operative reports;
unattached recursive historical sources are not claimed re-read.

The raw response has one typesetting defect: at zero-based byte25265,
equation(24) contains a form-feed byte0x0c followed by `rac`, where the
intended TeX is `\frac`. Its formula is correctly transcribed in §3 below.
The original bytes and original hash are retained as provenance; the
raw file is not represented as a repaired edition.

## 2. Accepted exact map, with all source and complex terms

Keep the accepted source notation: Z=integral_R Phi, p_X=Phi/Z,
U=X^2 with probability law nu, mu_j=E[U^j], h(u)=log Phi(sqrt(u)),
b=-2h', b>0 and b'>=1/2. Z is not the physical L2 normalization A.
All moments and the required exponential integrals are finite.
For each complex polynomial q, full-line integration by parts gives

    E[b(U)Uq(U)] = E[q(U)+2Uq'(U)].

For q=conj(P)Q both polynomial derivatives must be retained. With
independent U,V of law nu, define the finite positive pair measure

    dLambda_b = (1/4)uv[b(u)-b(v)](u-v)dnu(u)dnu(v)
              >= (1/8)uv(u-v)^2 dnu(u)dnu(v).

All its polynomial moments are finite: bound the absolute integrand by
uv(b(u)+b(v))(u+v) times a polynomial, and use the accepted score moments
E[b(U)U^k]=(2k-1)mu_(k-1), k>=1. No E[b^2] is assumed.
For every bivariate polynomial R the exact source identity is

    integral R dLambda_b = (1/4) E[(6UV-U^2-V^2)R
                            +2UV(U-V)(partial_u-partial_v)R].

Write e(w)=E(w)/E(0)=sum_j e_j w^j with e_j=(-1)^j mu_j/(2j)!,
g=-e'/e=sum_j a_j w^j near0, and H_n=[a_(i+j+1)]_(i,j=0)^n.
The entire series s_w(u)=sum_k(-1)^k(uw)^k/(2k+1)! satisfies

    e(w)=E[b(U)U s_w(U)],      -2e'(w)=E[U s_w(U)].

The parent checked the [sine series in DLMF4.19.1](https://dlmf.nist.gov/4.19#E1).
Only this elementary series is used from that external source; no sign
or zero-location theorem is imported. Full exponential bounds on Phi'
justify the series, fixed derivatives and double integrals.

Symmetrizing the last identities gives the following coefficient map.
For each i,j>=0, put m=i+j and

    C_ij(u,v)=(-1)^m sum_(k=0)^min(i,j)
      [(uv)^k / ((2k+1)!(2(m+1-k)+1)!)]
      * sum_(r=0)^(m-2k) u^r v^(m-2k-r).

This is the z^i w^j coefficient of

    [s_z(u)s_w(v)-s_w(u)s_z(v)] / [(z-w)(v-u)].

Both diagonal singularities are removable. The v-u factor cancels
exactly against the pair measure before integral bounds are used.
For each arbitrary finite n, set C_n=[C_ij]_(i,j=0)^n,
B_n=integral C_n dLambda_b and (T_n)_ij=e_(i-j) for j<=i, zero otherwise.
Then

    B_n = T_n H_n T_n^T,       det(T_n)=1,
    c*H_n c = integral d*C_n d dLambda_b,    d=T_n^(-T)c.

The coefficient proof holds for every i,j; no finite computation is
promoted to that quantifier. T_n is real and invertible at each finite
n; no bounded inverse for an infinite matrix is assumed. The formula
preserves every complex cross term and the whole source integral.

## 3. Accepted limited signs and exact failed sufficient step

After removing (-1)^(i+j), each polynomial C_ij is positive for u,v>0.
For v^(n)=(e_n,e_(n-1),...,e_0)^T this proves, for all n>=0,

    (v^(n))*H_n v^(n) = (B_n)_nn
      >= [mu_(n+1)mu_(n+3)-mu_(n+2)^2]
         / [4(2n+1)!(2n+3)!] >0.

Keep only k=n in C_nn and apply the lower measure bound. The remaining
strict moment determinant is a variance under u^(n+1)dnu; this measure
has positive density on the whole positive axis. This proves one
specified positive line in each H_n, not all coefficient vectors.
The n=0 case repeats the previously accepted H0 budget.
The correctly typeset content of raw equation(24) is

    (B_1)_11 = (35mu_2^2-14mu_1mu_3-mu_4)/10080
              >= (mu_2mu_4-mu_3^2)/2880 >0.

However, the inner2x2 matrix is

    C_1 = [[1/6, -(u+v)/120],
           [-(u+v)/120, (u^2+8uv+v^2)/5040]],
    det C_1 = [16uv-11(u-v)^2]/302400.

For the fixed d=(1/4,1)^T on I=[1,101/100], J=[4,401/100],

    d*C_1(u,v)d <= -2999/5040000 < -1/2000,
    integral_(I x J) d*C_1 d dLambda_b
      <= -89401 nu(I)nu(J)/40000000 <0.

The negative upper bound uses the entire rectangle and positive masses
of the actual source. It refutes precisely pointwise PSD of C_n.
It is not a negative H1 or physical K witness: the integral over the
complement is retained and may compensate. U,V are pair-measure
variables, not physical K nodes. Positivity of the scalar weight cannot
authorize deleting its negative matrix contribution.

## 4. Exact first unpaid balance and full remaining target

The measure mass is M_b=(3mu_1^2-mu_2)/2=6a_1>0. Normalize it to
Lambda_hat=Lambda_b/M_b and write E_b,Var_b for its moments. For every
complex d0,d1 the full matrix has the exact decomposition

    d*B_1 d = (M_b/6)|d0-E_b(U+V)d1/20|^2
               +(M_b/50400)Psi_b |d1|^2,
    Psi_b = 21Var_b(U+V)+16E_b(UV)-11E_b[(U-V)^2],
    det H_1 = M_b^2 Psi_b /302400
            = (10P4 P8-21P6^2)/1209600.

P4,P6,P8 are exactly the accepted SOURCE_MOMENT_HANKEL_INTERFACE
polynomials. The sign Psi_b>=0 remains unpaid. This is the complete
compensation, including the variance term, rather than a pointwise
surrogate. No impossibility theorem for every use of scalar(M) or
source TN-infinity is claimed. An independent source comparison has
not been supplied. Even proving H1 would leave all larger orders open.

The full target remains integral d*C_n d dLambda_b>=0 for every n and
every complex d. Stating that inequality without an independent source
argument only rewrites the target. The accepted ALL_ODD_TO_RH reduction
still makes all H_n PSD equivalent to RH for this exact source. Its
conditional Hilbert space is not an independent sign supplier.
Global ODD2/IC and the LOW1-LOW3 residual are unchanged.

The earlier accepted STEIN_POLYNOMIAL_CORRECTION diagnostic is compatible
with this response: both derivatives are present throughout, and no
uniform sign is assigned to its correction4(AS-BR). The new pair formula
does not remove that obligation by changing notation.

## 5. Reproduction, classification and continuation

The embedded standard-library checker verify_oddinfinity.py is unchanged:
5315bytes/143LF/SHA256
286ad3f1cf5c1758a6a2a2f8fd65cf08f821664a12dfa72b1ebfec594153bbe3.
Parent Python3.14.7 reproduced exit0, empty stderr and all1057 stdout
bytes, SHA25659b1f78a0a2cc637b89db10be58c3f96d1429295f1f2cc820808a825b2ad54f5.
The packet checker also reproduced all203 stdout bytes, SHA256
0e599f84f983dfef1b349f92f5f2dd89bd7080d95391bb1916ebf6ab8817aac1.
All6 embedded code/stdout byte counts and hashes match their declarations.
The optional redundant SymPy code was read and hashed, not re-executed;
no dependency was installed. The decisive exact replay uses Fraction
and formal moments; it evaluates no theta values and proves no source
Hankel signs. General formulas are justified by the analytic proof above.

The sole checker independently accepted only the claimed limited PAPER
scope and identified the raw typesetting defect. Parent independently
checked all-order coefficient extraction, source integrability, finite
congruence, strict direction budget, rectangle upper bound and full
variance identity. Source-sign no-delta advances1->2 for this completed
unsuccessful sign attempt; no reset for the representation or the one
positive line per order. Live waits do not add attempts.

AUTOPSY: dropped=SIGN; note=the inner source coefficient matrix has both signs; the required averaged sign, already Psi_b>=0 at H1, was not derived.

Do not repeat the false pointwise-C PSD step, delete complement
compensation, use a conditional positive space as input, or substitute
finite positive matrices for the full all-order requirement. Any next
mathematical attempt must introduce and test an independent property of
the actual source. The user's three-repeat threshold is not yet reached.

The sole checker returned CLEAN for the complete199LF intake above,
reviewed SHA256
611790c4a7c8e88c9baa0e84855a15c719627a7f56fddcf63161276993bbbe4f.
Only this exact review receipt was appended after the wording review.
