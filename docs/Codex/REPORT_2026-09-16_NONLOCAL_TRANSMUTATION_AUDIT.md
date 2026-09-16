# Nonlocal transmutation: equation transfer and the unpaid physical flux

STATUS: INDEPENDENTLY_ACCEPTED_PAPER_TRANSFER_AND_SCOPED_METRIC_OBSTRUCTION_ONLY.
Exploratory search: INCOMPLETE_NO_CONSUMABLE_TARGET in the canonical formal
workflow; one source-verified partial analogue, no formal admission.
Own analytic result proposed below: explicit intertwining and endpoint/norm
audit only. No full-V sign, RH claim, or exclusion of all nonlocal methods.

## Frozen input and consumer

Base: bd30dcdf922dc3a8de4b42a2f20e1c01d4455ec5.
Brief: docs/Codex/BRIEF_2026-09-16_COUPLEDFLUX_NONLOCAL_HUNT.md,
SHA256 7546cb16d6e907c109fee3ae49bbd65911ae9bb2f04c1e057b782340db4a6bb5.
COUPLEDFLUX response: 4a4575555554947d3db865819ee74652f9ec7639,
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_COUPLEDFLUX_2026-09-16.md,
SHA256 258fe6d40ab6b92b4c7a5645fb75ad5dadecd7848a7567e18c0553a65b28b0c4.
Its accepted intake has SHA256
79b56d8acadf8efcb4502cebd1d989d746c72b57aa0e57ed2f68c1a9ff0de45e.

All shifts lie in I=(-log(2)/2,0), coefficients are arbitrary finite complex
rows. The full source and its convolution powers are unchanged. Write
Y_k=(Y_(2,k),Y_(4,k)), A0=D^2-1/4 and

    Ltilde=A0 I2-6 exp(-2X) N, N=[[0,1],[0,0]], X>=0.
    Ltilde Y_k=F_k,
    F_(2,k)=2pi(D-5/2)R_(2,k),
    F_(4,k)=20 exp(-2X)Y_(6,k)+8pi(D-9/2)R_(4,k).

Definitions of Y and R are CF15-CF16 of the pinned response. The only consumer
is E_c(k)=int exp(-(4+4k)X)|Y_(2,k)|^2 dX and
A^2 V[c]=-E_c'(0)/2>=0. Neither forcing component may be omitted.

## Bounded search receipt

The three registered shelf queries were run once with --defer-external:
`Sylvester nonlocal symmetrizer`, `Volterra transmutation boundary`, and
`boundary storage physical flux`. All exited 2, status INCOMPLETE, because
q3_docs semantic-index freshness validation failed. This is not a no-hits
or absence result. No index repair or repeat was performed.

Inspected local hits: Goal058PolarizedVolterra.lean is a finite Fourier
convolution identity, not the required differential/domain transfer.
D0Mode4HermitianNegativeCountStability.lean:780-838 concerns Sylvester
inertia, not the commutator equation. The returned R6BoundaryCellBridge.lean
path was unavailable. Other metadata-only hits remain unverified.

One external metadata batch used the three dictionaries in the brief.
It returned candidates but status INCOMPLETE: an 8-second batch limit
exhausted two arXiv queries; one Crossref query returned HTTP 429. There was
no retry. Exactly one selected primary article body was fetched.

Log SHA256 values, in query order:
08333eb7b0dc73db071695bdaed2b916dac3537d4c4ed7289c09e57202a84329;
51c0cfffc85739b6e5c93c7c827b3795656cdc35fa173e07350c2255ed3c1094;
d2a2316098e5d4eb06b99d32216e41c5300dfcca7d60922b5274c986116cc4c1.
Metadata JSON SHA256:
542fe54a0dfdcca570c3bfb119fc7ded73d136daa0e27c0d0e02385b1448d02a.

## One published partial analogue

Kravchenko, Morelos, Torba, arXiv:1412.5237v1, *Liouville transformation,
analytic approximation of transmutation operators and solution of spectral
problems*: https://arxiv.org/html/1412.5237v1 . Fetched HTML SHA256
b292563edfd58432859c43f1c835610e65c2414188e0237f69f8c009cf41634d.
Read scope: section 2 hypotheses, section 4 Theorems 4.1-4.3 and proof of
4.3, and initial-data discussion through Theorem 4.5. The article attributes
4.1-4.2 to its reference [11]; we verify their printed statements, not a
separate independent proof of those cited results.

Short quote, Theorem 4.2: “The inverse operator \(\mathbf{T}^{-1}\) exists and has the form”. Locator for the substantive
statement: Theorem 4.1, equation (4.1), B T w=T A w for C^2[-b,b]; Theorem
4.2 gives the inverse integral formula. Theorem 4.3, equation (4.3), composes
this with the Liouville map.

Mapping: its scalar A=-D^2 corresponds to -A0 after a constant shift; its
scalar potential and symmetric finite interval do not match our two-channel
nilpotent coupling on a half-line. Its nonvanishing normalized solution
and Goursat kernel conditions are not supplied by our block. No theorem
there identifies our weighted norm, k-flux, forcing, or endpoint domain.
The finite Jordan control is outside those differential hypotheses.
Verdict: PARTIAL_ANALOGUE for integral intertwining, not a positivity supplier.

## N1. Direct half-line intertwiner

We now test the brief's own explicit candidate, independently of that article:

    Kq(X)=(3/2)exp(-X) int_X^infinity exp(-t)q(t)dt,
    T=[[I,K],[0,I]], T^{-1}=[[I,-K],[0,I]].

Take C^2 functions whose q, q', q'' decay faster than every exponential;
the actual fixed finite source rows and their needed k derivatives satisfy
this by CF4. Compactly supported smooth half-line functions are also valid.
The differentiations and two integrations by parts below have zero terms
at infinity. Directly,

    (Kq)'=-Kq-(3/2)exp(-2X)q,
    (Kq)''=Kq+(9/2)exp(-2X)q-(3/2)exp(-2X)q',
    K(q'')=Kq-(3/2)exp(-2X)(q'+q).

Therefore [A0,K]q=6exp(-2X)q and

    Ltilde T Z=T diag(A0,A0) Z.                         (N1)

The integral kernel is (3/2)exp(-X-t)1_(t>=X). Its squared L2 norm on the
quadrant is 9/32, so K is bounded on L2(0,infinity), and T and T^{-1} are
bounded there. This does not by itself identify any self-adjoint domain.

For the actual fields set Z_k=T^{-1}Y_k. The exact equations become

    A0 Z_(2,k)=F_(2,k)-K F_(4,k),
    A0 Z_(4,k)=F_(4,k).                                  (N2)

Thus both forcing entries survive; in particular Y6 has not disappeared.
No task for the sign of Y6 is created.

## N2. The endpoint is transformed, not erased

Let J(q)=(3/2)int_0^infinity exp(-t)q(t)dt. Then

    Kq(0)=J(q), (Kq)'(0)=-J(q)-(3/2)q(0),
    Z2(0)=Y2(0)-J(Y4),
    Z2'(0)=Y2'(0)+J(Y4)+(3/2)Y4(0).                       (N3)

For example, a test pair Y with both components smooth and compactly
supported strictly inside (0,infinity) has Z2(0)=-J(Y4), Z2'(0)=J(Y4).
Generally Z2(0) is nonzero. Therefore T^{-1} does not preserve the usual
Dirichlet domain. This example is a domain diagnostic outside the actual
source family, not a negative V witness. A pulled-back closed domain would
need a separate construction and would still not identify the physical flux.

## N3. Exact original energy after the transfer

Put PZ=Z2+KZ4 and w_k(X)=exp(-(4+4k)X). The unchanged energy is exactly

    E_c(k)=int w_k |P Z_k|^2
          =int w_k (|Z2,k|^2+|KZ4,k|^2
                    +2 Re(conj(Z2,k)KZ4,k)).              (N4)

For source rows all derivatives under this integral are justified by CF4
and the tail-integral bound defining K. Since T is k-independent,

    A^2 V[c]=2 int X w_0 |P Z_0|^2
             -Re int w_0 conj(P Z_0) P (partial_k Z_k|0). (N5)

No X integration by parts was used in (N4)-(N5), so no endpoint term has
been dropped. If N2 is used to integrate by parts, the traces N3 must be
retained. Formula N5 is an exact rewrite; it is not a new lower bound.

There is a decisive control against replacing N4 by the positive auxiliary
energy ||Z_k||_L2^2. For an actual single shift x in I, the gauge definition
gives Y_(alpha,k)=exp(-2kx)Y_(alpha,0), hence Z_k=exp(-2kx)Z_0. T is invertible
and the source is nonzero, so N=||Z_0||^2>0. Consequently

    -1/2 d/dk ||Z_k||^2 at k=0 = 2x N < 0,                (N6)

whereas V(x,x)=2 int_|x|^infinity u f(u)^2 du>0.
Thus this positive nonlocal metric's unweighted k-flux is demonstrably
not the physical V. The same conclusion holds for any fixed strictly
positive quadratic form on these gauge fields with finite nonzero value.
It says nothing against the physical k-dependent weight in N4.

## What this pass changes

The explicit nonlocal equation transfer works and the simple Jordan
obstruction to local multiplication metrics does not prohibit it. But the
candidate does not furnish the missing sign: boundary traces, forcing, and
the mixed observation P remain explicit. The tempting unweighted positive
metric replacement fails on an actual permitted one-shift row.

K depends on the coupling coefficient 6 and the half-line differentiation,
not on the arithmetic spacing pi*n^2. It exposes no newly proved property
of the full source that bounds the last term in N5. We stop this particular
diagonalization test rather than introducing another auxiliary energy or
more convolution levels. Other nonlocal constructions and full V remain open.

Next bounded research question, before any new request: return to the full
source's exact arithmetic structure and require a candidate to preserve the
physical observation from the outset. A new route must name the particular
source property it spends and one sufficient full-form inequality. N5 alone
does not qualify as that supplier. No Proshka request is pending or dispatched
by this report; canonical production HOLD remains unchanged.

## Independent acceptance

Candidate SHA256: `3161cd840a02ab5109d6de7d065460e04aa90a5042562fa5471413db0e9d4710`.
Read-only reviewer `/root/sibling5_check`, review SHA256: `e3db7624b53bc547e1da3c8cc6bf9317ac66a239066fed91da89f9865d8b103f`.
The parent independently checked N1-N6 and the exact primary theorem mapping.
Only the status and this receipt were added after review.
No canonical mathematical admission or Lean verification is claimed.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The positive unweighted nonlocal metric has the wrong k-flux on an actual one-shift source row; retain the physical weighted observation instead.
