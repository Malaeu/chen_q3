# STATUS: TRY_RAY_EVALUATION_RANK_WINDOW_INERTIA
```yaml
OPERATIVE_CLASS: TRY_RAY_EVALUATION_RANK_WINDOW_INERTIA
REQUEST_MODE: OWNER_DIRECT_MATHEMATICAL_QUESTION
DATE: 2026-09-17
SCOPE: ABSTRACT
VERIFIER: PAPER
ARTIFACT_KIND: LOCAL_ANALYTIC_NOTE
SOURCE_DEFINITIONS_READ: true
PAIR_BLOCK_IN_ZERO_COORDINATES: explicit_signature_1_1
PAIR_PULLBACK_THROUGH_CONTOUR_RAYS: explicit_conditional_on_signed_sampling_identity
PAIR_PULLBACK_NEGATIVE_INDEX_ONE: requires_rank_two_or_explicit_negative_image
FULL_ZERO_COORDINATE_WINDOW_NEGATIVE_INDEX: number_of_distinct_off_axis_j_pairs
ACTUAL_A_N_IDENTIFIED_WITH_THIS_WINDOW_FORM: NOT_ESTABLISHED_IN_READ_SOURCES
ACTUAL_A_N_WINDOW_NEGATIVE_INDEX_NUMERICALLY_DETERMINED: false
J_N_ZERO_FREE_IN_REQUESTED_REGION_PROVED: false
NEW_RH_SIGN_SUPPLIER_CLOSED: false
CLOSES: []
OPENS: []
LEAN_KERNEL_CHECKED: false
NUMERICAL_TESTS_RUN: false
REPOSITORY_CHANGED: false
INDEPENDENT_REVIEW: pending
RH_CLAIM: false
```

## 0. Answer and source boundary

For a fully retained two-element zero orbit, the signed Weil block has one positive and one negative direction. A finite ray compression need not retain both directions. The numerical negative index of the user's particular A_N is not determined by the presence of an orbit without the exact compression map and a signed-form identity.

This note distinguishes three objects rather than identifying them by notation:

1. The signed zero-coordinate Weil form, with its established separating tests.
2. A pullback of that zero-coordinate form through the literal contour-ray evaluation map.
3. The scalar head h_N(p)=4 Re(J_N'(p) conjugate(J_N(p))).

The read contour source defines J_N and h_N. It does not supply an identity identifying an operator A_N with the first or second object. Introducing the explicitly named pair pullback below does not manufacture that missing identity.

Sources read:

- [F] `docs/routeB_bus/proshka/PROSHKA_FOLDED_FULL_SOURCE_CONTOUR_ENCLOSURE_2026-09-17.md`, commit `3efebe3113a07de20c622437c1b409ee3fc4e364`, equations (2.4)–(3.6), (4.1)–(4.2).
- [G] `docs/routeB_bus/proshka/PROSHKA_GLOBAL_COUPLED_MARGIN_AUDIT_2026-09-17.md`, same commit, §§1 and 1.1. This pins the adaptive cutoff and explicitly leaves its global sign unproved.
- [S] `docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_SCREW_SIGNATURE_CLOSURE_2026-09-08.md`, commit `d6243e9fbeda53fe60fa9c27138c9dae6504e134`, blob `b90fa0d124ae324156cd3375994c129772c7ad5e`, equations (SC1)–(SC5). Its result is PAPER, not Lean verification.
- [L] Nakatsukasa–Noferini, *Inertia laws and localization of real eigenvalues for generalized indefinite eigenvalue problems*, arXiv:1711.00495, abstract: inertia is preserved by invertible congruence. Only that classical statement is used; the calculations below are written out.

All mathematical derivations below have [ABSTRACT][PAPER] scope. A finite set of zero coordinates does not mean that a numerical certificate was run.

## 1. The exact two-ray zero block

Fix the centered coordinate p=s−1/2 and reflection j(p)=−conjugate(p). Suppose the full centered xi function has the distinct pair

\[
p_+=\sigma+i\gamma,\qquad p_-=-\sigma+i\gamma,
\qquad\sigma>0,
\]

with common multiplicity m. The signed explicit formula uses the transform

\[
F_f(p)=\int_{\mathbb R} f(x)e^{px}\,dx.
\]

Put u=F_f(p_+), v=F_f(p_-). The contribution of this orbit is exactly

\[
q_{\rho}(f)=m(\bar vu+\bar uv)
=2m\Re(\bar uv).
\tag{1}
\]

Thus, in the two evaluation coordinates,

\[
B_\rho=m\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
S^*B_\rho S=\begin{pmatrix}m&0\\0&-m\end{pmatrix},
\quad S=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
\tag{2}
\]

The two definite coefficient rays are C(1,1) and C(1,−1). Their energies are respectively 2m|c|² and −2m|c|². The coordinate rays C(1,0) and C(0,1) are isotropic but not radical.

Using the source separating tests e_{p_+}, e_{p_-} of [S], the actual quotient rays can be represented by

\[
f_\pm=\frac{e_{p_+}\pm e_{p_-}}{\sqrt{2m}},
\qquad Q[f_+]=1,\quad Q[f_-]=-1,\quad Q(f_+,f_-)=0.
\tag{3}
\]

These separating tests are not automatically elements of an arbitrary finite ray span. This is precisely the distinction needed for compression.

Multiplicity m changes the nonzero weights, not the number of point-evaluation coordinates. One distinct j-pair contributes (1,1), even when m>1. A full quartet at heights ±gamma ordinarily comprises two such pairs.

## 2. The literal contour rays and their pair pullback

Freeze theta and N. Do not differentiate theta(T) or N(T) when differentiating in p. From [F],

\[
r_{n,+}(p)=I_n(p,\vartheta),\qquad
r_{n,-}(p)=I_n(-p,-\vartheta),
\]

\[
I_n(p,\vartheta)=a_n^{-p/2-1/4}
\left[2\Gamma(p/2+9/4,a_ne^{2i\vartheta})
-3\Gamma(p/2+5/4,a_ne^{2i\vartheta})\right],
\quad a_n=\pi n^2.
\tag{4}
\]

Let r_N(p) be the column of these 2N ray values. For a coefficient vector c define the auxiliary evaluation

\[
\mathcal J_c(p)=r_N(p)^T c,
\qquad J_N(p)=\mathcal J_{\mathbf1}(p).
\tag{5}
\]

Allowing arbitrary c in (5) is an auxiliary linear-algebra construction. It is not a claim that all these functions are transforms of admissible original Weil tests.

For a selected pair define

\[
R_{\rho,N}=\begin{pmatrix}r_N(p_+)^T\\r_N(p_-)^T\end{pmatrix}.
\]

The pullback of its zero block, *if this signed sampling form is the intended one*, is explicitly

\[
\boxed{B_{\rho,N}=R_{\rho,N}^*B_\rho R_{\rho,N}
=m\{\overline{r_N(p_+)}r_N(p_-)^T
+\overline{r_N(p_-)}r_N(p_+)^T\}.}
\tag{6}
\]

Write u_N=conjugate(r_N(p_+)), v_N=conjugate(r_N(p_-)). Equivalently,

\[
B_{\rho,N}=\frac m2\left[(u_N+v_N)(u_N+v_N)^*
-(u_N-v_N)(u_N-v_N)^*\right].
\tag{7}
\]

If rank R_{rho,N}=2, let C=R^*(RR^*)^{-1}. Then RC=I₂, and the vectors

\[
c_\pm=C\frac{(1,\pm1)^T}{\sqrt{2m}}
\]

have pair energies ±1. Appending a basis of ker R gives an invertible congruence to B_rho direct-sum zero. Thus

\[
\boxed{\operatorname{inertia}(B_{\rho,N})=(1,1,2N-2)
\quad\text{when rank }R_{\rho,N}=2.}
\tag{8}
\]

The exact rank discriminator is

\[
\Delta_{\rho,N}=\|u_N\|^2\|v_N\|^2-|u_N^*v_N|^2>0.
\tag{9}
\]

Without rank two the negative direction can disappear. For v_N=kappa u_N,

\[
B_{\rho,N}=2m\Re(\kappa)u_Nu_N^*.
\tag{10}
\]

Its negative index is one only if u_N≠0 and Re(kappa)<0; otherwise it is zero. In particular, identical ray rows preserve only the positive diagonal u=v and have negative index zero. This is a direct counterexample to automatic preservation under compression, not a zeta counterexample.

## 3. What the frequency-window index equals

Let W_T={p: |Im p−T|≤1}. Reflection j preserves W_T. For the full xi source, let Z_T consist of its distinct centered zeros in W_T. This set is finite because the zeros lie in a bounded critical strip and are discrete.

Let l_T count its j-fixed points and r_T count its two-element j-orbits. The full zero-coordinate form is

\[
D_T=\bigoplus_{p\in Z_T,\,\Re p=0}(m_p)
\ \oplus\!
\bigoplus_{\{p,jp\}\subset Z_T,\,\Re p>0}
 m_p\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{11}
\]

On the span of the actual source separators this is the full restricted Q, not merely formal independent coordinates. It follows that

\[
\boxed{n_-(D_T)=r_T
=\#\{p:\xi(1/2+p)=0,\ \Re p>0,\ |\Im p-T|\le1\},}
\tag{12}
\]

where the count is of distinct zeros, not their multiplicities. One pair gives one; several independent pairs give their number. No assertion that this unknown count is zero is made.

For a finite evaluation map E_{N,T} from a chosen coefficient space, set

\[
A^{\rm zero}_{N,T}=E_{N,T}^*D_TE_{N,T}.
\tag{13}
\]

Then exactly

\[
\boxed{n_-(A^{\rm zero}_{N,T})
=n_-(D_T|_{\operatorname{ran}E_{N,T}})\le r_T.}
\tag{14}
\]

Full row rank of E_{N,T} is sufficient for equality, but not necessary: retaining the entire negative coordinate subspace also suffices. Separate rank-two tests on individual pairs do not by themselves prove simultaneous interpolation or independence across all pairs.

Equation (14) applies to the windowed signed sampling form (13). It must not be assigned to the compression of the *full* form if zero contributions outside W_T are still present. Those contributions need exact isolation or a separate signed budget.

The set W_T is a region of the spectral parameter. It is not by itself a projection operator on a test-function space. A coordinate projection on the zero representation, a finite-dimensional restriction, and multiplication by a spatial window are different operations.

## 4. Why this does not prove the preceding J_N zero-free request

The inherited adaptive rule is

\[
t=T+1,\quad \vartheta(T)=\pi/4-1/t,\quad
M_0(T)=\left\lceil\sqrt{t(32+20\log t)/3}\right\rceil,
\qquad N=M_0(T)-1.
\tag{15}
\]

It controls the approximation error in [F] and [G]. Neither source establishes a signed-zero-form identity for A_N, its window projector, nor n_-=0 for that operator. Also, the displayed error estimates are for |Re p|≤1/2; they do not by themselves control the entire right half-plane requested in the earlier message.

For zeros of J_N rather than of full xi, a newly defined zero-sampling form could be built and its blocks counted. That would concern J_N and require its own source identity. It would not be the original Weil form merely by using the same block notation.

There is a direct local discriminator for the actual scalar head, requiring no spectral identification. Suppose a nonzero holomorphic J has a zero rho=sigma_0+i gamma with sigma_0>0 and order k. Write

\[
J(p)=a(p-\rho)^k+O((p-\rho)^{k+1}),\qquad a\ne0.
\]

Along the horizontal line through rho,

\[
\boxed{4\Re(J'(\rho-\varepsilon)\overline{J(\rho-\varepsilon)})
=-4k|a|^2\varepsilon^{2k-1}+O(\varepsilon^{2k})<0}
\tag{16}
\]

for all sufficiently small epsilon>0. The point still has positive real part and the same imaginary part. Consequently, a proved h_N≥0 throughout the requested right-hand region would exclude its zeros there. That lower bound is not established here. At the zero itself h_N=0, so testing h_N only at zeros cannot discriminate the defect.

## 5. Dependency closeout

DOWNSTREAM_CONSUMER: the earlier owner request, zero-freeness of the exact fixed-N, fixed-theta J_N in the prescribed band.

ACTUAL_CONSUMER_REQUIREMENT: exclusion of zeros of that function on that domain; a preferred matrix or all-support RH result is not required.

ORIGINAL_REQUESTED_OBJECT: an explicit (1,1) block in A_N and the negative index of its frequency-window compression.

ORIGINAL_OBJECT_IS: UNKNOWN for the undefined A_N-to-signed-sampling correspondence; NOT_NECESSARY as the sole proof mechanism for J_N zero-freeness.

FAILURE_TYPE: NO_DERIVATION of the source correspondence and window rank/sign. EPISTEMIC_STATUS: RESEARCH_DEBT, not impossibility.

Two available representations of the unresolved part, with ordinal planning estimates:

- Exact ray-evaluation pullback plus simultaneous rank and signed-form identity: diagnostic power 9/10, cost 4/10 once A_N is explicitly defined. It rejects a rank-losing window immediately; it does not prove a sign by itself.
- Direct argument principle or a whole-domain sign certificate for the literal J_N: diagnostic power 10/10, cost 8/10. A contour must have complete boundary coverage; the unbounded right-hand part requires a separate bound. Finite point samples are not a zero count.

DISCRIMINATORS: (9) for pair visibility; the actual signed form on the image in (14) for compression; a strict negative local head value in (16) for a putative off-axis root. None was numerically tested in this turn.

No previous predictions are rescored. This is an algebraic source clarification, not a new numerical experiment or a blinded adjudication. No claim that a particular off-axis zero exists is made. No repository or route-state write was performed.
