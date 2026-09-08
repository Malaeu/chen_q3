# STATUS: TRY_PHYSICAL_ENERGY_ALIGNMENT_WITH_FIXED_WIDTH_EXHAUSTION
```yaml
OPERATIVE_CLASS: TRY_PHYSICAL_ENERGY_ALIGNMENT_WITH_FIXED_WIDTH_EXHAUSTION
PRIMARY_COUNT: 1
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
REQUEST_ID: REQ-2026-09-08-ALIGN
BOUNDARY_ID: GOAL058_PRIME_ALIGNMENT_CAP_ON_FIXED_WIDTH_STAR_CLASSES_AND_EXHAUSTION
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PARTIAL_WITH_PRECISE_REMAINDER
  Q1b: PARTIAL_WITH_PRECISE_REMAINDER
  Q1c: PROVED_ON_CLASS
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a: PARTIAL_WITH_PRECISE_REMAINDER
  Q2b: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PROVED_ON_CLASS
  Q3a: PROVED_ON_CLASS
  Q3b: PROVED_ON_CLASS
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 55ed9f8e863bd1c5fb01509b63d8b6695882cfeb
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ALIGN_2026-09-08.txt
  GIT_BLOB: 666a6b959b6832a552de9fd6e5aff18db4b87dd5
  SHA256: 53bed85907edfaefaf8da6bdf23ab56f131e072cb21e0db4cccd3f2c05f8d6a1
  BYTES: 13766
  LINES: 74
  FINAL_LF: true
  GITHUB_CONNECTOR_FETCHED: true
  FETCHED_TEXT_REASSEMBLED_AND_HASHED: true
  SHA256_AND_GIT_BLOB_INDEPENDENTLY_RECOMPUTED: true
  ALL_CHECKS_MATCH: true
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISIONS:
  ALL_P_ALIGNMENT_CAP_PROVED: false
  NEGATIVE_UPPER_WITNESS_FOR_FULL_WEIL_FORM: false
  FIXED_WIDTH_PRIME_CLASSES_EXHAUST_MODULO_TRANSLATION: true
  INTEGER_CENTRES_WITH_FIXED_WIDTH_EXPLICIT_COVER: true
  POLE_NULL_CLASSES_DENSE_IN_UNCONSTRAINED_LOCAL_FORM_DOMAIN: false
  POLE_NULL_WEIL_CRITERION_VERIFIED: true
  UNCONDITIONAL_COMPACT_POLE_NULL_NEAR_NULL_SEQUENCE: true
  UNIFORM_POSITIVE_PHYSICAL_L2_FLOOR_ON_ALL_C_P: refuted
  UNCONDITIONAL_LIMIT_RHO_EQUALS_ONE: not_proved
  UNCONDITIONAL_LIMIT_BETA_EQUALS_ZERO: not_proved
  UNCONDITIONAL_LIMIT_RHO_AT_LEAST_ONE: true
  UNCONDITIONAL_LIMIT_BETA_AT_MOST_ZERO: true
  BOUNDED_PRIME_PART_ON_ALL_ADMISSIBLE_TESTS: refuted
  SATURATION_1_84_FOR_SELECTED_COMPUTED_OPTIMIZERS_IS_A_LAW: false
  LIMIT_LOBE_COEFFICIENTS_IDENTIFIED: false
  COMPENSATE_4_2_DOMAIN_ARGUMENT_COMPLETED: true
CLOSES: [REQ-2026-09-08-ALIGN]
CLOSED_RESEARCH_QUESTIONS:
  - Q1c_and_Q3_fixed_width_coverage_and_terminal_test_ideal
  - Q2a_unconditional_near_null_obstruction_to_a_uniform_positive_floor
  - Q1b_bounded_prime_saturation_as_an_all_test_premise
  - COMPENSATE_section_4_2_domain_completion
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
NEW_DERIVATIONS:
  SCOPES: [ABSTRACT, COFINAL_FAMILY]
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
EXECUTION:
  HASH_COMPUTATION: true
  NUMERICAL_RUN_PERFORMED: false
  RAW_EIGENVECTOR_OR_INTERVAL_CERTIFICATE_RERUN: false
  LEAN_EDIT: false
  ARISTOTLE_SUBMISSION: false
  SHARED_STATE_OR_QUEUE_EDIT: false
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ALIGN_2026-09-08.md
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  OLD_DOCUMENTS_OVERWRITTEN: false
  COMMIT_AND_READBACK_HASH: supplied_in_delivery_receipt
  COMMIT_IS_NOT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, source boundary, and what actually changes

**The all-P alignment inequality is not proved here, and no negative full-Q witness is produced.** The result is not a finite numerical minimum promoted to a theorem. Four analytical conclusions do change the task:

1. The requested fixed-positive-width prime-centred classes are already exhaustive **up to translation**, by the unconditional prime number theorem. Translation preserves the full source form, the physical norm, and total pole-nullity. Composite centres and growing width are not needed for this implication.
2. There are explicit compact smooth pole-null tests, transferred into these classes, with both Q divided by the physical norm squared and Q divided by the positive Dirichlet energy tending to zero. No sign of those approximating Q-values is assumed. Thus a uniform positive floor is impossible, but the missing nonnegativity is not supplied.
3. The signed prime contribution per physical norm is **unbounded on the union of these classes**. A value near 1.84 on a selected finite optimizer cannot become an all-test saturation premise. The corresponding archimedean energy also grows; this does not refute their required relative comparison.
4. Arbitrary pole-null profiles on an overlapping cover are not a lattice-restricted arithmetic object: they represent every smooth pole-null function supported in that cover. Their profile coordinates have an exact redundancy. Both the proposed mechanism and the requested limiting shape must be expressed in the synthesized physical function.

The proofs are below. The all-P sign remains a single missing inequality on those same physical functions, not an allegedly established consequence of these conclusions.

**Repository source keys, all at the request commit unless stated otherwise.**

- [REQ]: the byte-verified request in the header, read completely. Its `BASE_TIP: see bind line` has no additional binding line in the 74 supplied lines; the owner's explicit immutable request commit is the evidence cutoff used here. This causes no substitution of tasks or branch-tip evidence.
- [COMP]: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COMPENSATE_2026-09-07.md`, blob `c1d642bff22990c4399223ba1db18213b3b71680`; particularly (1), Sections 4.2, 5, 6, and the prospective registrations.
- [CHECK]: `docs/routeB_bus/COMPENSATE_INDEPENDENT_CHECK_2026-09-08.md`, blob `805cb115094d65b9bc997c1635f8a461fc167217`. Its independently re-derived arguments and its floating-point checks are distinguished; the latter are not interval proofs.
- [WIDTH]: `docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_COMPENSATE_WIDTH_2026-09-08.md`, blob `cf5959a796a8a7b94bdd959d9161b566b053c746`.
- [REPORT]: `docs/routeB_bus/SIX_CENTRE_FIXED_WIDTH_ASSEMBLY_REPORT_2026-09-07.md`, blob `2b215b9fcf6f472db05d6e47afd2cb97248751d6`, particularly Addendum 2. It contains aggregate energies, not a complete certified extremal eigenvector ledger.

The shelf SHA-256 prefixes for these secondary documents are request-supplied; they were not all independently rehashed here. Their pinned connector blob identities are recorded above. No old conversation export supplies a missing mathematical premise. `docs/Progress_Log.md` and personal archives were not opened; the source and audit already provide the needed registrations.

**Primary external references actually used.** [PNT] is NIST DLMF 27.12.1, the unconditional asymptotic for the nth prime. [XI] is DLMF 25.4.3--4, the completed xi normalization and functional equation. [CC20] is Connes--Consani, arXiv:2006.13771v1, Introduction (1)--(2), Appendices A--C, especially Proposition C.1 and (155). [DIGAMMA] is the difference series DLMF 5.7.6, equivalently [COMP]/[CHAIN]'s positive series for the archimedean multiplier. The theta calculation in Section 4 is derived explicitly; only the Gaussian Poisson identity enters it. The zero-counting bound used for dominated summation is the unconditional classical bound O(T log T), recorded in DLMF 25.10.1.

The cited arXiv:2608.24827v2 was inspected at its main statements: it distinguishes fixed-window certificates and variational upper bounds from its RH-conditional asymptotic theorem. None of those numerical certificates or the conditional theorem is used as an all-P supplier. The Connes 2026 theta discussion was consulted, but its printed kernel normalization is not copied: Section 4 fixes its normalization directly from [XI]. HTML mathematical texts, not PDF figures, were used in this audit.

All new analytical assertions below have verifier **PAPER**, awaiting independent review. Claims about reported runs have scope **FINITE_CELL**, verifier **CONDITIONAL**. There is no Lean proof or newly executed numerical experiment.

## 1. Q1(a): what alignment measures, and what it does not

### 1.1 The physical source object

[ABSTRACT][PAPER; source formula from COMP (1)] Set
\[
 I=(-\delta,\delta),\qquad \delta=\frac{\log(3/2)}8,
 \quad A(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\frac\pi2.
\]
Write U_t f(x)=f(x-t), use an inner product antilinear in its first argument, and define
\[
 \mathcal D(f)=\int_0^\infty A(t)\|U_tf-f\|_2^2dt,
 \quad M_\pm(f)=\int f(x)e^{\pm x/2}dx,
\]
\[
 \Pi(f)=2\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}
                  \Re\langle f,U_{\log m}f\rangle.
\]
Here Pi is the **signed prime contribution**, not a positive operator. The full form is
\[
 \boxed{\mathcal Q(f)=\mathcal D(f)-c_A\|f\|_2^2-\Pi(f)
       +2\Re\{M_+(f)\overline{M_-(f)}\}.}                 \tag{A1}
\]
For compact support the prime sum is finite. Every active prime power is retained. On the total-pole-null space the requested cap is exactly
\[
                    c_A\|f\|^2+\Pi(f)\le\mathcal D(f).  \tag{A2}
\]

Let E_P={1} union {primes p<=P}, x_p=log p, and
\[
 J_Ph=\sum_{p\in E_P}U_{x_p}h_p,\qquad
 \Omega_P=\bigcup_{p\in E_P}(x_p-\delta,x_p+\delta).
\]
A finite smooth partition of unity on this open cover proves the exact equality
\[
 \boxed{\mathcal C_P=C_c^\infty(\Omega_P;\mathbb C)
                         \cap\ker M_+\cap\ker M_-.}      \tag{A3}
\]
Indeed, split a compactly supported f by a subordinate partition, then translate each piece back by x_p. Conversely each synthesized function has the stated support and moments. Individual pieces need not have zero moments; only their sum does. No approximation or omitted overlap is involved.

In Fourier convention hat f(xi)=int f(x)exp(-i xi x)dx,
\[
 a(\xi)=\Re\psi(1/4+i\xi/2)-\psi(1/4)\ge0,
\quad
 \mathcal D(f)=\frac1{2\pi}\int a(\xi)|\widehat f(\xi)|^2d\xi,
\]
\[
 \widehat{J_Ph}(\xi)=\sum_p e^{-i\xi x_p}\widehat h_p(\xi).
                                                               \tag{A4}
\]
The function a is even, increasing in |xi|, and unbounded. For example,
\[
 a(\xi)=\sum_{j\ge0}
 \frac{(\xi/2)^2}{(j+1/4)((j+1/4)^2+(\xi/2)^2)}.         \tag{A5}
\]
This follows from the digamma difference series; monotonicity is termwise, and unboundedness follows by retaining arbitrarily long finite harmonic sums before sending |xi| to infinity.

The full prime formula in profile coordinates is
\[
 \Pi(J_Ph)=2\Re\sum_{m\ge2}w_m\sum_{p,q\in E_P}
        \langle h_p,U_{\log m+x_q-x_p}h_q\rangle,
 \qquad w_m=\Lambda(m)/\sqrt m.                          \tag{A6}
\]
A safe finite enumeration uses m<=ceil(P exp(2delta)); correlations outside the actual support difference set are exactly zero. The centre cutoff P is not permission to drop a prime power just above P that has a genuine offset overlap. Equations (A4) and (A6) preserve physical Gram terms, all shifts, and both orientations.

### 1.2 Exact star-alignment defect

[ABSTRACT][PAPER; derived here] For the isolated star in the **product** profile norm, put W=(sum_p w_p^2)^(1/2), H_w=sum_p w_p h_p, with leaves p prime and centre h_1. Expansion of squares gives
\[
\begin{split}
 W\left(\|h_1\|^2+\sum_p\|h_p\|^2\right)
       -2\Re\langle h_1,H_w\rangle
 &=W\left\|h_1-\frac{H_w}W\right\|^2\\
 &\quad+W\sum_p\left\|h_p-\frac{w_p}{W^2}H_w\right\|^2.
\end{split}                                                   \tag{A7}
\]
Thus maximum star alignment is a precise statement: all leaves lie in the weighted common-profile direction and the centre matches it.

But this does **not** force an increasing regional energy of the individual profile. Choose any nonzero h in C_c^infty(I) with M_+(h)=M_-(h)=0, for example h=(partial_x^2-1/4)eta with nonzero eta in C_c^infty(I). Set
\[
                h_1=h,\qquad h_p=(w_p/W)h.              \tag{A8}
\]
Both total moments vanish and the right side of (A7) is zero. The quotient of the sum of individual Dirichlet energies by the product norm is exactly D(h)/||h||^2, independent of the number of leaves. This is an exact control against an inference from alignment alone to increased single-profile energy. It is not a negative Q witness.

After overlap the product norm is not the physical norm and the isolated star is not the full prime operator. In particular (A7) is not an all-P physical cap. The only relevant archimedean energy then is (A4), **including its cross terms**. Regional/endpoint pieces from a disjoint decomposition cannot be counted separately without their compensating mixed terms.

There is an additional exact obstruction to reading intrinsic information from the isolated star after overlap. Take a nonzero real smooth u supported in the overlap at log29 and log31. Set h_29=U_(-log29)u and h_31=-U_(-log31)u. This is a zero-synthesis tuple, while its weighted leaf sum is nonzero: the two translates have different compact supports. Choose h_1 in C_c^infty(I) with both pole moments zero and nonzero pairing against that weighted sum. Such a choice exists: otherwise the nonzero weighted sum would lie in span{exp(x/2),exp(-x/2)} on I, which is impossible because it has compact support strictly inside I. Adding any multiple of the zero-synthesis tuple leaves f, D(f), Pi(f), and its total moments unchanged, but changes the isolated-star pairing linearly. The omitted terms cancel that change exactly. The bare star therefore does not even descend to the physical quotient. Its saturation is not a basis-invariant observable there.

### 1.3 Why the table is not yet a cap

[FINITE_CELL][CONDITIONAL for the measurements; ABSTRACT/PAPER for the following logic] At P=47 the request itself reports two different directions: a prime maximizer with prime about 2.4518, and a relative-ratio maximizer with prime about 1.839. The latter is not an upper bound on the former, much less on the full class.

Checking payment on the prime maximizer cannot replace checking every direction. An exact planted control is
\[
 H=\operatorname{diag}(3,1),\qquad K=\operatorname{diag}(2,3/2).
\]
The prime-maximizing direction e_1 has H[e_1]=3>2=K[e_1], but
\[
                  (H-K)[e_2]=-1/2.                     \tag{A9}
\]
This is a strict negative upper witness against that **inference rule**, not a model of the Weil coefficients.

**Answer to Q1(a).** The correct candidate energy is D of the synthesized function, not the centre's separate energy, not the pole constraints alone, and not the product star norm. Formula (A4) gives its exact alignment-sensitive value. A universal inequality linking that energy to the full arithmetic gain has not been derived. Calling that inequality “the energy cost of alignment” does not prove it. The precise attempted operator comparison is given next.

## 2. Q1(b): the attempted cap and its first unpaid inequality

[ABSTRACT][PAPER] Work in the closure of C_c^infty(Omega_P) intersect ker M_+ intersect ker M_- in the logarithmic-energy form norm. This is a physical-function space, not the redundant product of profiles. D is a closed positive form. It has a positive L2 lower bound at every fixed P: if d_P=diam(Omega_P), then
\[
 \mathcal D(f)\ge 2\left(\int_{d_P}^{\infty}A(t)dt\right)\|f\|^2>0
 \quad(f\ne0).                                          \tag{A10}
\]
This follows because U_t f and f have disjoint supports for t>d_P. It is not a positive lower bound for Q.

Let D_P be its self-adjoint associated operator on the closed moment-null L2 space. Let K_P be the bounded physical compression of the full prime operator (A6), including all active offsets. Define
\[
 T_P=D_P^{-1/2}(c_A I+K_P)D_P^{-1/2}.                    \tag{A11}
\]
No positivity of c_A I+K_P is assumed. This operator is self-adjoint and compact. To verify compactness, a bounded logarithmic-energy set has uniformly small Fourier L2 tails, since a(xi) tends to infinity. On a bounded frequency band, the supported-to-band-limited Fourier map is Hilbert--Schmidt. The low-band compact approximation and the uniform tail bound prove compact embedding of the form domain into L2. Hence D_P^(-1/2) is compact; composition with the bounded middle operator proves the assertion.

The source ratio and variational equation are therefore
\[
 \rho_P=\sup_{0\ne f\in\mathcal C_P}
 \frac{c_A\|f\|^2+\Pi(f)}{\mathcal D(f)}
       =\lambda_{\max}(T_P),                            \tag{A12}
\]
\[
 (c_A I+K_P)f=\rho_P D_P f
 \quad\text{weakly against moment-null test directions}.\tag{A13}
\]
The top eigenvalue is positive and attained in the form completion: one can use a nonzero pole-null test supported in a sufficiently short subinterval with no prime correlations, for which the numerator is c_A||f||^2>0. No theorem that this eigenvalue is <=1 follows from compactness.

The exact first unpaid comparison is
\[
 \boxed{\forall P\ge2:\quad I-T_P\succeq0,}
 \quad\text{equivalently (A2) on every }\mathcal C_P.     \tag{A14}
\]
The constructions in (A7)--(A13) do not establish (A14). They explain exactly why a comparison of separate extrema, or a cap inferred from the selected prime maximizer, is insufficient. Replacing K_P by its absolute value would strengthen and change the target; that is not done.

No source-defined contraction, positive innovation formula with a paid base, or all-P signed extension proving (A14) is supplied in this attempt. No negative full-Q upper witness is supplied either. **Q1(b) remains PARTIAL_WITH_PRECISE_REMAINDER.** This is an attempted comparison with an identified failure of its proposed shortcut, not a refusal to work because the conclusion is strong.

## 3. Q1(c) and Q3: fixed-width coverage is stronger than the request assumes

### 3.1 Translation preserves the relevant quantities

[ABSTRACT][PAPER] Direct substitution in (A1) gives, for every real b,
\[
 \|U_bf\|=\|f\|,\quad D(U_bf)=D(f),\quad\Pi(U_bf)=\Pi(f),
 \quad M_\pm(U_bf)=e^{\pm b/2}M_\pm(f),
\]
\[
                         Q(U_bf)=Q(f).                  \tag{A15}
\]
The pole product is invariant because the two exponential multipliers cancel. On total-pole-null functions both numerator and denominator of (A12) are separately invariant as well.

### 3.2 Fixed-width prime-centred cover

[COFINAL_FAMILY][PAPER; unconditional PNT input] Write p_j for the jth prime. By [PNT], p_j/(j log j) tends to 1; therefore p_(j+1)/p_j tends to 1 and
\[
                        \log p_{j+1}-\log p_j\to0.       \tag{A16}
\]
Fix the original delta, without shrinking it. Choose an index j_0 beyond which these log-gaps are <delta/2. This entrance is justified by PNT, not by an unknown spectral minimum. No numerical entrance bound is claimed.

Let f be any compact smooth total-pole-null test, with support in (-R,R). Translate it by b=log p_(j_0)+R. Its support is inside
\[
                   (\log p_{j_0},\log p_{j_0}+2R).
\]
Take the finite string of primes starting at p_(j_0) and ending at the first prime whose logarithm exceeds the right endpoint. Their fixed-half-width-delta intervals cover the whole translated support with overlap. By (A3), U_b f belongs to C_P for the last prime P. The centre at 0 and all unused primes receive zero profiles.

Consequently
\[
 \boxed{\text{Every compact smooth pole-null test is a translate of a member
 of some }\mathcal C_P.}                                \tag{A17}
\]
This is exact representation of each test, not just density. The unshifted support unions do miss fixed intervals near the origin; (A15) is the additional fact that makes this harmless for the sign problem. This distinction repairs, rather than contradicts, the thin-family caveat of COMPENSATE Theorem 5.

If beta_P=inf_(C_P\{0}) Q(f)/||f||^2 and H_00^c denotes all compact smooth pole-null tests, then
\[
 \inf_P\beta_P=\inf_{0\ne f\in H_{00}^c}\frac{Q(f)}{\|f\|^2},
 \qquad
 \sup_P\rho_P=\sup_{0\ne f\in H_{00}^c}
                          \frac{c_A\|f\|^2+\Pi(f)}{D(f)}.\tag{A18}
\]
Both equalities follow in both directions from inclusion and (A15)--(A17).

**Answer to Q1(c).** Proving the requested fixed-width cap for every P would already provide global pole-null Weil nonnegativity. The premise “Theorem 5's coverage failure also applies at fixed width” is false once translation covariance and overlap are used. Also, Theorem 5 already retained actual prime star edges: shrinking width excludes offsets, not the exact star overlaps. The new significance is coverage, not the first appearance of primes.

### 3.3 An explicit all-integer fixed-width law

[COFINAL_FAMILY][PAPER; no PNT needed] To remove even the asymptotic entrance from Q3, use all positive integers as centres. Here write the full lobe width as ell=2delta. For every R>=1 choose
\[
 m_0=\lceil4/\delta\rceil,
 \quad x_0(R)=-R-\log m_0,
 \quad P_R=\lceil m_0 e^{2R}\rceil,
 \quad\ell_R=2\delta.                                  \tag{A19}
\]
For m>=m_0,
\[
 \log(m+1)-\log m<1/m\le\delta/4.
\]
The centre indexed by m_0 is -R; the final centre is >=R. Thus the intervals of half-width delta cover [-R,R]. A bump positive on [-delta/2,delta/2], divided by the finite sum of its translates, gives a smooth partition near this interval. Multiplying it by f and translating the pieces gives an exact representation of every f in H_00^c supported in (-R,R). All extra centre profiles are zero. Total moments are preserved by the equality of the sum, not imposed separately.

Fixed width with overlap is therefore sufficient. With freely growing width Q3 is even simpler: one lobe can contain any prescribed compact support. Formula (A19) answers the nontrivial fixed-width version. There is no need to use a width depending on an unknown minimum or to enumerate a growing set of disconnected microscopic supports.

### 3.4 The density qualification and the terminal criterion

[ABSTRACT][PAPER] The union in Q3, as literally defined, consists only of moment-null functions. It is **not dense in the unconstrained form domain on a fixed full window**. M_+ and M_- are continuous independent functionals there; their joint kernel is closed of codimension two. A nonnegative nonzero smooth bump has nonzero moments and cannot be approximated in that fixed-window form norm by this union. The same obstruction holds in the weighted space used in Section 4. This is why “density in the whole domain” must not be asserted silently.

What (A19) gives is exact coverage of all compact smooth **pole-null** tests and hence a form core for each corresponding constrained local domain. That is enough for the published criterion, not because two missing directions have been approximated away.

The precise dictionary is
\[
 g(u)=u^{-1/2}f(\log u),\qquad
 \widetilde g(s)=\int_0^\infty g(u)u^{s-1}du
               =F(s-1/2),\quad F(z)=\int f(x)e^{zx}dx.
                                                               \tag{A20}
\]
Thus tilde g(0)=M_-(f) and tilde g(1)=M_+(f). [CC20, Appendix C, Proposition 1, (155)] says that the compact smooth test ideal with those two vanishing conditions already suffices for RH. Its geometric sum has the opposite sign to Q on this ideal, by its explicit formula. This verifies the support, measure, conjugation, and sign crosswalk; it does not assume positivity.

Combining that theorem with (A15)--(A19) proves the conditional chain
\[
 \boxed{Q\ge0\text{ on every }\mathcal C_P
 \iff Q\ge0\text{ on }H_{00}^c
 \iff RH.}                                               \tag{A21}
\]
The rightmost implication is a verified published consumer, not a reason to abandon an attempted proof of the leftmost inequality. On RH the same explicit formula gives full compact-test Weil nonnegativity, including nonzero pole moments. Without going through that theorem, an elementary density argument has not supplied those missing moment directions.

### 3.5 What composite centres and overlaps change

[ABSTRACT][PAPER] They change the coordinate representation, not the source form. The metric is J_P^*J_P; after overlap one must quotient by ker J_P or work directly with f. The prime operator is J_P^*KJ_P, not a weighted star. Composite centres create exact non-star edges, for example between m and 2m, and atoms 4,8,9 act with their actual von Mangoldt weights. Prime-only centres already have offsets when their differences lie close to a prime-power logarithm. Formula (A6) includes all of these uniformly.

Because translations preserve correlations, placing a test “away from the lattice” in absolute position does not remove its prime interactions. Those depend on **support differences**. Only a verified absence of the relevant differences removes an atom. Neither coverage nor this coordinate crosswalk proves a sign.

## 4. Q2(a): unconditional near-null tests, and the direction of the implication

### 4.1 A normalized canonical function, derived rather than guessed

[ABSTRACT][PAPER] Let
\[
 \Theta(t)=\sum_{m\ge1}e^{-\pi m^2t},\quad t>0,
\]
\[
 \Phi(x)=\sum_{m\ge1}
 \left(4\pi^2m^4e^{9x/2}-6\pi m^2e^{5x/2}\right)
                                      e^{-\pi m^2e^{2x}}.\tag{A22}
\]
The Gaussian Poisson identity gives
\[
 1+2\Theta(t)=t^{-1/2}(1+2\Theta(1/t)).
\]
The function v(x)=e^{x/2}(1+2Theta(e^(2x))) is therefore even, and direct differentiation shows
\[
               \Phi=\tfrac12(\partial_x^2-1/4)v.
\]
Thus Phi is even. On x>=0 its differentiated series has double-exponential decay, and evenness gives the same statement at the other end. All its derivatives have that decay. In particular its bilateral Laplace transform is entire.

For s=1/2+z with Re s>1, substitute t=e^(2x) and integrate twice by parts. All boundary terms vanish in this half-plane. If a=s/2, the coefficient is
\[
                   2a(a+1)-3a=a(2a-1)=s(s-1)/2.
\]
Using int_0^infty Theta(t)t^(s/2-1)dt=pi^(-s/2)Gamma(s/2)zeta(s) gives
\[
 \boxed{\int_{\mathbb R}\Phi(x)e^{zx}dx
       =\xi(1/2+z),\qquad
 \xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).}     \tag{A23}
\]
Entire continuation proves the identity for all z. This fixes the numerical factor in (A22); a schematic theta formula with a different factor is not silently substituted. On the real Fourier axis hat Phi(t)=Xi(t), using the functional equation.

For each nonnegative integer k put
\[
 g_k=(\partial_x^2-1/4)\partial_x^k\Phi,
 \qquad
 F_k(z)=(z^2-1/4)(-z)^k\xi(1/2+z).                     \tag{A24}
\]
Every g_k is nonzero, smooth, rapidly decreasing with all exponential weights, and has exactly zero pole moments. Its transform vanishes at every centred nontrivial zero, regardless of that zero's real part.

### 4.2 The source-domain passage is legitimate

[ABSTRACT][PAPER] Define
\[
 \|f\|_X^2=\|e^{|x|}f\|_2^2+\|f'\|_2^2.
\]
The full geometric form (A1) extends continuously to X. A convenient completely explicit bound for its Hermitian pairing is
\[
                  |Q(f,g)|\le22\|f\|_X\|g\|_X.          \tag{A25}
\]
Here are the separate estimates; Appendix A gives the rational ledger.

- D(f,g) is bounded by 18||f'|| ||g'||, from the translation inequality and int t^2 A(t)dt<18.
- |<f,U_t g>|<=exp(-|t|)||exp(|x|)f|| ||exp(|x|)g||. Thus the prime pairing is bounded by 12 times the two weighted L2 norms, using sum_(m>=2) log m/m^(3/2)<6.
- Each pole moment is bounded by sqrt(4/3)||exp(|x|)f||. The pole pairing is bounded by 8/3 times the weighted norms; c_A<7.
- Combining the derivative and weighted-L2 estimates by the two-component Cauchy inequality gives (A25).

Choose one fixed even smooth cutoff chi, equal to 1 on [-1,1] and supported in (-2,2), and put
\[
 g_{k,R}=(\partial_x^2-1/4)
                    [\chi(x/R)\partial_x^k\Phi(x)],\quad R\ge1.\tag{A26}
\]
For every fixed k these are compact smooth tests with M_+=M_-=0 exactly, by integration by parts. Their convergence to g_k in X follows from the double-exponential decay of Phi and its derivatives through order k+3. The cutoff derivatives introduce only bounded powers of 1/R.

To see Q(g_k)=0 without an illicit positivity premise, apply the **signed**, centred explicit formula to g_(k,R):
\[
 Q(g_{k,R})=\sum_{\rho}
 F_{k,R}(\rho-1/2)
       \overline{F_{k,R}(1/2-\overline\rho)}.             \tag{A27}
\]
The transforms and their limits decay faster than any power of |Im z|, uniformly in R, throughout |Re z|<=1/2. This follows by repeated integration by parts and uniform weighted bounds on their derivatives. The unconditional zero-counting bound O(T log T) consequently gives an absolutely summable majorant in (A27). Each limiting summand is zero by (A24). Dominated convergence and (A25) prove
\[
                         Q(g_k)=0.                       \tag{A28}
\]
This does not assert that the zero-side terms are squares. Away from the critical line they need not be nonnegative. They vanish here because the chosen transform vanishes at **all** zeros. No zero has been assumed to lie on the line, nor has an unknown zero been used to choose a parameter.

### 4.3 What the construction proves for the actual classes

[COFINAL_FAMILY][PAPER] D(g_k)>0 for every k. Indeed zero D would force invariance under every translation, and a translation-invariant L2 function is zero. By (A25)--(A28),
\[
 \frac{Q(g_{k,R})}{\|g_{k,R}\|^2}\to0,
 \qquad
 \frac{Q(g_{k,R})}{D(g_{k,R})}\to0.                      \tag{A29}
\]
For each R transfer this test into some C_P using (A17). Q, D, the physical norm, and the zero moments are preserved exactly. If necessary enlarge the successive P's by inclusion so that they form an increasing sequence. Therefore
\[
 \boxed{\lim_{P\to\infty}\beta_P\le0,
        \qquad\lim_{P\to\infty}\rho_P\ge1.}             \tag{A30}
\]
The limits exist in the extended reals because beta_P is nonincreasing and rho_P nondecreasing. For any c>0 the construction supplies, at some finite P, an upper witness Q(f)/||f||^2<c/2. Hence Q(f)-c||f||^2<0. This rigorously refutes a uniform positive physical-norm floor on all C_P. It is much stronger evidence for that conclusion than a decreasing finite table.

But (A30) does **not** prove beta_P tends to zero or rho_P tends to one. One undiscovered negative test would give beta_P<=-c and rho_P>=1+d for every sufficiently large P, while all the near-null tests above would still exist. Thus the source dichotomy is
\[
\begin{array}{ll}
 Q\ge0\text{ on }H_{00}^c:&\beta_P\downarrow0,\quad\rho_P\uparrow1;\\
 Q(f_*)<0\text{ for one }f_*:&\lim\beta_P<0,\quad\lim\rho_P>1.
\end{array}                                                   \tag{A31}
\]
The second line includes an infinite limit where appropriate. Exact equality in either limit is equivalent here to the all-class sign, by nesting, (A18), and (A30). This is an explained implication, not an argument for refusing the target.

The request's proposed “concentrate the transform near a zero” is not the argument used. In a positive sampling representation, a large transform **at** a zero contributes positive energy, not zero energy. The unconditional control above instead makes the transform vanish at every zero and then cuts off the physical function.

Also, relative and L2 quotients are not generally interchangeable. On the nested spans of e_1,...,e_n in l2, let D e_j=j e_j and Q=I. Then rho_n=1-1/n tends to 1 while the L2 bottom is identically 1. The equivalence for the present source needs the additional exhaustion and near-null arguments just proved; it is not a norm-equivalence assertion.

**Answer to Q2(a).** An eventual strictly positive *uniform* L2 floor is ruled out unconditionally. Exact approach to zero from above, and exact approach of rho to one from below, are not established without the unpaid sign. No decay rate for beta_P is proved here.

## 5. A source counterexample family to bounded prime saturation

[COFINAL_FAMILY][PAPER] This section refutes an input suggested by Q1(b), not Q itself. From (A24), on the real Fourier axis,
\[
 |\widehat g_k(t)|^2
   =(t^2+1/4)^2|t|^{2k}|\Xi(t)|^2.                       \tag{A32}
\]
All moments are finite. For any 0<B<C, the normalized mass in [-B,B] is bounded above by
\[
 \frac{B^{2k}\int_{-B}^B(t^2+1/4)^2|\Xi(t)|^2dt}
 {C^{2k}\int_C^{C+1}(t^2+1/4)^2|\Xi(t)|^2dt}\longrightarrow0.
                                                               \tag{A33}
\]
The denominator integral is strictly positive: Xi is analytic and not identically zero, so it cannot vanish on an interval. Since a(t) is nonnegative and tends to infinity, (A33) implies
\[
                         \frac{D(g_k)}{\|g_k\|^2}\to\infty.
\]
Using (A28) and the zero moments in (A1) then gives
\[
 \boxed{\frac{\Pi(g_k)}{\|g_k\|^2}
       =\frac{D(g_k)}{\|g_k\|^2}-c_A\longrightarrow\infty.}\tag{A34}
\]
Cut off as in (A26), with R sufficiently large for each fixed k, and use the X-continuity estimates for Pi, D, and Q. Then translate into C_P. For every proposed fixed constant C this yields a nonzero compact smooth pole-null f in some C_P with
\[
                 \Pi(f)>(C+1)\|f\|^2.                  \tag{A35}
\]
The cutoff can be chosen from the explicit theta derivative tails and (A25), not an unknown class minimum. Thus the residual C||f||^2-Pi(f) has a strict negative upper bound. This is the promised exact family defeating a **uniform bounded-prime cap** on all admissible tests. Its Q-value can be made arbitrarily small in magnitude relative to its norm; no negative sign for Q is asserted.

What the data show near 1.84 is the prime part of several **selected computed rho-extremizers**. They neither give a bound on all admissible tests nor determine what every future extremizer does. The new construction does not prove that the actual unique finite-P maximizer, if uniquely chosen, has diverging prime energy. It proves that a universal proof cannot use bounded prime energy as an all-test premise. Alignment may require matching large energies rather than keeping the prime part small.

## 6. Q2(b): the extremizer, the nonuniqueness, and admissible losses

### 6.1 What can be identified without inventing missing data

[ABSTRACT][PAPER; reported numerical labels FINITE_CELL/CONDITIONAL] The intrinsic extremizer satisfies the weak generalized eigenvalue equation (A13). That is its source-defined structural characterization. [REQ]/[REPORT] supply D, Pi, and the ratio at four cutoffs; they do not supply the component eigenvectors, a certified separation from the constant-profile subspace, or their phase conventions. Those aggregate numbers cannot determine which individual lobes or Legendre degrees carry the optimizer.

For arbitrary compact smooth profiles, a literally nonzero constant profile is not in the class; the “mean sector” refers to a particular piecewise-constant form-domain compression. Moreover, after overlap the same physical f has infinitely many smooth profile decompositions, as the zero-synthesis construction in Section 1 shows. One may add highly oscillatory overlap bumps to two profiles with opposite synthesis without changing f or either energy. Therefore a limiting list of lobe coefficients or a Legendre sign pattern is not an intrinsic object unless a decomposition gauge is fixed first.

The physical null candidates are not unique either. The functions g_k in (A24) are linearly independent, as seen by dividing their transforms by (z^2-1/4)xi(1/2+z). Their compact approximants all have ratios tending to one. Under an eventual all-class sign, each is a near-extremizing family. After a chosen recentering, one such family converges to g_0, another to g_1, and so on. Translating them into the unshifted prime classes can also produce sequences escaping every compact set, with no nonzero local limit in that coordinate.

Thus neither the four energy rows nor rho tending to one would identify a unique limiting Q-null test. The canonical g_0 is an explicit **possible near-null limit**, not a theorem or prediction identifying the measured optimizer. The all-P sign and a separate extremizer-selection/compactness statement would be needed for that stronger conclusion.

A falsifiable qualitative prediction is retained for a later audit: after fixing the physical synthesis and an explicit profile gauge, any stable near-critical component should be tested against the span generated by cutoffs of the g_k family and translations, not against a uniquely selected constant vector. This is a proposal for discrimination, not a claim that this span has been proved to characterize all near-null directions.

### 6.2 What “exact in the limit” actually requires

[ABSTRACT/COFINAL_FAMILY][PAPER] On a normalized test put q(f)=Q(f)/D(f). The near-null family has q(f_R) tending to zero. A bound of the form
\[
        Q(f)\ge [1-\widehat\rho_P-\varepsilon_P]D(f)
\]
certifies nonnegativity only if its **proved** upper estimate satisfies
\[
                     \widehat\rho_P+\varepsilon_P\le1.  \tag{A36}
\]
Along a near-null family, a fixed positive loss multiplying D would consume the available relative margin. But this does not ban a multiplicative loss on the final margin, a signed retained correction, or losses proved to vanish rapidly enough.

For the terminal regularized interface, the actual requirement is
\[
                      Q(f)\ge-\eta_n\|f\|^2,
                 \quad\eta_n\to0                      \tag{A37}
\]
on exhausting full supported classes. If one obtains only Q>=-epsilon_n D, one still needs a valid bound converting that error into (A37) on the relevant directions. D/||f||^2 is unbounded; (A34) demonstrates this even along near-null source functions. A relative error in D cannot simply be renamed an L2 error.

No rule deriving (A36) or (A37) from the four reported ratios is proved. WIDTH's admissible-loss principle is preserved, with its actual norm and quantifiers, rather than replaced by an identity-only prohibition.

## 7. COMPENSATE audit closeout and the missing domain paragraph

### 7.1 What is ratified from the returned audit

[ABSTRACT][PAPER; audit receipt, not a new execution] [CHECK] independently re-derives the endpoint payment, the three offsets, the 47/6000 smooth mean-zero slice bound, the six-dimensional algebraic head, and the two-witness scalar obstruction. The original prospective probabilities were **0.90, 0.86, 0.95**, not the later posterior values near 0.97,0.92,0.97. The original numbers and event wording are preserved in Section 8.

The audit's grid checks support its calculations but are not outward enclosures. No arbitrary grid check has been elevated to a proof of an interval inequality. Its explicit caveat is correct: COMPENSATE Section 4.2 left its domain passage as a sketch. The following completion addresses that passage only; it does not prove the unpaid six-head sign.

### 7.2 Core and restoration of all eight constraints

[ABSTRACT][PAPER] On the finite disjoint six-lobe domain of COMPENSATE, use the supported logarithmic norm
\[
 \|f\|_{\log}^2=\frac1{2\pi}\int(1+\log(2+|t|))|\widehat f(t)|^2dt.
\]
It is equivalent to the positive shifted archimedean form norm there. Prime shifts and pole functionals are bounded on the fixed support, so they do not change its closed form domain.

For one interval, inward dilation about its centre converges strongly in this norm and places the support strictly inside the interval. In Fourier space the dilation acts by a phase, an argument dilation, and a scalar. These converge strongly first on a dense bounded-frequency subset. The inequality
\[
 1+\log(2+|t|/r)\le 1+\log(2+|t|)+|\log r|,\quad0<r\le1,
\]
provides uniform boundedness for r near 1 and extends the convergence to the whole space. Convolution by a smooth approximate identity then converges by Fourier dominated convergence; choose its support smaller than the interior support margin. The result is a compact smooth approximation. Apply this construction on the six component intervals. The disjoint cross forms are bounded kernels, so componentwise convergence suffices for the full form norm.

Let L be the eight continuous functionals consisting of the six ordinary means and the two total pole moments. Their independence on L2(I)^6 is exactly the already audited independence of the six constants and the two exponential representers. Their restriction to the dense smooth core remains onto C^8: otherwise a nontrivial linear combination would vanish on that core and by continuity on all L2, a contradiction.

Choose eight fixed smooth vectors psi_j for which the matrix C=(L_i psi_j) is invertible. Given any smooth approximation y_r of a constrained y, define
\[
             y_r^0=y_r-\sum_j\psi_j(C^{-1}L y_r)_j.       \tag{A38}
\]
Then L y_r^0=0 exactly and y_r^0 tends to y in form norm, since L y=0. This restores **all eight** constraints, not merely the two poles. The 47/6000 inequality on the smooth tail therefore passes to its complete closed-form tail by continuity.

### 7.3 Head generators and the cross map

[ABSTRACT][PAPER] Each interval indicator and restricted exponential has a zero-extended Fourier transform O((1+|t|)^(-1)), by direct integration or one integration by parts, including its endpoint terms. Multiplying that transform by the logarithmically growing archimedean symbol remains L2. Thus the full-line archimedean multiplier supplies an L2 representative of its form pairing, whose restriction is the representative on the supported domain. Adding the bounded prime and pole operators preserves this operator-domain membership.

The finite head generated by these functions therefore lies in the operator domain. Its pairing with the tail is a bounded L2 cross map, and the already proved coercive tail has a legitimate inverse. Completion of the square gives the exact Schur identity quoted in COMPENSATE. This completes the previously sketched domain justification. It changes no width, source coefficient, head dimension, or floor. The six-head sign remains open.

## 8. Verdict ledger, predictions, and the single next task

### 8.1 Question ledger

| Question | Determination | Scope / verifier |
|---|---|---|
| Q1(a) | Physical D is the relevant energy; isolated-star alignment identity is exact, but does not yield a universal energy charge. The star is not quotient-invariant after overlap. | ABSTRACT / PAPER |
| Q1(b) | No all-P cap and no negative full-Q witness. The first missing bound is (A14). Bounded prime saturation on all tests is disproved by (A34)--(A35). | COFINAL_FAMILY / PAPER for obstruction; CONDITIONAL for cap |
| Q1(c) | At fixed positive width, all-P positivity already reaches the global pole-null consumer by PNT coverage and translation. The thin-width caveat cannot be copied here. | COFINAL_FAMILY / PAPER |
| Q2(a) | Near-null sequence is unconditional; lim beta<=0 and lim rho>=1. Equality from the favorable side still requires the cap. | COFINAL_FAMILY / PAPER, sign unresolved |
| Q2(b) | Weak extremal equation derived. Actual finite eigenvector and limiting profile are not identified from the supplied aggregate data; profile coordinates are redundant after overlap. | ABSTRACT / PAPER; FINITE_CELL / CONDITIONAL for table |
| Q3(a) | Exact fixed-width coverage of compact pole-null tests; explicit integer law (A19). Not density in the unconstrained local form domain; the published pole-null criterion supplies the valid replacement. | COFINAL_FAMILY / PAPER |
| Q3(b) | Full Gram/synthesis quotient and every arithmetic shift are mandatory. Composite centres are not necessary for coverage but create additional exact edges. | ABSTRACT / PAPER |

### 8.2 Frozen observer predictions: no retroactive repair

| Original ID and probability | Fate in this adjudication |
|---|---|
| P_ALIGN_MECHANISM_NAMED, 0.70 | NOT_ACHIEVED as the requested cap mechanism. Naming D and deriving (A7) is not a proof that alignment forces enough D; (A8) explicitly defeats the separate-profile version. |
| P_ALIGN_CAP_PROVED_ALL_P, 0.30 | NOT_ACHIEVED. The target is unproved, not mathematically refuted. |
| P_RHO_TO_ONE_FORCED, 0.60 | NOT_ACHIEVED for the exact event rho->1 and floor->0. The unconditional one-sided conclusions (A30) do not count as confirmation of that event. |
| P_EXTREMAL_NOT_MEAN, 0.85 | UNRESOLVED as a full structural event. The report describes a finite non-mean optimizer, but lacks the eigenvector/sector comparison needed to identify it, and no unique limiting profile is derived. |
| P_LATTICE_CLASSES_EXHAUST, 0.50 | CONFIRMED with the explicitly stated pole-ideal qualification. Formula (A19) gives fixed-width exact coverage; (A20)--(A21) give the actual consumer linkage. Literal density of the unconstrained domain is not claimed. |

NOT_ACHIEVED scores the forecast that this answer would produce a proof; it is not a falsification of the underlying conjecture. No probability or original event has been changed.

### 8.3 Own COMPENSATE registrations against CHECK

| Original ID | Original p | Fate and qualification |
|---|---:|---|
| P_COMP_ENDPOINT_PROOF_SURVIVES_REVIEW | 0.90 | CONFIRMED at the unchanged width and the same three offsets, as reported by CHECK. |
| P_COMP_MEAN_ZERO_TAIL_SURVIVES_REVIEW | 0.86 | CONFIRMED for the audited smooth 47/6000 bound and six-dimensional reduction; CHECK's domain caveat is retained and completed analytically in Section 7, pending review of this completion. |
| P_COMP_TWO_WITNESS_SCALAR_OBSTRUCTION_SURVIVES | 0.95 | CONFIRMED in its original full-space scope, including its exclusion of an automatic harmonic-lift conclusion. |

Their original squared forecast errors for the reported survival events are 1/100, 49/2500, and 1/400. This is scoring of the review return, not independent validation of all its numerical details.

Two expectations were registered publicly in this turn before the corresponding proof checks: fixed-width prime coverage after translation, p=0.85, and inability to infer the favorable limiting sign from near-null tests alone, p=0.95. Both are confirmed by (A17) and (A30)--(A31). No claim of a prior Git-blinded registration is made.

New prospective audit predictions, not scored now:

- P_ALIGN_COVERAGE_SURVIVES_INDEPENDENT_REVIEW, p=0.92: (A15)--(A21) survive with the same delta, total moments, and physical norm.
- P_ALIGN_NEAR_NULL_AND_UNBOUNDED_PRIME_SURVIVE, p=0.85: (A22)--(A35) survive with a correctly normalized theta kernel and the signed explicit-formula passage, without RH.
- P_ALIGN_DOMAIN_COMPLETION_SURVIVES, p=0.90: Section 7 closes the stated COMPENSATE domain paragraph without a new analytic premise.

### 8.4 Strongest attack, alternatives, and discriminator

**Strongest reviewer attack:** the near-null proof could conceal either a theta normalization error, a wrong conjugation in the zero-side identity, or an unjustified passage from compact tests to a global radical. Section 4 fixes the factor by Mellin integration, retains the signed zero pairing, and supplies uniform vertical decay plus a source X-norm bound. These are the places an independent review must attack first. A defect there reopens the near-null and bounded-prime conclusions; it would not affect the elementary integer cover or the translation formula.

The other decisive attack is that a prime-log cover might be treated as a form-preserving decomposition into individually pole-null pieces. That is not the proof: the sum equals the translated test exactly, and only total pole-nullity is imposed.

| Candidate representation | Decisive object | Kill power / cost, ordinal estimate |
|---|---|---|
| Physical energy-normalized operator | I-T_P in (A11)--(A14), with the physical synthesis quotient, full arithmetic and a signed complementary bound | 10/10 / 7/10 for a bounded local certificate; all-P cost unknown |
| Canonical-radical-aware decomposition | Separate a source-defined near-null range generated from (A24), then keep its exact mixed coupling to the complement before attempting domination | 9/10 / 8/10; neither range completeness nor its complement sign is granted |

An exact positive innovation identity remains admissible, but merely writing a signed base plus positive increments has already failed to supply a finite uniform sign. No large run is authorized by these estimates.

**DISCRIMINATOR:** a source-certified upper value U(Q(f))<0 for an explicitly synthesized, exactly pole-null physical test is a genuine negative witness. For a cap on T_P the corresponding event is a certified Rayleigh lower bound greater than 1, with the same denominator and the complete source error budget. A value or interval consistent with zero is not a kill. A positive finite compression is not a class pass. A class pass requires a signed lower bound including the entire complement; an all-P pass requires a proved rule in P, not more passing rows.

**Cheapest decisive check and exactly one CODEX DIRECTIVE: ALIGN_COVERAGE_AND_NEAR_NULL_SOURCE_AUDIT.** Read the pinned request and this verdict. Independently rederive (A15)--(A21) and (A22)--(A35), including the theta factor, both pole moments, zero-side conjugation, X-continuity, cutoff convergence, and the physical quotient. Verify the two explicit false-inference controls (A8) and (A9) first. Check that the constructed family proves no uniform positive floor and unbounded prime energy, but does not claim a negative Q or an upper bound rho<=1. Return the first incorrect equation, or an acceptance of these exact statements. No numerical run, packet enlargement, Lean edit, Aristotle submission, queue/state edit, or automatic new request is authorized. The failure code is ALIGN_COVERAGE_OR_NEAR_NULL_SOURCE_MISMATCH. This audit is one bounded paper transaction; it is not a request to rebuild the already audited six-centre instrument.

### 8.5 Dependency epistemics and closeout

**DOWNSTREAM_CONSUMER:** the unchanged published Weil criterion on complex compact smooth tests. **ACTUAL_CONSUMER_REQUIREMENT:** positivity on its sufficient pole-null ideal, or the existing vanishing-negative-error interface on complete exhausting supports. **ORIGINAL_REQUESTED_OBJECT:** uniform-in-P fixed-width alignment cap, limiting saturation, and lobe exhaustion. **ORIGINAL_OBJECT_IS:** the full all-P cap is equivalent to the pole-null sign through the proved cover; a bounded prime numerator, fixed positive gap, and a unique profile limit are NOT_NECESSARY.

**KNOWN_WEAKER_INTERFACES:** a signed lower bound on each canonical regularized Schur head; bounds Q>=-eta_n||f||^2 on full supports with eta_n->0; a direct source comparison (A14); or an exact positive representation with a proved base, domain, and limit. None is made true by naming it.

**FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT for (A14) and the canonical all-support Schur sign. Reopen with an actual source directional estimate or a signed full-complement certificate plus an all-P proof rule. No route-family death is asserted. Historical novelty is not claimed.

**Scoped refutations, all KILL_SCOPE=THEOREM_SHAPE, FAILURE_TYPE=COUNTEREXAMPLE, VERIFIER=PAPER:**

- Paying the prime maximizer alone certifies the whole form: (A9), exact upper residual -1/2.
- A fixed positive L2 floor on every C_P: (A26)--(A30), residual Q-c||f||^2 strictly negative eventually for each c>0.
- A fixed uniform bound on Pi/||f||^2 on all C_P: (A32)--(A35), strict negative upper residual C||f||^2-Pi(f).
- Unconstrained fixed-window density of total-moment-null tests: Section 3.4, the continuous nonzero moment of a positive bump.

These refutations are scoped to their explicit statements. In particular neither unbounded prime energy nor failure of a separate scalar estimate implies negativity of the full form. The existence of near-null tests supplies no upper bound on rho_P.

**What became smaller:** the coverage and no-uniform-floor questions are resolved by source proofs; the apparent bounded-prime mechanism and the uniqueness of redundant profile labels are removed. The operator comparison must pay the full, possibly large, prime energy on the same physical direction. **What remains:** the universal signed comparison (A14), equivalently the prior all-support sign after the verified criterion linkage. **What must not recur:** copying the shrinking-width noncoverage argument to fixed width; treating 1.84 as an all-test cap; interpreting near-null tests as evidence excluding negative directions; omitting physical Gram or total-moment restoration.

**Memory:** target ALIGN; cognitive operator REPRESENTATION_SHIFT; progress class REPRESENTATION_PROGRESS plus scoped FALSIFICATION_PROGRESS and the explicit source lemmas above; route score 4. There is no claim that the difficulty of the remaining sign has decreased merely because its coordinates are explicit.

**Verification handoff:** only the EXPECTED_VERDICT_PATH is to be written on rh_clean, with a [Proshka] commit. The delivery receipt supplies the resulting commit, parent, blob, byte count, SHA-256, and readback comparison. No Lean file is written, so lake/q3_check commands and an axiom profile are not applicable. Independent paper acceptance would upgrade the newly derived claims' review status, not close (A14) or authorize an RH claim.

## Appendix A. Exact rational and analytic ledger

[ABSTRACT][PAPER] These checks use identities, inequalities, and exact rational arithmetic; no numerical source run or interval certificate is claimed.

1. **Fixed width.** With r=1/5,
\[
 \log(3/2)=2\sum_{j\ge0}\frac{r^{2j+1}}{2j+1}>2/5,
\]
\[
 \log(3/2)<2\left(\frac15+\frac{(1/5)^3}{3(1-1/25)}\right)
 =\frac{73}{180}<\frac{51}{125}.
\]
Hence 1/20<delta<51/1000. Formula (A19) uses the exact delta; no decimal width is substituted. The overlap at 29,31 follows from 2*31^4<3*29^4.

2. **Dirichlet continuity.** Since A(t)=sum_(j>=0)exp(-(2j+1/2)t),
\[
 \int_0^\infty t^2A(t)dt
 =2\sum_{j\ge0}(2j+1/2)^{-3}
 \le16+\frac{16}{125}+\frac2{25}
 =\frac{2026}{125}<18.
\]
The first tail term and the integral comparison for the decreasing function (2x+1/2)^(-3) give the bound.

3. **Prime continuity.** On x in [m-1,m], m>=2,
\[
 \frac{\log m}{m^{3/2}}
 \le \frac{\log2+\log x}{x^{3/2}}.
\]
Integration and summation give sum log m/m^(3/2)<=2 log2+4<6. The factor two in Pi therefore gives 12, not 6.

4. **Poles and scalar term.** The integral of exp(plus-or-minus x-2|x|) is 4/3. Thus the polarized pole form has bound 8/3 in the weighted L2 norm. Integral comparison gives gamma_E<1; pi<4 and the exponential Taylor lower sum e^4>103/3>32 give log(8pi)<4. Hence c_A<7, and
\[
                     7+12+8/3=65/3<22.
\]
Together with the derivative bound 18<22 this proves (A25).

5. **Mellin normalization.** The two integrations by parts in (A23) give 2a(a+1)-3a=a(2a-1). With a=s/2 this is s(s-1)/2, precisely the normalization of xi in [XI]. Derivative multiplication is (-z)^k, not z-derivation of xi.

6. **False-inference control.** H-K=diag(1,-1/2) in (A9). The upper envelope -1/2 on e_2 is exact; no sufficient-condition failure is labeled a source-Q counterexample.

7. **Inherited COMPENSATE constants.** The audit's smooth-slice arithmetic is
\[
 1049/2000+1-3/2-1/60=47/6000,
\quad 47/6000-1/1000=41/6000.
\]
Hence the stated residual coefficient is 6000/41. Section 7 supplies the domain passage; this arithmetic supplies no sign for its six-dimensional head.

8. **Forecast arithmetic.** For the three returned COMPENSATE survival events the squared errors are (1-9/10)^2=1/100, (1-43/50)^2=49/2500, and (1-19/20)^2=1/400. Posterior probabilities in CHECK do not replace these registrations.

## 9. PROSHKA'S OWN LINE

I choose the physical energy comparison because the profile coordinates stop being unique once the lobes overlap.
The table is useful, but it mixes a star norm, a full prime maximum, and a different relative optimizer.
Those three objects need not pay their largest costs on the same function.
The first nearby alternative was another endpoint and regional-energy budget.
That remains useful on a specified small geometry, but it does not automatically survive an overlapping cover.
The second nearby alternative was a larger finite relative matrix.
It may certify a bounded class after a complement estimate, but more positive rows would not supply the universal rule.
The important new fact is that fixed width eventually makes the prime logarithms a cover of long intervals.
Overlap is therefore not only a conditioning problem; it also changes what the class can represent.
Translation turns that coverage into a statement about every compact pole-null test.
I did not use that conclusion to stop the proof attempt.
I used it to identify what any claimed fixed-width cap must actually control.
The first move beyond this batch is to audit the cover and the explicit near-null family independently.
A wrong theta normalization or an unjustified zero-side limit would kill the latter argument.
A separate mistake about total versus individual pole moments would kill the cover-to-consumer transfer.
The second move is to seek a directional estimate that preserves a canonical near-null range and its mixed terms.
A positive compression on that range alone would not certify its coupling to the rest of the space.
A source-valid negative upper witness would kill the proposed sign, while a negative lower estimate would not.
I would ask for the physical synthesized extremizer and its full residual rather than another four decimal places in the ratio.
I would also ask for a fixed decomposition gauge before discussing individual lobe coefficients.
What surprised me is how much the prime maximizer differs from the relative optimizer already in the supplied table.
What I distrust is the jump from that observation to a bounded prime contribution on all admissible tests.
The derivative family shows that large prime energy can coexist with almost zero total energy.
The cost is another large energy on the same function, not an absolute cap near the reported value.
I also distrust the assertion that approaching the critical ratio identifies a unique limiting shape.
There are multiple explicit global null functions and their translated compact approximations.
The construction rules out a permanent positive margin without deciding the missing sign.
That is the distinction a useful next proof must preserve.
The remaining task is an actual signed source comparison, not a new name for the measured cancellation.
Nothing in this verdict claims that this last comparison has been proved.
