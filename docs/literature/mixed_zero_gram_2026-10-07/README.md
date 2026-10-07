# Mixed zero Gram: alias return, 2026-10-07

Individual paired rows are explicit and their same-pair overlap cancels before Fourier truncation. The obstruction is the joint interaction of different pairs, the finite Fourier carrier, and the actual exceptional projector. A better-conditioned basis alone does not give a sign.

Consumer: in `DISPLACEMENT_AUDIT_2026-10-07.md`, Gamma<=g{(q0+rN)(gc+e)-Mc} for all actual exceptional vectors, every eta>0 with r=C_eta*m^eta on unbounded original cells m=N,L=log m. Known: Q7 exact projected return and middle-band same-pair tail bound; Q6 T>=2cA I. SP is open.

Negative control: on [0,L], the two unit exponentials 1/sqrt(L), exp(i*h*t)/sqrt(L) have Gram eigenvalue 1-|sinc(hL/2)| ->0 as hL->0. Bounded imaginary parts alone cannot give a uniform lower Riesz bound for raw exponentials. This is an abstract control, not a CCM counterexample.
UNVERIFIED search hints: mixed positive/negative Gram as oblique interpolation; clustered divided differences as a stable coordinate system with a nontrivial signed coefficient metric.
Dictionaries: operator mixed Gram/oblique projection; special-function cardinal sine/divided differences; control nonharmonic observability/Ingham clustered modes.

## Search and fetched candidate

Three shelf queries (mixed Gram exponential systems complex frequencies finite Fourier projection; Carleson interpolation nonseparated zeros signed Gram Schur complement; Hilbert inequality complex frequencies hyperbolic sine cosine correlation) returned ASK_STATUS INCOMPLETE due index freshness. This is not absence. External search sought an exact hypothesis/constant bridge.

Avdonin–Ivanov, *Exponential Riesz bases of subspaces and divided differences*, arXiv:math/0103160.
Primary PDF: https://arxiv.org/pdf/math/0103160 ; local `avdonin_ivanov.pdf`.
SHA256: 40a557049e47703b55e670633bc120ac8cc054342fc4f0cac638718c628451b6.
Quote, Theorem3, printed p7: “Let Λ be a relatively uniformly discrete sequence and r < r0.”
Discovery evidence VERIFIED by root reread of theorem and proof; strength CONDITIONAL PARTIAL, not a CCM supplier.

Theorem3(i), pp7–8: under its strip/relative-discreteness setup, generalized divided differences form a Riesz basis on (0,T) iff an exponential-type generating entire function of indicator width T satisfies the stated Helson–Szego condition on a horizontal line. Section1 condition(2) relates this to a bounded Hilbert-transform decomposition. This hypothesis is substantive, not a consequence of knowing the zeros lie in a strip.
Worked proof, §3.2 pp13–15: projection from half-line cluster subspaces to (0,T) is an isomorphism under that condition. Within each uniformly finite cluster, Lemma5 bounds Gram inverses by compactness: a vanishing eigenvalue would give a linearly dependent limiting divided-difference family, contradicting Theorem2. Constants depend on cluster size/radius and the fixed vertical strip; the paper does not provide the needed m-uniform signed comparison.

Mapping: exp(w*t)=exp(i*lambda*t) with lambda=-i*w=gamma-i*delta; T=L after interval translation. Pair sums/differences are exact linear combinations. Strip boundedness PROVED for the zeta strip. A shift into a positive strip is allowed on a fixed interval but its norm cost on growing L must be paid. Relative uniform discreteness, bounded cluster size, quantitative Helson–Szego constants: OPEN for the required families. Exponential-type generating function of the required width: OPEN; xi cannot simply be substituted. Finite Fourier projection and signed coefficient metric: additional OPEN transfers. The negative control is discriminated by divided differences/cluster hypotheses, but raw-coordinate conditioning costs return through coefficients.

## Bounded own test: basis changes keep the weight

Independent bounded check: causal_algebra_audit PASS for projector, weights and pair-norm asymptotic; no sign claim.

For any invertible cluster-coordinate matrix R, write C=D R. Then
CC*=D(RR*)D*, range(C)=range(D), Pi=I-C(C*C)^dagger C*=I-D(D*D)^dagger D*.
Thus the projector is unchanged but the negative Gram weight is RR*, not identity. The mixed block is Omega=Pcal D R. Replacing it by Pcal D while deleting R changes the source matrix. This algebra holds even for redundant columns when R is square invertible. It supplies no sign.
A concrete pair confirms the scaling: e^(delta*t+i*gamma*t)-e^(-delta*t+i*gamma*t)=2e^(i*gamma*t)sinh(delta*t). On the centered interval, its squared norm is asymptotic to delta² L³/3 when delta*L->0. Dividing by 2delta yields a stable derivative row, but the original Gram contribution retains the factor 4delta² (and its original multiplicity). Renormalization cannot discard that factor.

Rejected as immediate suppliers: bounded-strip-only Riesz inference; stable divided-difference coordinates with identity replacement of RR*; individual same-pair cancellation promoted to mixed operator norm. None refutes SP.
Next step/stopping condition: seek a source-specific mixed block estimate retaining RR*, both Fourier tails and Pi, with constants uniform in m. Stop this candidate as a supplier if the only available input is an unproved uniform Riesz/Helson–Szego bound; do not send a representational Q8 without new evidence.

## Source-specific completeness candidate: Burnol

Fetched primary source https://arxiv.org/pdf/math/0203120 (v7, 25 Feb 2004); published DOI https://doi.org/10.5802/jtnb.434 . Local `burnol_complete_minimal.pdf`, SHA256 cff449f51fe65cb8ae72f64b17e3dd4d9f5fb903776f9b825be77bfd75606039. The older shelf file `burnol_2002.pdf` is a different paper (math/0103058); it was not substituted.
Quote, §3 Theorem3.1: “They are a complete system if and only if a ≥ 1.” Root read the theorem, §2 domains/evaluators and §6 Proposition6.1 proof. Discovery evidence VERIFIED; strength PARTIAL ANALOGUE, not a quantitative sampling supplier.
The evaluators use ALL nontrivial zeros with derivative orders below multiplicity, completed right Mellin transform pi^(-s/2)Gamma(s/2) integral f(t)t^(-s)dt, in the cosine-Sonine space L_a: both f and its cosine transform are constant on (0,a). This differs from compact log-window Fourier carrier V_m and from the positive critical/pair-sum rows.
Worked mechanism in Proposition6.1: orthogonality to all zero evaluators gives G(s)=zeta(s)theta(s) with theta entire; functional equation gives Nevanlinna class in both half-planes. Krein yields finite exponential type; a>1 forces negative type, while a=1 plus square integrability and Paley–Wiener forces theta=0. Thus exact annihilation implies zero. No uniform lower frame constant for finite rows follows.
Mapping: Mellin/log-coordinate change formally available (PROVED elementary substitution); simultaneous Sonine support conditions for our vectors OPEN; gamma factor and norm transport OPEN; all-zero derivative rows to positive-only rows INAPPLICABLE without a new map; finite-height m-uniform lower bound OPEN. A complete sequence eps_n e_n in l2 with eps_n->0 has no positive lower frame bound, explicitly discriminating qualitative completeness from the required quantitative hypothesis. The actual theta near-null test is recorded in `POSITIVE_ROW_FRAME_OBSTRUCTION_2026-10-07.md` in the bus.
This candidate is not selected as a mechanism. Suzuki screw/canonical-system search returned the already-audited conditional positivity interface (`SHIFTED_XI_KERNEL_AUDIT_2026-10-06.md`); no new supplier was imported. The shelf search was INCOMPLETE, not negative evidence.
