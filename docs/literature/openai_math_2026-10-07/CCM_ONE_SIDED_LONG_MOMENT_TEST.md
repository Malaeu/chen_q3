# Actual one-sided long-source moment — own test

2026-10-08. Root derivation; independent read-only audit negative_moment_transfer PASS, including refined t=m^(3/8) control. RH/SP OPEN. Same FULL_CCM_COUPLED_MOMENT_DRIFT phase, same original K_m, N=m, L=log m. No Pro question sent.

## Exact obstruction and source

Q05 bounds short arithmetic high moments but leaves all long cycles beyond two insertions unbounded. The original consumer needs only the negative spectral moment, whereas a bound for the full even moment also controls an unnecessary positive sector. This test removes that excess requirement without asserting a new source estimate.

For fixed even p>=4, m>=2^(p-1), x=m^(1/(p-1)), retain Q05(6): U=Pi(B-C_short)Pi, V=Pi C_long Pi, S=U-V=Pi K Pi. All matrices and the grid remain those of Q05; V depends on p through its lower arithmetic cutoff, not through a changed carrier. Q05(14),(23a) give

    Tr|U|^p <= D_p m L^(p*p+1),   D_p=3+A_(p-1).                (1)

V is the literal integral over (L/(p-1),L] of Pi Q(s) Pi against the signed measure sum Lambda(n)/sqrt(n) delta_log(n) - exp(s/2)ds + exp(-s/2)ds. The internal endpoint atom is in U, the final endpoint kernel is zero. Both continuous terms and every prime power are retained.

## Positive Schatten duality avoids false adaptive cyclicity

For a Hermitian A and p>1, with p'=p/(p-1),

    ||A_+||_p = sup {Tr(W A): W>=0, ||W||_(p')<=1}.             (2)

Indeed Tr(W A)<=Tr(W A_+)<=||W||_(p')||A_+||_p. If A_+ is nonzero, the optimizer is W=A_+^(p-1)/||A_+||_p^(p-1); otherwise W=0 attains zero. Hence for Hermitian A,H,

    | ||(A+H)_+||_p - ||A_+||_p | <= ||H||_p.                 (3)

This is a scalar inequality between norms, not the generally false operator inequality (A+H)_+<=A_++H_+. Apply (3) to A=V,H=-U. Since -S=V-U,

    | ||S_-||_p - ||V_+||_p | <= ||U||_p.                    (4)

Thus both inequalities hold:

    Tr S_-^p <= 2^(p-1)[Tr V_+^p + D_p m L^(p*p+1)],
    Tr V_+^p <= 2^(p-1)[Tr S_-^p + D_p m L^(p*p+1)].           (5)

An exponent independent of arbitrarily large fixed even p for the actual long positive moments is therefore equivalent to the requested exponent for compressed negative moments, with the common exponent enlarged at most to max(A,1). Constants, log powers and starting indices may depend on p. Nothing here is uniform when p grows with m; the RH receiver chooses p fixed first, then m large. The Q4 endpoint fee restores K once, as Q05(30), with polynomial exponent one.

This is a weaker sufficient target than Q05's full even moment, but it is not a supplier for it. No bound for Tr V_+^p has been obtained.

## Actual negative-density identity and failed norm closure

Let W=S_-^(p-1), M=Tr S_-^p. Because W is functional calculus of the actual S,

    Tr(W V)=M+Tr(W U),
    |Tr(W U)|<=M^((p-1)/p)||U||_p.                            (6)

The unpaid pairing is the actual signed arithmetic integral Tr(W V), not a generic PSD test and not a rotated rooted-word formula. Replacing it with Schatten Holder gives only M^((p-1)/p)||V||_p, returning the old unbounded long norm. Replacing V by V_+ recovers the forward inequality in (4); applying positive-part duality in both directions proves its absolute-value form; this is a valid one-sided reduction, not an estimate. No adaptive projector was moved through U or V.

## Negative control outside the literal arithmetic class

Let d=2m+1, b=ones/sqrt(d), Pi=I-bb*, e one coordinate vector and g=Pi e. Put t=m^(3/8) and define the synthetic matrices

    K=L I-t ee*, U=L Pi, V=t gg*, S=Pi K Pi.

For every unit flat vector c (all coordinate moduli 1/sqrt(d)),

    ||Kc||<=L+t/sqrt(d)<=L+1;
    b*Kb=L-t/d>=L/16                 (m>=8);
    ||Kb||<=L+1;
    Tr K²=dL²-2L t+t²<=dL²+m.

The short U satisfies (1) and Q05's short operator envelope. Also Tr V²=t²(1-1/d)²<=m, [U,V]=0, so the quadratic credit is exactly zero. However,

    Tr S_-^p=[t(1-1/d)-L]_+^p ~ m^(3p/8)                (7)

for every fixed p as m tends to infinity. Its full floor also respects the existing exponent3/8+epsilon envelope: lambda_min(K)=L-t>=-m^(3/8). Thus the flat-vector, positive-boundary, full second-moment and short high-moment bounds, plus nonnegative credit, cannot alone imply a common polynomial exponent. This synthetic control is NOT the prime/continuous CCM source and does not refute SP, RH or a source-specific inequality. The failed hypothesis is precisely any claim that those generic envelopes already enforce the needed arithmetic cancellation.

## Decision

Do not repeat a generic Holder/positive-part or cyclic-credit-only proof. Seek a source-specific one-sided upper-tail estimate for the literal V, or an upper estimate for the actual pairing (6). This note changes the supplier specification and rejects a concrete insufficient proof strategy; it does not improve the established full floor. An alias search must preserve the signed prime/continuous source and all projections, and must not import probabilistic independence.


## Bounded alias return

Dictionaries: positive-part Schatten duality and one-sided spectral moments; signed prime-product fibers and large deviations of Dirichlet polynomials; centered covariance/closed-walk graph contraction. The first dictionary supplies (2)–(5), not the arithmetic bound. The synthetic control above distinguishes an actual source supplier from a generic matrix envelope.

Researcher long_positive_alias ran three shelf queries; all returned ASK_STATUS: INCOMPLETE because q3_docs freshness failed. This is not evidence of literature absence. No additional global absence claim is made.

One local primary-source candidate was reread by root: OpenAI, Ordinary two-point correlations of multiplicative functions, graph-setup.tex, lines1–120 at pin adc7f1241b42e322a6451854ab7e4b4c146bf78a. SHA256 a0288ebfcbffa2e40008b273815a132bb002493fbd224d2fea78cf9f1b404eb1. Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/graph-setup.tex#L86-L107

Verbatim quantifier boundary: “All graph parameters are fixed when X tends to infinity.” The Proposition Divisor graph estimate bounds a limsup X-average of a specially weighted additive correlation F(x)G(x+hd), not a positive-part matrix moment. Its g_d contains core divisibility, two endpoint cutoffs and center factors (1_(p|x)-theta/p), with theta=1/4. The weight moments in lines70–84 use an actual uniform residue probability space and independent prime coordinates.

Mapping test: our m simultaneously changes the cutoff, Fourier grid and full source; our centering subtracts continuous densities in log n, not those prime-residue factors. No map from Pi Q(s) Pi against dnu to g_d, no fixed-parameter X-average return, and no discarded-complement estimate have been supplied. The theorem's hypotheses are therefore UNMAPPED, not implied by the existing second moment. Its precise statement is verified discovery evidence only; it is an excluded supplier for this target, not an audited proof of the manuscript. The coherent deterministic spike has no such residue-space structure, so the graph hypotheses appropriately exclude that control.

Next bounded question: estimate the actual negative-density pairing (6), or the actual positive long moments, with one finite exponent independent of p. Stop and record failure if the calculation only invokes the generic envelopes falsified by (7), or replaces the signed source by the graph model without a complete map. No new consumer estimate follows from this alias return.


## 2026-10-09 bounded return after the q-block test

Baseline d39e8b0e. No new moment bound obtained. The exact original (6) means
that a proposed Tr(WV)<=theta M+E, theta<1, must establish
Tr(WU)<=-(1-theta)M+E for THIS W=S_-^(p-1). Merely knowing [W,S]=0
or the short Schatten bound does not supply that signed arithmetic statement.
The earlier CCM_SPECTRAL_COMMUTATION_ATTEMPT.md already retains the residual;
CCM_NEGATIVE_SUBSPACE_L1_TEST.md already pays the unsuccessful sparse return.
These are reused, not new results or new impossibility claims.

Three shelf dictionaries (deterministic self-consistent negative spectral
density; relative form/Mourre positive commutator arithmetic translations;
signed transfer correlation spectral Gibbs negative projector) returned
ASK_STATUS: INCOMPLETE due to q3_docs freshness. No absence conclusion follows.
Researcher long_positive_alias returned no usable mapped supplier.

One primary lead was checked by researcher and then independently reread by
root as DISCOVERY evidence: Maurizio Laporta, On Ramanujan expansions and
primes in arithmetic progressions, arXiv:2204.01581v1, Theorem1, PDF page3.
URL: https://arxiv.org/pdf/2204.01581v1 . Local source:
sources/laporta_2204_01581v1.pdf,186925bytes,SHA256
f79ed7856dc9dd073d44c7ff6112a117e1bac34cb22322b1ab6d34e4bcad9608.
The hypothesis on its Delange series (8) is: "be convergent for every
sufficiently large N". Conditional on that, (9) bounds scalar Delta(N,h)
by O_epsilon((N+h)^epsilon). Source page4 explicitly notes its connection
to the Hardy-Littlewood prime-pair conjecture and the missing unconditional
cancellation. This is not an unconditional prime-correlation theorem.

Mapping status: source N is a scalar arithmetic cutoff, h an additive shift;
our m also determines Fourier carrier and W. Neither the Delange convergence
hypothesis nor a return from its scalar correlation to f_W(n), moving long
cutoff and both continuous terms has been proved. The synthetic commuting
spike has no corresponding arithmetic correlation or verified Delange series,
so this theorem cannot exclude it through a mapped hypothesis. EXCLUDED
CONDITIONAL LEAD; no theorem is admitted, and no arithmetic status changes.
Do not send Pro the already-tested generic adaptive-weight question again.
A next request needs a concrete additional source hypothesis and a worked
check that distinguishes the actual matrix from the synthetic spike.
