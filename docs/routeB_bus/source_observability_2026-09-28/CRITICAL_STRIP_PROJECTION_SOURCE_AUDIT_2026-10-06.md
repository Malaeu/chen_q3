# Critical-strip projection: existing conditional source bridge

Status: selected-shell G3c PAPER_OWN rev from accepted HMODE/chi and G4;
no G1/G3 promotion, no fresh Lean check, no RH claim. Earlier reconciliation
sections below retain their narrower historical scope.
Source inspected: rh_clean, fc0b25a887feea95a4c7ee2191661184be0a53c7.
Scope: the selected Ferrers trial and its original cofinal shell, not the
new two-column plane span{c(G),c(G'')} and not the tracked ground vector.

## Actual consumer domain

`Q3/Proofs/RouteB/Goal058DirectGroundZeroEscape.lean:27` in
`q3.lean.aristotle/` requires locally uniform convergence only on
`centeredCriticalStrip`. `ClassicalXiInterface.lean:21` defines this as
`{z : |Im z| < 1/2}`. Every compact subset lies in a closed substrip
`|Im z| <= sigma < 1/2`; this is already proved in
`D0CriticalStripCompactBound.lean:26`.

Consequently estimates on strips of arbitrary height are a stronger
sufficient target, not a requirement of this final consumer. This does
not supply tracking for the ground family or change that family.

## Located source implementations

All paths below are under `q3.lean.aristotle/Q3/Proofs/RouteB/`.

1. `G6N1SelectedFerrersN2SourceScaledTailRate.lean:551` states
   `selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate`.
   From the exact mode, chi and theta rates, it proves

   `sqrt(L_k) * lambda_k^sigma * ||a_k (P_k g_k - g_k)|| -> 0`

   for each `0 <= sigma < 1/2`. Here `a_k` is the literal
   `selectedFerrersLemma73SourceScale`, `g_k` is the selected
   `prolateCombination` passed through `gTrial_m`, and `P_k g_k` is
   `gTrial_m_N` in the same Hilbert space. No source replacement occurs.

2. `G6N1SelectedFerrersN2CompactDecayAssembly.lean:902` states
   `selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates`.
   It turns that weighted residual into locally uniform convergence of
   the centered finite trial minus the anchored full-trial transform.
   The latter is evaluated at `-z`, retaining the production orientation.
   The per-index bound at line 780 is the rate above multiplied by

   `|R_k|`, where `R_k = Xi(0)/(a_k * Gwin_k(0))`.

   The finite trial norm cancels in the exact centered identity at line
   532. The ratio limit at line 749 uses `D.muntzLimit` at zero and
   `Xi(0) != 0`; it is not a new unconditional proof of the continuum
   limit. In particular, nonzero denominators alone would not establish
   their uniformly bounded inverses.

3. `Q3FourierOverlapCandidate20260922.lean:1375` derives the theta rate
   from the stated mode rate. At line 1423, the projection receiver also
   uses the chi-rate reduction. At line 1445,
   `selected_locally_uniform_xi_of_mode_rate` states convergence of the
   resulting selected shell's `centeredPstar` to `centeredXi` on the
   actual critical strip, still conditional on `hmode`.

4. The continuum-port input is itself constructed conditionally:
   `G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean:84-135` uses the
   source closed-substrip Mellin convergence theorem from hmode and chi
   rates, with the literal factor-four source scale. The shell constructor
   in `G6N1SelectedFerrersN2CompactDecayAssembly.lean:628-650` consumes
   exactly this port and `selectedFerrersPreAnchorData`. Root inspected
   both constructions. The continuum limit is therefore not an extra
   free premise of the hmode-only wrapper, although its underlying proof
   still needs to be included in any full dependency audit.

## What this establishes and what remains

The generic assertion that no source-specific compact projection bridge
is written is too coarse: the signatures and their proofs are present in
the current source. Root reread the weighted-rate theorem, compact-decay
signature, ratio proof and hmode-only candidate wrapper after the native
read-only explorer located them.

This inspection does not certify a fresh Lean build or the transitive
axiom set. A textual scan found no `sorry` or top-level `axiom` declaration
in the candidate file; this is not a substitute for kernel checking.
The hmode supplier, the continuum-port construction, and the exact
identification of this shell with the final tracked-ground family must
remain explicit. Trial convergence does not imply ground convergence;
G1 and G3 remain unpaid. PAPER_CHAIN node labels are not changed here.

The accepted `PROSHKA_VERDICT_GOAL058_HMODE_QUASIMODE_2026-09-25.md`
states HMODE for this same selected pair, anchors `1/h0(0), 3/h4(0)`,
full window `[-sqrt(k+2),sqrt(k+2)]`, and denominator `k+2=lambda_k^2`.
Root checked that the current candidate's Git blob is exactly the blob
read in that verdict: `010cdf1915d2cc3b08886a7de290660a5c73f1c5`;
SHA-256 `83a4bb5ee70b2b523aeccedf6f482a8b8887b7f95f30a3d4eb563be915adcfbd`.
This binds the comparison to the same candidate bytes, not a fresh proof
or axiom audit. Native independent review `/root/projection_bridge_audit`
completed one on-target pass with no substantive findings. It checked
the anchors (`G6N1CenterAnchorScalarLock.lean:85-90`), lambda dictionary
(`G6N1SelectedFerrersPaperParameterDictionary.lean:55`), cylinder argument
(`G6N1ParabolicCylinderD0D4Exact.lean:52`), and selected schedule.
It confirmed that no extra independent analytic premise appears in the
hmode-only wrapper. For arbitrary production `S`, the separate projection
receiver still requires `SelectedFerrersPreAnchorProductionFamilyCrosswalk S`
(`G6N1SelectedFerrersFirstOrderBudgetApplication.lean:32`); this is not
ground/trial tracking. The review did not repeat a complete PAPER audit
or run Lean and its transitive axiom check.

The explorer also located the exact common-shell join:
`G6N1SelectedFerrersFiniteCCMSourceRow.lean:76` defines
`selectedFerrersCofinalSourceData P` by the same generic constructor as
the N2 shell. Root read this definition. Choosing the same constructed
port P identifies their source data; it does not identify the trial with
the ground vector. The remaining ground-to-trial estimate must decay
after the compact kernel and central normalization factors, on this
same shell/reindex. Merely making the residual/floor ratio less than one
does not prove that decay.

Next bounded action: reconcile the accepted PAPER hmode result with the
exact candidate hypothesis and audit the same-shell ground/trial join
before deciding whether any G3c/G4 label can be updated. Do not reprove an arbitrary-height
projection rate as a prerequisite to this strip-only consumer.

## Direct fixed-limit projection estimate (PAPER checked)

This argument concerns the SAME selected shell, not the ground family.
Write m=N=k+2, lambda=sqrt(m), L=log(m), h_m=a73*q_m and
H=4*h_CCM. The accepted full-window HMODE/chi packet estimate and
the scalar crosswalk below give sup_(|x|<=lambda)|h_m(x)-H(x)|<=C/lambda^2.
The literal selected h_m is zero outside this window. Put
f_m=E_star(h_m) on [lambda^-1,lambda] and K=E_star(H) on (0,infinity).

For u in the window, at most lambda/u summands satisfy n*u<=lambda,
so their combined E_star error is at most C/(lambda*sqrt(u)).
For the omitted fixed target, |H(x)|<=C_H*x^-4 for x>0, and
sum_(n>r)n^-4<=C_4*r^-3 for r>=1. Consequently its contribution is
at most C_H*C_4*lambda^-3*u^-1/2. Thus, with a fixed C0,

    ||f_m-K||^2_(L2(window,du/u))
    <= C0^2/lambda^2 * integral_(lambda^-1)^lambda u^-2 du
    <= C0^2/lambda.

Let kappa(t)=K(exp(t)). Exact Poisson inversion for H gives
kappa(-t)=kappa(t). The explicit polynomial Gaussian and its derivative
give |H(x)/2+x*H'(x)|<=C1*x^-4. Termwise differentiation is justified
by locally uniform Gaussian domination, and for u>=1,

    |kappa'(log u)|
    = |sqrt(u)*sum_(n>=1)[H(nu)/2+nu*H'(nu)]| <= C2*u^-7/2.

Inversion gives the negative-log tail as well. Hence
D=||kappa'||_(L2(R)) is finite and independent of m.
For completeness, the inversion has an elementary source check: under
the exp(-2*pi*i*x*xi) Fourier convention, the transforms of
x^2*exp(-pi*x^2) and x^4*exp(-pi*x^2) are respectively
(1/(2*pi)-xi^2)*exp(-pi*xi^2) and
(xi^4-3*xi^2/pi+3/(4*pi^2))*exp(-pi*xi^2).
Thus h_CCM=(pi^2*x^4-3*pi*x^2/2)*exp(-pi*x^2) is Fourier invariant,
and H(0)=integral H=0. Poisson summation for this Schwartz H gives
sqrt(u)*sum_(n>=1)H(n*u)=sqrt(1/u)*sum_(n>=1)H(n/u), with no constant
or mass correction. This is the exact inversion used above.
The endpoint values at +/-L/2 agree. Integration by parts in the
literal Fourier basis V_n_m therefore has zero boundary term;
its shift log(lambda*u) contributes only the existing (-1)^n phase.
Bessel and Parseval give for the SAME |n|<=N orthogonal projection P,

    ||(I-P)K|| <= L*D/(2*pi*(N+1)).

Orthogonal contraction and linearity now yield

    ||a73*(P*gTrial-gTrial)|| = ||(I-P)f_m||
      <= C0*m^-1/4 + D*log(m)/(2*pi*(m+1)).

This proof differentiates only the FIXED explicit target K, never the
HMODE error or a uniform C0 convergence assertion.
For every fixed 0<=sigma<1/2, the compact Mellin kernel contributes
at most sqrt(L)*lambda^sigma. The displayed residual becomes

    O(sqrt(log m)*m^(sigma/2-1/4))
      +O((log m)^(3/2)*m^(sigma/2-1)) -> 0.

The centered finite-trial identity already cancels its Hilbert norm;
the remaining ratio Xi(0)/(a73*Gwin_m(0)) tends to 1 by the accepted
G4 continuum result and Xi(0)!=0. P preserves the constant mode, so
there is no new independent central denominator. Production orientation
-z is retained. The conclusion is projected-trial minus continuum-trial
convergence on each compact of |Im z|<1/2 for the selected shell.

Root checked D0KTrialStage1.lean:40,60 (measure, window and shifted basis),
D0KTrialStage2.lean:24,41,56 (E_star and literal projection),
D0PstarExplicitCCMLimitFourier.lean:29 (target), and the accepted G4
full-window packet crosswalk. The elementary window bound also appears
in G6N1SelectedFerrersOddMassDecay.lean:426. The independent author was
/root/projection_bridge_audit. Independent /root/g3c_projection_independent_check
verified the complete argument and source mapping without substantive findings.
It checked PreAnchorDataInhabitant:45--47, FactorFourPortRate:50,84--91,
D0KTrialStage1:126--141, D0PstarExplicitCCMLimitFourier:561--571 and
N2CompactDecayAssembly:532--549,749--774. The first assigned Luna checker
returned an off-target Type I answer; that was not counted. The Sol
escalation performed the actual independent G3c check. Root reread the
scalar/window/basis definitions and checked the elementary Fourier-Gaussian
inversion above. Result: selected-shell G3c is PAPER_OWN rev conditional
on the accepted HMODE/chi and G4 inputs.
No fresh Lean compilation or arbitrary-production-family crosswalk is claimed.

Shelf check: `./ask.sh 'centered critical strip quarter power tracking rate'`
returned useful local declarations but ASK_STATUS: INCOMPLETE (semantic
index freshness validation failed). No absence claim is based on it.

## Consumer-specific sufficient tracking rate (PAPER deduction)

This retains the same ground family and all matched hypotheses of
`../fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md`, (T1)-(T6): a simple
ground projector for the same full K, the selected center floor,
the exact reference/selected-row error, and the original cofinal schedule.
It supplies none of those hypotheses anew. Write t_m=E_m/Z_m.
The accepted conditional bound (T3), with (T6), gives

`sup_{z in K}|F_m(z)-T_m(z)| <= C m^(H/2) sqrt(log m) (alpha_m+4t_m)`

whenever K is a compact subset of `|Im z|<=H`, with
`C=|centeredXi(0)|/sqrt(cCenter)`. Here F is the trial-center-normalized projected-ground transform
of that source transfer, T is its matched centered trial. In particular
F is not replaced by the newly tested two-column U family.

For every compact K in the actual centered critical strip, choose
`0<=H<1/2` with `|Im z|<=H` on K. Assume on the full original eventual
sequence, with fixed finite constants C_alpha and A>=0,

`alpha_m <= C_alpha m^(-1/4) (log m)^A`.

Then the alpha contribution is at most

`C C_alpha m^(-epsilon) (log m)^(A+1/2) -> 0`,
`epsilon=1/4-H/2>0`.

The t contribution tends to zero by the matched exponential bounds in
(T5). Hence this rate is sufficient for locally uniform ground-to-trial
tracking on the whole open critical strip. In particular A=0 suffices.
Combining with the SAME shell's trial limit would supply hconv; the
real-zero and entire-family inputs remain separate obligations.

This does not assert a source proof of that alpha bound. It only corrects
the strength of the target needed by the final strip consumer. Original
(T7), quantified over every H>=0, is retained as a stronger sufficient
all-height statement; it is not necessary for this argument.

Negative controls: alpha=1 does not satisfy the proposed rate and does not
give decay of the displayed majorant. If alpha=m^(-p) with 0<=p<1/4, choose
2p<H<1/2; the displayed majorant then diverges. Conversely
alpha=m^(-1/4) is not superalgebraic but passes every strict substrip.
Failure of this sufficient norm bound does not refute transform tracking,
which may use cancellations not retained in (T3).

Native independent check `/root/projection_bridge_audit`, one pass:
no substantive findings; one WORDING clarification of C was applied.
The reviewer checked the trial-center-normalized projected-ground scale
in `G6N1SelectedFerrersTrackedGroundTransform.lean:153`; no independent
ground-center denominator is introduced. Status: verified conditional
PAPER consequence of (T1)-(T6). No source-node status is changed and no
alpha estimate is claimed proved. Lean was not run.


## Selected-shell G4 scalar and phase crosswalk (PAPER, 2026-10-06)

Source reread at HEAD f451d06f7cf754263a7bec82e1033e29bb882993.
This is a paper identification using the accepted HMODE/chi inputs,
not a fresh Lean build or a claim about the ground eigenvector.

Let A0=1/h0(0), A4=3/h4(0), d=sqrt(I0^2+I4^2),
q=(I4*h0-I0*h4)/d. In ProlateLayer.lean:73--76,
I0=integral h0=chi0*h0(0), I4=integral h4=chi2*h4(0).
The identifier chi2 is carrier index 2, corresponding to full mode 4;
it is not the Fourier eigenvalue of full mode 2.
The selected-source nonzero centers and d>0 justify the divisions.

With a72=-A0*A4*d/16, exact cancellation gives

    a72*q=(chi0*A4*h4-3*chi2*A0*h0)/16.

This is the source formula in G6N1SelectedFerrersZeroMassCylinderPacket.lean
:129 and :156. Its integral vanishes EXACTLY at every source index;
zero mass is not obtained by taking a limit. Accepted HMODE and chi->1
then give the full-window O(lambda^-2) approximation to

    (D4-D0*3)/16 = (pi/2)*x^2*(2*pi*x^2-3)*exp(-pi*x^2)
                 = h_CCM(x).

The target is literally CCM equation (7.1), and the selected packet is
an admissible choice of its 'suitably normalized' h_lambda in Lemma
7.2(ii). The paper does not fix an additional unique finite scalar:
we identify a valid representative, not an unspecified independently
normalized finite function. The source packet-rate theorem is at :182.

Parameter dictionary is lambda=sqrt(k+2), m=N=k+2=lambda^2,
c=2*pi*lambda^2, with Ferrers coordinate x/lambda and full modes 0/4.
This agrees with CCM (7.5),(7.9). Primary paper locators are
ccm.txt:1502--1587,1618--1632,1691--1709 in
../litreview/pdfs/survey_2026-09-03_sources/.

The production normalization is a DIFFERENT, explicitly recorded scale:
a73=4*a72 (G6N1SelectedFerrersFactorFourPortRate.lean:50).
It tends to 4*h_CCM, not to h_CCM. The exact source Mellin identity
G6N1ExplicitCCMLimitMellinNormalization.lean:744 states

    mellin(E_star h_CCM)(-i*z)=centeredXi(z)/4.

Its factor-four corollary at :768 yields centeredXi itself.
G6N1PreAnchorLimitZeroModeAndSelectedShell.lean:35 fixes the Mellin
coordinate -i*z; the reflected Xi argument is removed by the functional
equation in the displayed proof, not by changing the coordinate silently.
The polynomial argument -L*z/(2*pi) is the separate finite-transform
coordinate; it must not be confused with the Mellin variable -i*z.

Root reread the scalar identity, ProlatePair integral/center equations,
CCM equations and both Mellin-normalization theorems. Independent native
/root/projection_bridge_audit found no substantive error and confirmed
the selected parameter dictionary, with the representative-versus-unique
normalization qualification above. It found no new analytic premise
for this trial crosswalk beyond accepted mode/chi and the existing
Mellin-port proof. No ground/trial identification is inferred.

Conclusion: the selected-shell G4 scalar/phase/parameter correspondence
is resolved on PAPER conditional on the accepted HMODE/chi suppliers.
This does not assert the full arbitrary-production crosswalk, replace
G3, provide G1, or certify a transitive Lean build/axiom check.

A separate read-only reconciliation by /root/g3c_reconcile compared this
section with the primary CCM text and current definitions and found no
discrepancy. It confirmed that the paper leaves its finite scalar free,
so the displayed a72*q is an admissible representative without an extra
scalar hypothesis; the convergence estimate still consumes HMODE/chi.
