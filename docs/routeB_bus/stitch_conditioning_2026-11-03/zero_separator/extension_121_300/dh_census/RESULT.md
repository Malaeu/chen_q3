Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

The original DH table contains all four requested off-line pairs, with the quoted approximate coordinates matching their saved80-digit values. The source generator at rh_clean3691f8e has Git blob2ba30781cf00bf06ad07994422beef7afd08475b; the local generator matches it exactly. Original inputs were read only.

The preferred200dps census dh_zeros_600_200dps.json contains494 positive-height zeros through600:464 critical-line roots and15 off-line quartets, each represented by two reflected positive-height zeros. Eleven quartets are additional to the old230 table. Every20-height band agrees with the number of listed roots. Independent global discrete windings in the completed-function rectangle [-1,2]+i[.001,600] are494 at steps.25,.125,.0625. The corresponding maximum phase increments are.83347,.41738,.21745radians (exact figures in JSON). This is a numerical count match, not an interval argument-principle certificate or proof of simplicity.

New quartet right-hand coordinates (approximate):

|sigma|gamma|
|---:|---:|
|.8695305796|240.4046723514|
|.8195495921|320.8764896688|
|.7682231236|331.0502594079|
|.6285081083|366.6409075762|
|.8158736778|411.7967375490|
|.7088822243|440.4845107397|
|.5159183144|520.9438010351|
|.8469538031|531.2797268965|
|.7295334000|548.9067937778|
|.7865590820|566.5097129115|
|.5828556698|595.0233780278|

Critical-line sign scans used step.0625; all count-deficit bands were independently rescanned at.01 and gave identical critical counts. The off-line search used bounded complex Newton iterations, prioritizing large critical-root gaps, and retained only distinct roots with sigma>.500001. Reflected partners were independently evaluated. All coordinates were first refined at90dps, with off-line roots checked at120dps; then every root was refined at200dps in37.3s. The200dps table differs from the saved90dps coordinates by at most4.994e−83 and has maximum |D(s)| residual7.679e−197. dh_zeros_600.json preserves the90dps census as a comparison artifact. CHECKS.json records independent mpmath Dirichlet evaluations, functional equation checks and numerical derivative diagnostics.

The exterior exclusion is analytic: |a(n)|<=1, so for sigma>=2, |D(s)-1|<=zeta(2)-1<1. The functional equation excludes completed zeros for sigma<=-1. The separate thin rectangle [-1,2]+i[-.001,.001] has winding0, numerically checking the omitted very low heights. The remaining completeness limitation is the discrete boundary winding: no interval enclosure of the whole contour or rigorous boundary-zero exclusion was constructed.

For the parent's cutoff scan, Omega_300=330.4746631782259 has240 listed positive-height zeros below it. The301st upper zero is a critical-line root at397.13952267410658225538, so the600-height census covers the full-rank counting thresholds needed through m300. Rank itself is a separate matrix question.

Reproduce with `python extend.py`, then `python fine_line_check.py`, then `python checks.py`, then `python refine_200.py`. python-flint0.9.0 and mpmath are required; FLINT_DEPS and DH_ZERO_INPUT override session dependency/input locations. The session resumed an initial unconstrained Newton search using two already found seeds; the published driver instead directly invokes the bounded continuation. No source operator or original table was changed.
