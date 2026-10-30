# Alias return: negative spectral escape and uniform semiboundedness

Status: NO_TRANSFER in this bounded pass; no literature-absence claim.
The finite cutoff test increased energy; LOCALIZE's selected E+F_far bound
remains open. A spectral route must exclude negative exact bottom states,
including eigenvalues escaping to minus infinity, rather than merely control
near-zero radical quasimodes. The accompanying CONSTANT_FLOOR_REDUCTION
proves conditionally that an off-critical zero forces precisely that divergence.

Target on original real even V_m, N=m, L=log(m): a finite C independent of m
with k_m[v]>=-C||v||² for every v in V_m on an unbounded set of m.
The full source, pole, prime powers, Gram norm and return remain fixed.
NOESCAPE L1,L4 supply dense fixed near-null jets and strong-resolvent limit0;
CONFINE (4.5) supplies fixed negative-test energy return under an off-critical
zero. Neither is a lower bound. Actual radical trials have energy/residual→0;
under the contrary zero hypothesis their excess above the exact bottom→infinity.

Search dictionaries: negative spectral pollution / collective compactness;
discrete compactness / Galerkin spectral exactness; Gårding lower bound /
high-frequency coercivity of source Weil forms. Search-hint rewrites were
UNVERIFIED hypotheses, not admitted replacements for the source estimate.
Three sequential ask.sh --deep --defer-external queries ended INCOMPLETE:
q3_docs freshness validation failed. Exact local files below were nevertheless
read directly. No repeated global search or claim of shelf absence is made.

## The worked primary estimate and its actual cost

H. Yoshida, On Hermitian Forms attached to Zeta Functions, Adv. Stud. Pure
Math.21 (1992), pp.281–325; DOI https://doi.org/10.2969/aspm/02110281.
Local PDF: ../litreview/pdfs/yoshida_hermitian_forms_1992.pdf.
SHA256 aa1d3d5c0af8124d0ad38ceaacac0574e338f983d91cb5e6541d21f591c5e82b.
Root independently read pp.287–291 and visually checked p.287 after text
extraction; the DOI fetch failed, but the local primary PDF is present.

Lemma3 is on p.290, its proof ends p.291. Quote from its conclusion:
"Choosing N sufficiently large, we get" the prescribed coercive bound.
For fixed a0>0 and mu>0 it supplies an N such that q_a[phi]>=mu||phi||²
for phi orthogonal to modes |n|<=N, uniformly only over 0<a<=a0.

The proof uses (2.4), p.288: a positive archimedean large-frequency term,
a low-frequency Fourier integral as a negative remainder, and costs
C1(a), C2(a). Integration by parts on the high Fourier tail bounds the
low-frequency transform by a constant times sum_(|n|>N)1/n²; for fixed a0
this tends to zero, proving the result. This is the worked absorption step.

The definitions on p.287 are

 C1(a)=integral_(-2a)^(2a)(exp(x/2)+exp(-x/2))dx=8sinh(a),
 C2(a)=#{(prime ideal p,k): k log N(p)<=2a}.

The initial research extraction incorrectly divided C1 by 2a. Root's visual
check corrected that error; the published quantity is NOT 4sinh(a)/a.
With a=L/2=log(m)/2, C1=4(sqrt(m)-1/sqrt(m)). In the rational field,
C2 counts every prime power up to m and also grows. Applying Plancherel to
(2.4) yields a lower bound with cost C1(a)+2C2(a)+a field-dependent constant,
not a uniform constant as a→infinity. The even positive pole could be retained
instead of charged absolutely, but no required signed prime/pole compensation
is proved by this quoted estimate.

Mapping: a=L/2 and Yoshida's normalized modes exp(pi i n x/a)/sqrt(2a)
match the carrier modes up to the unit phase (-1)^n. Fixed-window domain and
normalization match; uniformity over growing a and all low carrier modes do
NOT. This is a verified partial source mechanism, not a CCM semibound supplier.

## Existing source Lean theorem: same uniformity obstruction

q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
SHA256 1a5d37851bd0092ad6e3c6942293900b71e7566be86d58ed36649a668c68665b.
The sourceWeilSesquilinearForm_re_self_lower_evenGraphFinsuppShift theorem
(starting line591) proves margin1/2 on a high even tail. Its displayed proof
absorbs ||W02_i|| and ||Prime_i|| separately. The cutoff R_i is per-index,
using L_i and a target including ||W02_i||+||Prime_i||+1, with exponential
frequency thresholds. No uniform R_i or R_i<=m on the literal diagonal, or
whole-carrier constant floor, is supplied. Exact finite-form crosswalks do
not remove these dependencies. Source read only; no fresh Lean build claimed.

## Spectral language does not remove the missing estimate

For z=i, strong-resolvent convergence to0 gives (Atilde_m-i)^(-1)→iI.
On lambda<=-a<0, |(lambda-i)^(-1)-i|=|lambda|/sqrt(1+lambda²)
>=a/sqrt(1+a²). Hence Q_m=1_(-infinity,-a](Atilde_m)→0 strongly.
If the images Q_m(unit ball) were collectively relatively compact, nonzero
unit q_m in ran Q_m would have a strongly convergent subsequence; strong
Q_m→0 makes q_m weak→0, contradicting unit norm. Thus collective compactness
would exclude that whole negative half-line eventually. Without a source
estimate proving compactness, this is only another formulation of the debt.
Excluding bounded negative spectral windows alone misses lambda_min→-infinity.

Osborn's fixed compact-operator spectral approximation theorem was a lead,
not an admitted supplier: no fixed compact operator / collectively compact
approximation representing these moving source forms was identified. No
new theorem from that lead is used here.

Next bounded question: can the exact signed prime/pole combination in the
original form satisfy the constant-slack inequality in CONSTANT_FLOOR_REDUCTION,
without replacing the window-dependent terms by unsigned norms? A bound growing
with m, fixed-window coercivity, or compactness asserted without a source proof
will not answer it. No RH claim or cutoff mechanism kill follows from this pass.
