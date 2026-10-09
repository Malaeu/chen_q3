# Q7 poor frequencies — artificial label inflation test

The unresolved object is the exact signed poor-frequency correlation JP.20 in
`PROSHKA_VERDICT_JOINT_PRODUCT_PAIR_Q07.md`. Adding a label could in principle
make a character moment usable. This test asks whether a nonnegative monomial
lift can do that while keeping the canonical coefficient class and a common
integral row. It does not replace the original pair by arbitrary coefficients.

## Exact entrance and already checked facts

Consider the necessary entrance g=d=e=a=1, after the exact Gauss-sign transport
and complete coprimality inversion JP.8. For q_s~S, X=L/S, the actual columns are

    A(h;s) = X^(-1/2) sum_(n sf,good) a0(n) nu_*(n)
             chi_n(h) chi_n(s)^4 V(q_n/X),
    a0(n)=conjugate(alpha(n)) gamma2(n),
    0<q_h<=K,  K=C_W L² U^(-1+zeta),  zeta=1/200.

The summand still has mu(s)/q_s and the real coupled profiles before the
positive separation. Here we test a proposed canonical entrance only; no
claim that this particular g,a,d,e branch must itself satisfy the final bound.
All actual rows and the remaining outer sums remain obligations in JP.20.

Pinned source K is `lem:canonical-moment`, lines9296–9340, SHA256
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Its raw bound is XB², with
unit-puncture necessity 1<=XB/K_row * U^(-c*), c*>0. The source also requires
a fixed ray character supported in fixed S, no free column coefficient, and
one common row variable independent of the columns. Q7 checked only the
mapping and keeps the analytic source lemma conditional.

## A1. The mask cannot be suppressed

Let f be squarefree good, (s,f)=1. On every column, including all zero cases,

    chi_n(h f²) chi_n(sf)^4
       = chi_n(h) chi_n(s)^4 1_(n,f)=1.

This follows from multiplicativity and chi_n(f)^6=1_(n,f)=1. Thus introducing
an arbitrary f produces the polynomial with its f-divisible columns removed;
it does not reproduce A(h;s). A concrete negative control is n=f=p at a good
prime, h=s=1: the original character factor is 1, the lifted factor is 0.
Averaging over f creates a column-dependent coprimality frequency, not a
constant. In a pair it creates a factor depending on both columns. Its exact
recovery or error needs a separate proof, which is not supplied by K.

## A2. Even free mask recovery does not fix the domain

Restrict to the deliberately narrow class of common integral monomial lifts

    h -> h f^j,   s -> sf,   j>=0,

with the same coefficient a0(n)nu_*(n). On nonzero sextic values the character
identity requires j+4=0 modulo6. For the full sextic coefficient class the
smallest possible j is2; all others are2+6t, t>=0. This algebraic necessity is
not inferred by pretending the character is cubic. Its zero extension still
has the mask in A1.

For q_f~F>=1, the canonical label has B~SF while the expanded unrestricted
row range has K_row~K F^j. The product X B~L F, so, writing ell=log_U L,
phi=log_U F>=0,

    log_U(XB/K_row) = 1-ell-zeta+(1-j)phi + O(1/log U).

Throughout the original band ell>=28/25-1/100=1.11. Already at F=1 the first
canonical condition fails; any polynomially large F and j>=2 worsen it.
No choice of positive c* works for all sufficiently large U. Fixed dyadic
constants cannot repair this strict negative exponent. The s scale cancels
exactly, so using many common divisors does not improve the entrance either.
This holds even if all mask-recovery and label-multiplicity costs are granted
for free. Actual costs can only add obligations.

This excludes this monomial route into this version of K, not a more refined
estimate on the sparse occupied rows h f^j. Such an estimate would be a new
analytic input; sparsity alone does not make the existing lemma applicable.

## A3. Why the two apparent shortcuts are different problems

* The rational lift h/f^4 gives the correct size improvement only when f^4
  actually divides h. That is exactly Q7's already bounded rich sector.
  A poor fourth-power-free h has no such nonunit divisor.
* Using h f^(-4) modulo a column modulus requires a unit and gives a row
  representative depending on n (or on both n,m for the pair). K averages
  one shared integral row before forming the polynomial square. Substituting
  those different representatives does not instantiate its stated family.
  A new completion or reciprocity theorem with all costs might do something;
  the bare modular identity does not supply it.

Independent read-only audit `mobius_short_transfer`: **PASS** on A1–A3.
It checked the zero extension, full sextic exponent congruence, source K
parameter map and first-domain failure (gap at most -0.115+o(1)).
This is a proof of failure of the stated entrance, not an analytic estimate.

## Alias return

UNVERIFIED search hints were conductor lowering by multiplicative modulation,
Burgess shift averaging, and metaplectic character large-sieve amplification.
The required invariant is joint coefficient and row preservation, including
zero masks and both profiles; a method name alone is insufficient.

Three actual `ask.sh --defer-external` queries are preserved in
`Q07_ARTIFICIAL_LABEL_ALIAS_RECEIPTS.json`. Each returned ASK_STATUS INCOMPLETE
because q3_docs freshness validation failed, with external Lean deferred.
This is not evidence of absent literature.

Verified discovery / **partial analogue, excluded as a direct supplier**:
J. Bourgain and M. Chang, *On a multilinear character sum of Burgess*,
January20,2010, [primary PDF](https://math.ucr.edu/~mcc/paper/138%20BurgessJB.pdf),
9 pages, SHA256 `02cac4cd28077402df1214233d4ab7ec116896befce941683d1ddcebaba743d7`.
Agent fetched `/tmp/Bourgain-Chang-Burgess-multilinear.pdf`; root checked its
hash and directly read the primary theorem/proof entrance through the web.
Exact quote, PDF p.2 Theorem(0.3): “Assume H > p^(1/4+epsilon). Then”
(the displayed inequality is |S|<p^(-delta)H^n).
The object is a box sum of one fixed nontrivial character modulo a prime,
applied to a product of independent linear forms. Section1, p.3,
equations(1.2)–(1.5), shifts x to x+ty and uses multiplicative energy of ratios;
the following lattice argument supplies that energy estimate.

Mapping failure: shifting our column n changes both a0(n) and the character
modulus. Fixing n instead leaves a generally composite Eisenstein modulus,
radial rows and the actual coupled signed average. Reciprocity does not remove
a0, squarefree/zero masks or the two profiles. The theorem does not contain a
uniform estimate for those weighted sums or their shift differences. These
are OPEN bridges, not a contradiction of Burgess. The full sextic local zero
control in A1 remains valid and is not repaired by a method name.
`long_positive_alias` independently read this primary proof and reached the
same excluded-direct-supplier classification. No cubic-only or fixed-modulus
bound is imported into JP.20.

## Decision

Do not attempt to force poor frequencies into K by adding an artificial
nonnegative monomial label. For this monomial entrance the exact row cost defeats the domain before
any possible estimate. The unresolved signed JP.20 remains the target, and
must be attacked by a genuinely joint estimate or a proved new transfer.
RH/SP/MB34 and the source analytic premises remain open/conditional as before.
AUTOPSY: dropped=COUPLING; note=artificial fourth-power label requires at least a square frequency inflation and an extra zero mask; the existing canonical entrance becomes worse.
