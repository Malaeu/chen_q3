# Five concrete work items after the Poincare transfer test

Date: 2026-09-16. Base: `1112f4b07bb1cbedbf6abc18d92a44ac166c1dfa`.
STATUS: INDEPENDENTLY_REVIEWED_WORKITEM_RECONCILIATION_ONLY; exact scope and reviewed hash in the accompanying certificate.
Purpose: answer which existing constructions are worth a bounded next test.
Ranking is research judgment about readiness and source content, not a
probability of RH and not five new or already positive representations.
No new mathematical sign theorem, source-sign attempt, dispatch or goal.

The unchanged target is the complete theta V on every finite complex row
with nodes in I=(-log(2)/2,0). A candidate means a specified representation
plus a proposed missing sign mechanism. A general mechanism with no source
map is labelled construction-needed, not a built candidate.

## 1. Source renewal: compensate the averaged two-channel blocks

Existing object: the literal cutoff-aware fields F_(c,m) in the SIZEBIASCOMP
response §3 and §7, with the same moving conditional projection and physical
weight at each S_m. Equations (39)-(41) prove an absolutely convergent exact
telescope for V. Both mean and fluctuation channels and the boundary survive.

Input using the full source: T*=law T+H T*, independently on the right,
with density h^(-1/2)-1 for H on (0,1). This is the particular hyperbolic
law from the complete rates πn², not generic reflection symmetry. It supplies
the 1/6 and 1/15 moment factors; actual cutoff error has nonzero 6^(-m)
leading order. No new direct prime-factorization lemma is used here.

Proposed mechanism, UNVERIFIED: derive one source-dependent comparison for
averaged blocks of the two channels, retaining the trace. §11 gives an exact
martingale alternative: level increments are orthogonal across levels, but
their internal form uses J(a,b)=(b,a) and is signed. That orthogonality is
available; positivity inside a level is not.

First bounded test, specified before evaluation: group the FIRST TWO renewal
increments, starting from E_0=0. For independent T_1,T_2 with the full source
law and H with the law above, set S_2=T_1+H T_2. In the notation of §9,

 K_2(x,y)=E[1_(S_2>=1) psi_xy(S_2)]
        =psi_xy(1) P(S_2>=1)
          +integral_1^infinity P(S_2>=t) psi_xy'(t)dt.

The second equality is the same finite bulk/trace identity, now with S_2;
the bounded derivative and integrable survival tail justify Fubini. This
is exactly the sum of the first two expected original telescope increments,
not a new source substituted into V. Check a two-node K_2 diagonal and
determinant analytically first. A negative result rejects this proposed
two-step positive-block rule only. A positive result is only a necessary
check; arbitrary ranks and the remaining blocks would still need one common
rule. No sign of K_2 is asserted here. Simply restating the terminal
bulk/trace inequality (43) supplies no new hypothesis.

Do not repeat: almost-sure positive increments (already false); absent trace;
full-field 15^(-m); positivity from summability or from martingale orthogonality.
Priority 1: source-specific law and the entire target are already on one
space. This does not mean its missing sign is known to be easier.

## 2. Coupled full-source ladder: use an equation linking the channels

Existing object: REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION, L11,
the U_(alpha,k)(X) fields for alpha=2,4,... built from full convolution powers
r_alpha and the same finite coefficients. The exact ladder is

 alpha(alpha+1)U_(alpha+2,k)
 =[(partial_X+alpha+2k)^2-1/4]U_(alpha,k)
  -(alpha²π/2)(partial_X+2k-1/2)U_(alpha,k+1).

With E_c(k)=integral_0^infinity |U_(2,k)|², L12 gives
||Phi||_2² V[c]=-E_c'(0)/2. Source input: the complete sinh product over
πn² and the associated convolution recurrence. This is stronger structural
input than the first Dirichlet eigenvalue alone; a sign does not follow yet.

Proposed mechanism, UNVERIFIED: a common energy identity for the linked
channels proving the derivative sign AT k=0 with the exact X=0 traces.
First bounded test: the alpha=2,4 equations must exhibit a specified repeated
cancellation/weight rule. Calculate the uncancelled channel and all boundary
terms explicitly. If it merely asks for a new unknown sign at alpha=6, no
reduction is established; adding more levels is not the default continuation.

Do not repeat: scalar homogeneous Sturm equation (forcing is nonzero and
the tested scalar energy is negative); raw all-k energy decay (false already
on one negative shift). Only the local derivative sign is required by L12.
Priority 2: exact source equations exist, but a positive coupled energy does not.

## 3. Original interaction operators: a sign condition for the actual pair

Existing object: HANKEL_JORDAN_PREFLIGHT H1-H5. Reflect nodes into
J=(0,log(2)/2). H_f has kernel f(x+t), H_g has kernel (x+t)f(x+t), and
V is the kernel of H_f H_g+H_g H_f. There is also an explicit positive
Gram kernel L(x,y)=V(x,y)/(x+y); exactly K=DL+LD on each node list.

Proposed mechanism, UNVERIFIED: a property of these actual source-built
operators or feature vectors that forces their symmetrized product positive.
First bounded test: state such a property in terms of f, not in terms of
the desired K>=0, and verify it against the known negative control f0.
Without a source condition or explicit common factorization, there is no
new sign candidate to test; merely renaming K as an operator is insufficient.

Do not repeat: positive L implies positive DL+LD (false), commuting shortcut
(the actual pair does not commute), or positive Hilbert-Schmidt operator
quadratic form implies preservation of positive matrices (different claims).
Source distinction still missing: this representation works for the negative
control too. Priority 3: compact exact object; no discriminating input supplied.

## 4. Fourier representation with the endpoint contribution retained

Existing object: INTEGRATED_SIGN_HUNT H9-H11. For the zero-extended half-line
profiles P_c,Q_c, V[c]=(1/pi)Re integral conjugate(hat P_c)hat Q_c. The
exact A_x,B_x include the node-dependent missing finite interval and
B_x=i partial_omega A_x+x A_x.

Proposed mechanism, UNVERIFIED: an augmented transform that retains the
boundary information and produces a nonnegative matrix energy. A source-built
transform and its finite or infinite channel space still need construction.
First bounded test: specify the additional channel, expand its kernel, and
check all off-diagonal coefficients against V. If a two-channel model closes,
then check its 2-by-2 spectral symbol; existence of such closure is not assumed.

Do not repeat: a common scalar B_x=m(omega)A_x (false even for Gaussian f),
or omission of the cutoff term. Generic Fourier identities use no special
property of primes. Priority 4: exact transform available, positive map absent.

## 5. Pairwise difference energy on a new field

Existing mechanism only: INTEGRATED_SIGN_HUNT H7, the nonlocal ground-state
identity from Frank--Seiringer. It expresses an energy minus its matched
potential as integral integral omega(r)omega(s)k(r,s)|v(r)-v(s)|², k>=0.
No such source-defined k,omega and c->v map giving our full V has been built.

Proposed mechanism, UNVERIFIED: combine a source-built difference energy with
the independently accounted mean/boundary part, and prove exact equality or
a sufficient lower comparison to V. The kernel and map must be explicit
before this can be called a constructed theta candidate.
First bounded test: source equation, limiting zero-shift row, then the full
two-node identity. A map losing the means fails the zero-shift equality test;
passing it remains only necessary. Reject a kernel defined using an assumed
positive square root of V. Generic ground-state algebra has no prime-specific
input; the required distinguishing source property is still unprovided.
Priority 5: a verified general compensation method, with the source map unpaid.

## Decision and scope

Use 1 first for one explicitly written block comparison; keep 2 as the next
source-specific option if 1 gives no new sign premise. This is a recommendation
and a test specification, not a report that the block inequality was tried
or proved. Items 3-5 are conditional reserves, not equally prepared candidates.
Do not run five open-ended proof tasks. The user's Poincare-only fluctuation
candidate is already diagnosed; improving its constant is not a sixth route.

The required invariant for every item remains the entire original V or a
proved sufficient implication to the original RH criterion. An invertible
change of coordinates can expose a sign but cannot erase a negative direction.

## Evidence and search status

This is reconciliation of project reports and existing mechanism cards. No
new literature-discovery claim or exact-fit admission is made. The existing
INTEGRATED_SIGN_HUNT brief and its recorded three shelf queries were reused;
their INCOMPLETE freshness status remains unchanged. New mgrep retrieval
failed with authentication and exhausted-credit errors. No alternative search
tool, new paid search, index repair or absence claim was used.

Known source locators read directly:

- PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md, §§3,7-11;
  exact full-field identity, correction rates, and explicitly signed J.
- REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md, L1-L20, plus its
  independent certificate; Pitman--Yor Theorem1(ii) and Proposition12(iv)
  were already source-locked in that report, not newly discovered here.
- REPORT_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md, H1-H6 and certificate.
- REPORT_2026-09-15_INTEGRATED_SIGN_HUNT.md, §§3-6 and its saved brief;
  existing source quotes/hashes and theta/control mappings reused.
- REPORT_2026-09-16_POINCARE_TRANSFER_PREFLIGHT.md, P1-P5.

Independent checking of this comparison does not prove any missing sign.
