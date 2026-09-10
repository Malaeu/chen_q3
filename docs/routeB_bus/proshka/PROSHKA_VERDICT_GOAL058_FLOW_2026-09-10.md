# STATUS: TRY_FLOW_CUT_PRICE_AND_DYADIC_TAIL_REPAIR
```yaml
OPERATIVE_CLASS: TRY_FLOW_CUT_PRICE_AND_DYADIC_TAIL_REPAIR
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-FLOW
BOUNDARY_ID: GOAL058_FULL_SOURCE_LOCATION_DEPENDENT_PATH_ALLOCATION
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
CENTRAL_SUPPLIER_VERIFIED: false
CENTRAL_PUSHFORWARD_IDENTITY_VERIFIED: true
CENTRAL_NUMERICAL_CERTIFICATE_FULL_RECHECK: NOT_COMPLETED
NEW_SOURCE_ALLOCATION_PROVED: true
EXACT_PAID_DOMAIN: >-
  {t in I, abs(x+t/2)>=11/4}
  UNION {t in (tau,infinity) outside I,
  x>=t+4 OR x+t<=-t-4}; I=[log(7/5),log(8/5)].
NEW_ALLOCATION_SCOPE: EXACT_PAID_DOMAIN_ONLY_NOT_ALL_RESIDUAL_DEMAND
NEW_ALLOCATION_USES_CENTRAL_CERTIFICATE_AS_PREMISE: false
GLOBAL_REMAINDER_PAID: false
LOWER_SIGN_PROVED: false
CONTINUOUS_ONLY_ALL_PATHS_OBSTRUCTION_PROVED: true
INDEPENDENT_CHECK_OF_NEW_PROOFS: PENDING
LEAN_VERIFIED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_LOCK:
  COMMIT: 4695e21604af1fbe721cd6670707ff109c4352b9
  BLOB: 6f03d3ad67ad598ed8b4b849dbf16d2556da93e2
  SHA256: 86ef6fb572406321d0fd1c628501787b43bb76014b7d97f3c1f06ef3ebe9a25e
  BYTES: 15250
  LINES: 81
  FINAL_LF: true
  LOCAL_BYTES_AND_BOTH_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: a05a3b6d333b9fdabb04d49cd5c963a31084b173
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SHELF_CHECKS:
  PINNED_BLOB_METADATA_MATCHES: 4
  FULL_SHA256_AND_BLOB_RECOMPUTATIONS: 1
  FULL_RECOMPUTED_FILE: docs/BATCH_PATTERNS.md
  FULL_BUNDLE_HASH_AND_16_EMBEDDED_HASHES: NOT_COMPLETED
  CENTRAL_2493_REGION_COVERAGE_REPLAY: NOT_COMPLETED
FIRST_FAILURE:
  Q1: independent_authentication_and_complete_coverage_check_of_D23_not_completed
  Q2_INITIAL: continuous_only_cut_demand_at_Y_3_exceeds_twice_available_capacity
  Q2_AFTER_REPAIR: no_allocation_or_signed_comparison_for_Lambda_in_F22_has_been_proved
  Q3: F24_remaining_signed_domination_unproved
PREDICTION_FATES:
  P1: UNRESOLVED
  P2: UNRESOLVED
  P3: CONFIRMED
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
EXECUTION:
  NEW_SOURCE_NUMERICAL_CAMPAIGN: false
  OLD_ADAPTIVE_SEARCH_RERUN: false
  EXACT_RATIONAL_CHECKS: true
  LEAN_EDIT_OR_GATE: false
  OLD_VERDICT_QUEUE_REGISTRY_OR_RH_EDIT: false
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FLOW_2026-09-10.md
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  BRANCH: rh_clean
  FINAL_HASHES_COMMIT_AND_PUSH_STATUS: EXTERNAL_DELIVERY_RECEIPT
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
```

## 0. Decision and source boundary

**There is a class-wide obstruction and a constructive repair, but not a global sign proof.** Every allocation using only positive continuous edges fails a necessary cut-capacity inequality for the actual theta source. The number of edges, their orientations, their location-dependent probabilities and their unequal coefficients are unrestricted in that refutation. A prime-assisted repair then pays the entire original interval I in both sufficiently remote physical tails, plus an unbounded two-sided wedge for every other negative length. Its total receiving load is less than 1/16 of the available full positive resource on its support. [COFINAL_FAMILY][PAPER]

The new support is disjoint from every receiving edge of the retained central construction. Thus this is additional supply, not a change of the central interval or radius, and not an unrecorded reuse of its resource. The central construction remains exactly D20-D23. Its pushforward identity is rederived below, but its complete numerical certificate was not independently authenticated and checked in this execution. Consequently `CENTRAL_SUPPLIER_VERIFIED` is false, not a claim that the central theorem is false. Composition with its reported capacity bound is explicitly conditional. [ABSTRACT][PAPER for support and algebra; CONDITIONAL for that certificate]

The new allocation theorem itself uses only the displayed theta series and elementary inequalities. It does not depend on the numerical central maximum, D24-D26's numerical witnesses, a zero-location assertion, an unknown eigenfunction, or a prime-number error estimate. Its independent paper review is pending. Publication does not constitute that review.

### 0.1 Exact source ledger

All shelf locators below use SOURCE_BASE from the header. `BLOB MATCH` means the connector returned the requested object identifier. It is not a fresh computation of the complete SHA-256.

| Key | Path | Pinned SHA-256 | Pinned Git blob | Actual verification this batch |
|---|---|---|---|---|
| X | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md` | `93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9` | `136aceb3cbbabcdfa425459562b803b67c548b48` | BLOB MATCH; READ CAN, RAD, GS, DOM and their relevant proofs; complete 46207-byte rehash not completed |
| R | `docs/routeB_bus/BOUNDARY_INDEPENDENT_CHECK_2026-09-10.md` | `b30d024c5a7e73806653300ebf30b37b1718cb25fa00ae612bd44d3b1e6cd6c5` | `6f5ddbad0d91d3f4a8bb7e5734838b55f10a4226` | BLOB MATCH; READ relevant D14-D26 arguments, code and receipts in excerpts; complete 121953-byte rehash not completed |
| C | `docs/routeB_bus/phase5_codex/out/three_edge_central_20260910.json` | `c193163d562dfc5eedcc5a462932c879533364f52af86c9e47182c8d2f193db2` | `f18fc6d374a6dc891f488625035c79756318e999` | BLOB MATCH; READ schema, embedded source construction and evaluator excerpts; complete 708850-byte capture, embedded checks and cover replay not completed |
| P | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full; 11341 bytes, 79 LF; both hashes independently recomputed and MATCH |

The request was read completely from its local attachment and exact-commit connector response. Its computed Git blob, SHA-256, byte count and LF count all match the controlling instruction. The non-Route-B document opened was precisely `docs/BATCH_PATTERNS.md`, which the request explicitly includes.

Direct raw acquisition attempts did not produce a complete local certificate bundle: the container request encountered DNS failure, the download bridge failed, and a web opening of the exact raw locator returned 404. Connector reads still resolved the pinned objects. No missing bytes have been reconstructed from an earlier, different verdict. The historical external explicit-formula dependency behind X's RAD is identified there; no new external theorem or PDF is imported or claimed freshly read here.

## 1. Source, central construction and exact composition interface

All assertions in this section are [ABSTRACT][PAPER], except the explicitly marked numerical-certificate input.

Write p=log 2, t_-=log(7/5), t_+=log(8/5), I=[t_-,t_+], R=1/8, and n(t)=b_-(t). The source Phi, A, f0, alpha, c_A, w_n and the two pole moments are exactly those in the request and X. In particular Phi has coefficients 4 pi^2 and 6 pi, not the half-sized raw normalization of another batch. Define the unoriented receiving-edge space by (y,u), u>0, with endpoints y and y+u, and put

\[
c_u(y)=f_0(y)f_0(y+u),\qquad
\mathcal D_-(dx,dt)=\mathbf1_{t>\tau}n(t)c_t(x)\,dx\,dt,
\]
\[
\mathcal C_+(dy,du)=\mathbf1_{0<u<\tau}b(u)c_u(y)\,dy\,du
+\sum_{n\ge2}w_nc_{\log n}(y)\,dy\,\delta_{\log n}(du).
\tag{F1}
\]

For completeness, the literal source underlying these measures is

\[
\Phi(x)=e^{x/2}\sum_{k\ge1}(4\pi^2k^4e^{4x}-6\pi k^2e^{2x})
                         e^{-\pi k^2e^{2x}}\quad(x\ge0),
\qquad \Phi(-x)=\Phi(x),\quad f_0=\Phi/\|\Phi\|_2,
\]
\[
\begin{split}
Q(g)={}&\int_0^\infty\alpha(t)\|g(\cdot+t)-g\|_2^2dt-c_A\|g\|_2^2
+2\Re\big(M_+(g)\overline{M_-(g)}\big)\\
&-2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
             \Re\int_{\mathbb R}\overline{g(x)}g(x+\log n)dx,
\end{split}
\]

where alpha(t)=exp(-t/2)/(1-exp(-2t)), c_A=gamma+log(8pi)+pi/2, and M_+/-(g)=integral exp(+/-x/2)g(x)dx. Pairings are antilinear first. The source control domain is X={g: integral exp(2|x|)|g(x)|^2dx + D(g)<infinity}, with D the displayed translation energy. It is not replaced by H1_0 or a moment-null subspace.

The continuous and atomic measures are different resources. In particular the atom at log(2^k) has weight log(2)/2^(k/2), not k log(2)/2^(k/2).

For r in C+C_c^infinity, subtracting Re B(f0,f0|r|^2)=0 from Q(f0r) gives

\[
Q(f_0r)=\int |r(y+u)-r(y)|^2\,d\mathcal C_+
-\int |r(x+t)-r(x)|^2\,d\mathcal D_- .                 \tag{F2}
\]

For clarity, the algebra of this source transformation retains the poles. With P=f0(x), Q0=f0(x+t), z=r(x), w=r(x+t),

\[
|Q_0w-Pz|^2-(Q_0-P)(Q_0|w|^2-P|z|^2)=PQ_0|w-z|^2.
\]

The scalar diagonal cancels. The two pole correlations contribute -(e^(t/2)+e^(-t/2))c_t(x)|w-z|^2; the negative prime correlation contributes +w_n c_(log n)(x)|w-z|^2. Thus the continuous coefficient is exactly b=alpha-e^(-t/2)-e^(t/2). This rechecks GS from the stated radical identity, not from an assumed minimum. X's RAD proof uses its explicit-formula dependency; this batch does not replace that dependency by a numerical observation.

Near u=0 the squared difference is O(u^2), whereas b_+(u)=O(1/u). At large t a nonzero difference requires at least one endpoint in the fixed compact support of r minus its constant. The other theta factor decays faster than every exponential. These facts establish separate convergence of the continuous energies and the prime sum in F2. They apply to complex r without a parity restriction.

### 1.1 Recheck the central pushforward

Let j(u)=u^3 b_+(u) for u>0, zero otherwise, L=j*j and Z=j*j*j. We have 1/4<tau<log(4/3)<t_-. For t in I, t/3 is strictly inside (0,tau). Thus Z(t)>0, and compactness gives a positive minimum on I. The ordered probability density

\[
\frac{j(s_1)j(s_2)j(t-s_1-s_2)}{Z(t)}\,ds_1ds_2
\quad(s_1,s_2>0,\ s_1+s_2<t)                         \tag{F3}
\]

has total mass one. There is no 3! factor. Its three nonzero lengths lie in P almost surely. The path is x,x+s1,x+s1+s2,x+t. Per unit demand, take a_i=t/s_i. Then sum_i 1/a_i=1, and weighted Cauchy-Schwarz proves its inequality for all complex vertex values.

For the first edge use y=x,u=s1; for the last use y=x+t-u,u=s3; for the middle use y=x+v,u=s2,v=s1. Every inverse Jacobian is one. Since j(u)/(u b(u))=u^2, the central charge is exactly

\[
\begin{split}
\rho_c(y,u)=\frac{u^2}{c_u(y)}\int_I\frac{n(t)t}{Z(t)}
\bigg\{&L(t-u)\big[c_t(y)\mathbf1_{|y+t/2|\le R}
+c_t(y-t+u)\mathbf1_{|y-t/2+u|\le R}\big]\\
&+\int_0^{t-u}j(v)j(t-u-v)c_t(y-v)
                   \mathbf1_{|y-v+t/2|\le R}\,dv\bigg\}\,dt .
\end{split}                                                        \tag{F4}
\]

This formula is for 0<u<tau and is zero elsewhere. All paths stay between their demand endpoints. Consequently every central receiving edge has BOTH endpoints in [-H,H], where

\[
H=R+t_+/2<3/8.                                           \tag{F5}
\]

This support statement does not depend on a numerical maximum.

### 1.2 What is and is not verified about D23-D26

The reported D23 bound is the exact rational

\[
U_c=\frac{340263072827858175414912363711278527325}
          {340282366920938463463374607431768211456}<1,
\]

over 2493 regions, partitioned as 195+889+1409. The bundle and report describe interval theta/L/Z enclosures, support exclusions and the complete cover. I have not independently captured and hashed every embedded artifact or replayed this cover. Thus the inequality rho_c<=U_c remains a **reported certificate, not a newly verified supplier in this adjudication**. F3-F5 are proved here; the numerical premise is [FINITE_CELL][CONDITIONAL].

The narrow algebra behind D24-D26 survives inspection. For D24, (x,t) -> (x-iq,q), q=(p-t)/2, has inverse absolute Jacobian 2. For D25-D26, isolating a single short difference by vertex values forces its physical charge to be at least the negative-edge demand, independently of the prime charge. The two variable-short receiving maps have inverse Jacobian 1; reflection is (y,u) -> (-y-u,u). Hence changing only the charges cannot change their derived mandatory-load lower expression. The reported strict numerical witnesses are not rerun or silently upgraded here. Their complete dependency authentication remains unpaid alongside the central certificate.

**FIRST_FAILURE Q1:** full authentication and coverage verification of C, including the 16 embedded hashes and the 2493-region assertion, was not completed. No mathematical counterexample to F4 or D23 is claimed. In particular the central charges may not be discarded to improve a later budget.

Conditional on rho_c<=1, define

\[
\Gamma_c=\rho_c\mathbf1_P b(u)c_u(y)\,dy\,du,
\qquad \mathcal C_{\rm res}=\mathcal C_+-\Gamma_c\ge0.       \tag{F6}
\]

For any additional probability law on the remaining demand, valid path inequalities and its TOTAL charge Gamma<=C_res imply DOM by Tonelli. Repeated edge occurrences are summed with multiplicity. This is a sufficient interface; no continuum strong-duality theorem is asserted.

## 2. Elementary theta estimates used by the new construction

[COFINAL_FAMILY][PAPER]. These are direct estimates for the exact source, not a Gaussian replacement.

Set

\[
a_-=4\pi^2-6\pi>0,\qquad
 a_+=\frac{4\pi^2}{1-16e^{-3\pi}}.
\]

For every x>=0,

\[
a_-e^{9x/2-\pi e^{2x}}\le\Phi(x)
\le a_+e^{9x/2-\pi e^{2x}},\qquad a_+/a_-<4.             \tag{F7}
\]

For the lower bound keep the k=1 term and use e^(2x)>=1. For the upper bound drop the negative polynomial term. In the remaining positive sum the ratio of successive k^4 exp(-pi(k^2-1)e^(2x)) terms is at most 16 exp(-3 pi). The geometric sum proves the stated constant. Since pi>3, both 1-3/(2 pi) and 1-16 exp(-3 pi) exceed 1/2, proving a_+/a_-<4.

Every theta summand is decreasing for x>=1. Indeed, with z=pi k^2 e^(2x), its derivative is e^(x/2-z)(-8z^3+30z^2-15z), negative there. Normal convergence permits summation. Thus Phi is decreasing on [1,infinity).

The elementary inequalities e^4>50 and e^(2h)-1>=2h give, for y>=2 and h>=0,

\[
\frac{\Phi(y+h)}{\Phi(y)}
\le4\exp\{(9/2)h-\pi e^{2y}(e^{2h}-1)\}
\le4e^{-200h}.                                        \tag{F8}
\]

There is a useful uniform refinement: if y>=t+2 and t>=0, then

\[
\frac{\Phi(y+h)}{\Phi(y)}\le4e^{-(200+400t)h}.           \tag{F8a}
\]

In fact 2 pi e^(2y)-9/2 >=300e^(2t)-9/2 >=295.5+600t >=200+400t. No hidden t-dependent constant occurs.

Here are elementary parameter bounds used below. The function e^(3t)-e^t is strictly increasing for t>=0. Its value at log(4/3) is 28/27>1. At 1/4 it is less than (4/3)(5/3-1)=8/9, using e^(1/4)<4/3 and e^(1/2)<5/3. Hence 1/4<tau<log(4/3)<1/3. Also 2/3<p<7/10, t_+<1/2, log(5/4)>1/5, and log(8/7)<1/7. These follow from the integral for log and elementary exponential series bounds. In particular

\[
\epsilon_\theta:=4e^{-40}<1/1000.                       \tag{F8b}
\]

The inequalities e^3>20, e^4>50 and all later rational margins were also checked with exact rational partial sums/arithmetic. No source-energy floating-point computation enters the proofs.

## 3. A new class-wide obstruction: continuous-only paths cannot pay the tail

### 3.1 Price every short edge crossing a fixed cut

[ABSTRACT][PAPER]. This tests the first proposed global mechanism: extend positive-continuous path allocation to the residual demand, allowing arbitrary location-dependent finite paths, both orientations, arbitrary step counts and any valid nonnegative charges. No prime edge is allowed in this class.

Fix Y>=3. Give a positive continuous receiving edge the bounded price

\[
h_Y(y,u)=\mathbf1_{y<Y\le y+u},\qquad 0<u<\tau.
\]

A path joining x<Y to x+t>=Y must have priced charge at least one per unit demand. To prove this without any assumption about independent increments, assign each vertex the value 1 when it is at least Y and 0 otherwise. The path inequality itself gives

\[
1\le\sum_i a_i h_Y(y_i,u_i).                            \tag{F9}
\]

This handles repeated vertices as well. It is a finite-vertex test; no discontinuous step function is being admitted as an original Weil test. Any finite assignment on distinct vertices can also be realized by a compact smooth function.

Consequently every continuous-only allocation of even just the following residual I-demand must satisfy

\[
D_Y:=\int_I n(t)\int_{Y-t}^{Y}c_t(x)\,dx\,dt
\le C_Y:=\int_0^\tau b(u)\int_{Y-u}^{Y}c_u(y)\,dy\,du.  \tag{F10}
\]

The price has finite capacity: u b(u) is bounded near zero. C_Y is strictly positive. The crossing demand lies outside the central block. Granting it the ENTIRE positive continuous resource, rather than deducting Gamma_c, makes F10 weaker and therefore a valid necessary test.

More generally one may integrate any measurable lower bound for the per-path priced cost against the demand and compare with its finite priced capacity. That statement follows directly from nonnegative pushforwards and Tonelli. It requires neither an attained path-cost infimum nor finite-dimensional strong duality.

### 3.2 Strict violation from the literal theta source

[COFINAL_FAMILY][PAPER]. In fact

\[
\boxed{D_Y>2C_Y\quad\text{for every }Y\ge3.}             \tag{F11}
\]

Here is a proof with explicit constants. Put beta=log(4/3), alpha0=log(3/2), and epsilon=e^(-2Y)/100. Since tau<beta and Phi decreases at all arguments involved,

\[
C_Y\le\frac{4}{9A^2}\Phi(Y-\beta)\Phi(Y).              \tag{F12}
\]

Indeed u b(u)<=u alpha(u)<=4/3 for 0<u<tau<1, and tau<1/3. The alpha bound follows from concavity of 1-e^(-2u), which is at least 3u/4 on [0,1].

In D_Y retain t in [alpha0,t_+] and z=x+t in [Y,Y+epsilon]. This rectangle lies in the crossing domain. On it n(t)>=7/15, because e^t>=3/2 and e^(3t)-e^t>=15/8. Its t-length is log(16/15)>1/16. Monotonicity gives

\[
D_Y\ge\frac{7\epsilon}{240A^2}
       \Phi(Y+\epsilon-\alpha_0)\Phi(Y+\epsilon).        \tag{F13}
\]

To compare the products, F7 yields an exponential advantage. Its double-exponential exponent is

\[
\pi e^{2Y}\left[\frac{25}{16}-\frac{13}{9}e^{2\epsilon}\right]
\ge\frac{17\pi}{144}e^{2Y}-\frac{52\pi}{900}
>\frac{17}{48}e^{2Y}-1.
\]

Here e^(2epsilon)<=1+4epsilon, epsilon e^(2Y)=1/100 and pi<4 were used. The remaining linear exponential factor is at least (8/9)^(9/2)>1/2; the squared source-constant ratio exceeds 1/16. Combining F12-F13 and e^(-1)>1/4 therefore gives

\[
\frac{D_Y}{C_Y}>
\frac{\exp((17/48)e^{2Y})}{200000e^{2Y}}.                \tag{F14}
\]

The prefactor calculation uses 21/4096000>1/200000. Let z=e^(2Y). For Y>=3, z>400 because e^3>20. Keeping the fifth term of exp((17/48)z),

\[
\frac{e^{(17/48)z}}{200000z}
\ge\frac{(17/48)^5 z^4}{120\cdot200000}
>\frac{35496425}{5971968}>2.
\]

This proves F11. Thus the success margin has the strict negative upper envelope C_Y-D_Y<-C_Y<0. It excludes the ENTIRE continuous-only path class, not merely a fixed-length or fixed-density law. The infimum in the cut-price argument cannot be reduced by taking more short steps or by changing the probability kernel.

**Scope of refutation:** THEOREM_SHAPE, namely a continuous-only nonnegative path allocation paying all residual demand (indeed, paying this I-tail submeasure is already impossible). It is not ROUTE_FAMILY death and is not negative Q. The omitted positive prime resource is exactly why the latter inference would be invalid. Allowing a prime edge crossing the cut removes the premise of F9 with this price.

## 4. Concrete repair on the unchanged I: location-gated three-edge prime paths

[COFINAL_FAMILY][PAPER]. Put M_*=11/4 and

\[
\Omega_3^+=\{(x,t):t\in I,\ x+t/2\ge M_*\},\quad
\Omega_3^-=\{(x,t):t\in I,\ x+t/2\le-M_*\}.
\]

For a right-tail demand set q=(p-t)/2 and use the deterministic probability-one path

\[
x,\quad x-q,\quad x-2q,\quad x+t,                     \tag{F15}
\]

with per-unit-demand coefficients 3,3,3. All three vertices are distinct, both short lengths q lie in P, and the last length is p. Cauchy-Schwarz gives the complex path inequality because the three reciprocal coefficients sum to one. The law does NOT act at the old central join. For the left tail reflect and reverse the path; its nodes are x,x+p,x+p-q,x+t, again with coefficients 3.

Let J=[q_-,q_+]=[log(5/4)/2,log(10/7)/2]. For u in J write t=p-2u. If gamma denotes the physical receiving density, the EXACT right-tail short charge is

\[
\gamma^+_{3,c}(y,u)=6\mathbf1_J(u)n(t)
\sum_{i=1}^{2}c_t(y+iu)\mathbf1_{\Omega_3^+}(y+iu,t).     \tag{F16}
\]

The factor 6 is 3 times the inverse Jacobian 2. The exact prime charge is

\[
\gamma^+_{3,2}(y)=3f_0(y+p)\int_I n(t)f_0(y+p-t)
        \mathbf1_{\Omega_3^+}(y+p-t,t)\,dt.              \tag{F17}
\]

There is no prime-length Jacobian factor: (x,t) -> (y=x-p+t,t) has determinant one. Other prime densities in this piece are zero. Define the left charges by pushing F16-F17 through (y,u) -> (-y-u,u). Reflection of the demand has determinant one, and f0 is even. No parity of r is assumed.

Every vertex of a right-tail path is greater than 2, since its minimum is x-2q=x+t/2-p+t/2>=11/4-p>2. All left-tail vertices are less than -2. These are disjoint receiving supports and are disjoint from F5.

For u in J, writing v=e^u<=sqrt(10/7)<6/5 gives v^3-v<=18/35. Hence b(u)>17/18. Also n(t)<4/3 on I, w2>4/9 and |I|<1/7. In the first short occurrence the normalized theta ratio is Phi(y+p-u)/Phi(y). In the second it is

\[
\frac{\Phi(y+2u)\Phi(y+p)}{\Phi(y)\Phi(y+u)}
\le\frac{\Phi(y+p)}{\Phi(y)}.
\]

For each active occurrence y>=2, and every displayed shift is at least log(5/4). F8-F8b bound these ratios by epsilon_theta<1/1000. The prime ratio in F17 is Phi(y+p-t)/Phi(y) and has the same bound. Therefore, for the complete densities including reflection,

\[
\frac{\gamma_{3,c}}{b(u)c_u(y)}
<\frac{288}{17}\epsilon_\theta<\frac1{32},\qquad
\frac{\gamma_{3,2}}{w_2c_p(y)}
<\frac97\epsilon_\theta<\frac1{32}.                    \tag{F18}
\]

No factor two is lost in adding the reflection: its receiving support is disjoint. These are whole-domain density bounds, not sampled resistances. They pay the entire I-demand on Omega3+ union Omega3- with the exact original f0 and prime weight.

This repair also pays the actual demand used in the failed cut test at Y=3. Its midpoint lies between 3-t/2 and 3+t/2, and 3-t_+/2>11/4. The prime edge crosses that cut; the continuous-only lower price F9 is therefore no longer mandatory. The failed class and its repair concern the same source demand, not unrelated examples.

## 5. A second paid region: all other negative lengths, including arbitrarily large t

[COFINAL_FAMILY][PAPER]. The following explicit law uses only powers of the prime 2, but retains all other primes as unused resource. It is not proposed on the whole middle region.

For t in N outside I let

\[
k(t)=\lfloor t/p\rfloor+2,\quad
\ell_k=kp,\quad d_t=kp-t\in(p,2p],\quad u_t=d_t/8.
\]

Then k>=2, p/8<u_t<=p/4<tau. On

\[
\Omega_9^+=\{t\in N\setminus I,\ x\ge t+4\}
\]

use eight inward short edges followed by one prime-power edge:

\[
x_i=x-iu_t\ (0\le i\le8),\qquad x_9=x+t.              \tag{F19}
\]

The final length is kp=log(2^k). Give ALL nine differences coefficient 9 per unit demand. Thus the path inequality holds for every complex assignment, with reciprocal sum one. This is a measurable deterministic probability kernel. At the countable bin boundaries the floor defines the choice; no source mass is lost. Reflect and reverse for

\[
\Omega_9^-=\{t\in N\setminus I,\ x+t\le-t-4\}.
\]

### 5.1 All short-edge preimages and their summable load

Write J_k=[(k-2)p,(k-1)p). For p/8<u<=p/4 set t_k=kp-8u. Its right-tail receiving density is exactly

\[
\gamma^+_{9,c}(y,u)=72\mathbf1_{(p/8,p/4]}(u)
\sum_{\substack{k\ge2\\t_k>\tau,\ t_k\notin I}}n(t_k)
\sum_{i=1}^{8}c_{t_k}(y+iu)
                \mathbf1_{y+iu\ge t_k+4}.               \tag{F20}
\]

For each occurrence the inverse map is t=kp-8u, x=y+iu and its absolute Jacobian is 8, giving 72=9 times 8. The sum includes every branch and every short occurrence. On bounded receiving sets only finitely many k are active, but the following estimate also bounds the entire infinite sum uniformly.

An active occurrence has y>=t+4-8u>=t+4-2p>t+2. In particular all right-tail vertices exceed 2. Monotonicity and F8 give

\[
\frac{c_t(y+iu)}{c_u(y)}
\le\frac{\Phi(y+u+t)}{\Phi(y)}\le4e^{-200(t+u)}.
\]

We have b(u)>1/2 on this u-range: p/4<q_+ and the bound preceding F18 applies. Since n(t)<=e^(t/2), the full normalized short load is at most

\[
4608e^{-200u}\sum_{t_k>\tau}e^{-(399/2)t_k}
<9216e^{-49}<\frac1{32}.                               \tag{F20a}
\]

The t_k are p-spaced. The first retained t_k exceeds tau>1/4, and the geometric ratio e^(-(399/2)p) is less than 1/2. Dropping the restriction t_k outside I only enlarges this safe bound. The final rational check uses e>2 and 9216/2^49<1/32.

### 5.2 The entire prime-power load, with the correct source weights

For each k>=2 the exact right-tail density at log(2^k) is

\[
\gamma^+_{9,2^k}(y)=9f_0(y+kp)
\int_{J_k\cap(N\setminus I)}n(t)f_0(y+kp-t)
                   \mathbf1_{y+kp-t\ge t+4}\,dt .        \tag{F21}
\]

The coordinate map x=y+kp-t has determinant one. Divide by w_(2^k)c_(kp)(y), with w_(2^k)=p e^(-kp/2). For an active t, y>=t+2 and d_t>=p. F8a therefore gives

\[
\frac{n(t)}{w_{2^k}}\frac{\Phi(y+d_t)}{\Phi(y)}
\le\frac{8}{p}\exp\{-400/3-(797/3)t\}.
\]

Indeed n(t)/w_(2^k)<=e^(t+d_t/2)/p<=2e^t/p, while d_t>=p>2/3. Multiplying by the path coefficient 9 and integrating over a set of length at most p proves

\[
\frac{\gamma_{9,2^k}}{w_{2^k}c_{kp}(y)}
\le72e^{-400/3}<72e^{-100}<\frac1{32}
\quad\text{for EVERY }k\ge2.                            \tag{F21a}
\]

Again reflection does not double the bound, because its endpoints are below -2. This is a uniform bound for each distinct atom, not an inappropriate summation of different prime resources into one density. Tonelli handles their countable union. The infinitely many other prime atoms remain unchanged.

## 6. Exact paid domain, residual measures and the original all-test conclusion

[COFINAL_FAMILY][PAPER for the new allocation and identities; CONDITIONAL where the central capacity bound or the remaining domination is invoked].

Let

\[
\Omega_e=\Omega_3^+\cup\Omega_3^-\cup\Omega_9^+\cup\Omega_9^-,
\quad \Omega_c=\{t\in I,\ |x+t/2|\le R\}.
\]

These source sets are disjoint. The complete unpaid domain is

\[
\boxed{
\Lambda=
\{t\in I,\ R<|x+t/2|<11/4\}
\ \cup\
\{t>\tau,\ t\notin I,\ -2t-4<x<t+4\}.}                 \tag{F22}
\]

The definitions assign all boundaries consistently; changes on their null sets do not affect the measures. In particular the second component is unbounded in t and x. Nothing outside I is silently paid by the central theorem.

Let U be the receiving set with both endpoints in [2,infinity) or both in (-infinity,-2]. Put Gamma_e=Gamma_3+Gamma_9, using the exact densities F16-F17 and F20-F21 and their reflected copies. The two short loads may overlap, and are added, not declared orthogonal. Their sum is less than 1/16 of the continuous capacity. Their prime supports are different: n=2 for Gamma3, n=2^k with k>=2 for Gamma9. Thus

\[
\boxed{0\le\Gamma_e\le\tfrac1{16}\mathbf1_U\mathcal C_+.}
                                                               \tag{F23}
\]

This is the NEW unconditional source-allocation theorem. For every complex r in C+C_c^infinity it implies

\[
\int_{\Omega_e}n(t)c_t(x)|r(x+t)-r(x)|^2dxdt
\le\int |r(y+u)-r(y)|^2d\Gamma_e
\le\tfrac1{16}\int_U|r(y+u)-r(y)|^2d\mathcal C_+.
\]

It does not use the certificate U_c. F5 proves Gamma_c has no support in U, so on the support actually used by the new law the original residual resource equals the full resource exactly. Conditional on the reported central capacity inequality, the two allocations compose without interference and leave a nonnegative measure

\[
\mathcal C_{\rm new}=\mathcal C_+-\Gamma_c-\Gamma_e.
\]

On U this measure retains at least 15/16 of the continuous resource and at least that fraction of every prime resource. Away from U it retains the exact central residual, not a uniform fictional reserve 1-U_c over resources that were never used.

### 6.1 Exact unpaid signed form

Define nonnegative path slacks

\[
S_c[r]=\int|\Delta r|^2d\Gamma_c-\int_{\Omega_c}|\Delta r|^2d\mathcal D_-,
\qquad
S_e[r]=\int|\Delta r|^2d\Gamma_e-\int_{\Omega_e}|\Delta r|^2d\mathcal D_-.
\]

The central path slack is nonnegative by F3 even before verifying its resource ceiling. Its total charged mass is finite on the compact central source domain, since j(u)/u is integrable and Z is bounded away from zero. The extra slack is finite by F23 and the already established convergence of the positive energy. Hence there is no subtraction of divergent energies in

\[
\boxed{Q(f_0r)=S_c[r]+S_e[r]+\int|\Delta r|^2d\mathcal C_{\rm new}
                         -\int_\Lambda|\Delta r|^2d\mathcal D_-.}   \tag{F24}
\]

If the central ceiling is not supplied, C_new is read as the displayed signed difference; its weighted integral remains well defined. If that ceiling is supplied, C_new is a genuine positive measure. No part of the prime sum, either pole contribution in b, or mixed source weight has disappeared.

A sufficient remaining theorem is to allocate D_- restricted to Lambda from C_new, or to prove directly that the last positive integral in F24 dominates its negative one for every original compact smooth r. Neither has been proved. The slacks may also be exploited by a different signed proof; dropping these nonnegative slacks is a sufficient, not necessary, interface.

**FIRST_FAILURE Q2 after repair:** there is no established allocation or signed lower comparison for the explicit Lambda and C_new in F22-F24. In particular the near-join region R<|x+t/2|<11/4 was never licensed by the far-tail estimate y>=2. Extending F18 there would be an invalid use of F8. A location-dependent middle allocation must still pay its shared receiving capacity.

### 6.2 Measure, test-class and terminal transfer

Every new source responsibility is one, not a reweighted fraction: a deterministic law is used on each of the disjoint new regions. The central responsibility is the normalized probability F3. All maps are Borel, and every path is finite. Countable k-branches, both reflections, all receiving preimages and repeated edge occurrences have been included explicitly. Nonnegative Tonelli, or first truncation in source/edge domains followed by monotone convergence, justifies the passage from path inequalities to F23.

If an independently proved remaining allocation Gamma_Lambda<=C_new were supplied, adding its path inequality, F3 and F23 would give DOM for every compact smooth complex r. For every original complex g in C_c^infinity, f0>0 and smooth imply r=g/f0 is again compact smooth. F2 would then give Q[g]>=0 on the unchanged class, reaching the stated Weil consumer. No ground-state, parity, finite-window approximation or cofinal-rate premise is added to this implication.

**FIRST_FAILURE Q3:** the remaining comparison in F24, and this execution's incomplete independent authentication of the central ceiling, prevent an unconditional all-test conclusion. Neither lower sign nor RH is claimed. The new tail theorem is still unconditional and is not weakened by those separate missing inputs.

## 7. Adversarial controls, one next decisive test and its stopping rule

### 7.1 Required three-vertex control

[ABSTRACT][PAPER]. On the two unit positive edges 01 and 12 with negative demand d on 02, the test (0,1/2,1) has energy 1/2-d. Thus d=1/4,1/2,3/4 give 1/4,0,-1/4. Constants are radical in all three cases.

A valid two-edge path has 1/a1+1/a2<=1 and consequently a1+a2>=4. Price one on both positive edges therefore gives mandatory cost 4d against capacity 2. At d=3/4 the strict violation is 3>2. At d=1/2 equality is allowed: a1=a2=2 spends both unit capacities exactly. This detector does not turn equality into strict positivity. The extra facts used for the actual source repair are F7-F8a's uniform theta-ratio bounds at the ACTIVE receiving locations and the exact prime-power weights and Jacobians. None follows merely from a radical or a positive auxiliary matrix.

### 7.2 Additional falsifiers

Dropping the receiving Jacobian changes the coefficient 6 in F16 or 72 in F20 and invalidates the resource proof. Applying the inward laws down to |x+t/2|=R violates the hypothesis y>=2; D24 is an existing warning against that extension, not a repeated computation. Replacing Lambda(2^k) by k log2 supplies nonexistent capacity. Removing the prime edge from a path makes it unable to repair F10; removing all prime resource while retaining the conclusion contradicts F11. Using an even r only would not prove the complex all-test assertion; none of the present path inequalities makes that restriction.

### 7.3 Exactly one next_decisive_test: JOIN_LOCATION_MIXTURE_CAPACITY

[FINITE_CELL][CONDITIONAL as a proposed bounded test, not an executed certificate]. The newly unpaid SAME-I join is

\[
\Omega_J=\{t\in I,\ R<|x+t/2|<11/4\}.
\]

Keep Gamma_c and Gamma_e exactly as above. On Omega_J allow a measurable mixing function theta(x,t) in [0,1] between these TWO explicit kernels: the forward triple law F3 with charges t/s_i, and the inward prime/q/q law F15 with charges 3, reflected according to the sign of the demand midpoint. Theta may depend on both x and t; neither fixed-density charge tuning nor a constant mixture is being proposed.

The exact terminal observable is the residual measure

\[
\mathcal R_\theta=\mathcal C_{\rm new}-\Gamma_J[\theta].   \tag{F25}
\]

Gamma_J[theta] is defined by the same pushforwards: insert theta(x,t) times the Omega_J indicator into F4, and insert 1-theta(x,t) times that indicator into F16-F17 and their reflections. This specifies the operator, including every Jacobian and shared preimage, without discretizing it. All vertices in this test lie in [-4,4]. Other negative lengths stay in the second component of F22, even if this test succeeds.

The single task is to prove feasibility by exhibiting such a measurable theta with R_theta>=0 as a measure, OR to exclude this entire location-dependent two-kernel mixture class by a bounded nonnegative edge price h of finite C_new-integral. Its concrete necessary inequality is

\[
\int_{\Omega_J}n(t)c_t(x)
\min\{C_F(h;x,t),C_D(h;x,t)\}\,dxdt
\le\int h\,d\mathcal C_{\rm new},                       \tag{F26}
\]

where C_F is the F3 expectation of sum_i (t/s_i)h(edge_i), and C_D is 3 times the sum of h on the three F15 edges. An explicit strict reverse inequality kills EVERY measurable theta in this class. It follows by linearity of the mixture and the pointwise minimum, not by a strong-duality theorem. A bounded price supported on [-4,4] receiving vertices and away from u=0 automatically has finite priced continuous capacity; its prime component may be restricted to n=2.

**Stopping rule:** accept a whole-domain feasible measure or a strict price witness with a proved error budget. If neither is established, report the unresolved F25/F26 sign and stop this subattempt. A numerical interval containing zero, a passing necessary price test, or a fit of theta on a mesh is not feasibility. Do not increase degree, precision, the number of path steps or the central radius automatically. This is the sole new mathematical test; recovering and checking the already existing central bytes is a provenance gate, not a second numerical research campaign.

## 8. Dependency epistemics and prediction closeout

| Object | Domain / normalization | Proven output or missing premise | Tags / locator |
|---|---|---|---|
| Canonical GS dictionary | Full physical complex class, f0=Phi/||Phi||2; both poles | F2 from X's RAD and explicit algebra | [ABSTRACT][PAPER]; X CAN/RAD/GS, F1-F2 |
| Central probability and support | Exact I, R=1/8; all ordered triples | Exact density and support; no 3! | [ABSTRACT][PAPER]; F3-F5 |
| Central capacity ceiling | Full D23 receiving domain | Complete embedded-byte/cover audit not completed here | [FINITE_CELL][CONDITIONAL]; section 1.2 |
| Theta tail estimates | All x>=0; ratios at y>=2 or y>=t+2 | Fixed constants, no numerical A needed | [COFINAL_FAMILY][PAPER]; F7-F8b |
| Continuous-only class obstruction | All finite positive-continuous paths; all Y>=3 | Demand exceeds twice even undeducted continuous cut capacity | [COFINAL_FAMILY][PAPER]; F9-F14 |
| Three-edge repair | Whole I and |x+t/2|>=11/4 | Exact physical density; loads <1/32 | [COFINAL_FAMILY][PAPER]; F15-F18 |
| Dyadic repair | Whole N outside I on the two stated wedges | All k, both tails, loads <1/32 | [COFINAL_FAMILY][PAPER]; F19-F21a |
| Combined additional allocation | Omega_e exactly; no central resource overlap | Gamma_e<=C_+ restricted to U /16 | [COFINAL_FAMILY][PAPER]; F22-F23 |
| All-test transfer | Original complex compact smooth g | Conditional on the remaining signed inequality and central ceiling | [COFINAL_FAMILY][CONDITIONAL]; F24 |

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q[g]>=0_for_every_original_complex_compact_smooth_g
  ORIGINAL_REQUESTED_OBJECT: location_dependent_nonnegative_path_allocation_of_all_residual_demand
  ORIGINAL_OBJECT_IS: UNKNOWN
  KNOWN_WEAKER_INTERFACES:
    - direct_signed_DOM_without_a_nonnegative_path_certificate
    - full_source_lower_envelopes_tending_to_zero_on_each_fixed_original_test
    - use_of_the_nonnegative_path_slacks_in_F24_in_a_signed_repair
  CHOSEN_INTERFACE_IMPLICATION: full_residual_capacity_allocation_implies_DOM_implies_all_test_sign
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: arbitrary_short_path_cut_obstruction_and_explicit_disjoint_prime_tail_supply
  REOPEN_TRIGGER: a_proved_signed_or_capacity_comparison_on_Lambda_with_exact_remaining_resources
SCOPED_REFUTATION:
  CLAIM: continuous_only_finite_path_allocation_pays_the_entire_residual_source_demand
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: strict_actual_theta_cut_capacity_upper_margin
  PINNED_EVIDENCE: this_verdict_F9_through_F14_at_Y_equal_3
  SUCCESS_MARGIN_UPPER_ENVELOPE: C_3-D_3_less_than_minus_C_3_less_than_zero
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  ACTUAL_WEIL_SIGN_REFUTED: false
  REPAIR: permit_actual_prime_edges_crossing_the_cut_with_measured_shared_load
```

Two re-representations remain distinct before any escalation. The chosen measure-level allocation keeps the actual locations and all receiving multiplicities; F25-F26 can falsify a whole location-dependent mixture class at estimated kill-power 8/10 and bounded audit cost 4/10. A second representation works directly with the signed remainder in F24 and retains the nonnegative slacks S_c,S_e instead of requiring edgewise allocation; its potential consumer reach is 10/10, but estimated proof cost is 8/10. Those scores are planning judgments, not probabilities or proof evidence. The second representation is not a second dispatched task. Necessity of the original nonnegative allocation interface for DOM has not been proved or disproved; that is why its K8A necessity field is UNKNOWN.

### Frozen predictions

The user probabilities are preserved verbatim: P1=.90, P2=.80, P3=.75. [ABSTRACT][PAPER for this audit ledger]

| Prediction | Fate | Evidence and limitation |
|---|---|---|
| P1: D20-D26 survive their narrow scopes | UNRESOLVED | The source normalization and pushforward arguments inspected survive; complete central/bound-obstruction certificate authentication was not completed. No source theorem is refuted by this provenance limit. |
| P2: changing charges cannot rescue the fixed inward product law | UNRESOLVED | The charge-independent necessary formula is verified by vertex isolation. Its reported numerical overload has not been freshly authenticated through the complete shared bundle, so the whole frozen event is not newly certified. F11 concerns a different, larger continuous-only class and is not substituted as evidence for this prime-law event. |
| P3: partial with a new source allocation or class-wide obstruction | CONFIRMED | F11 excludes all continuous-only tail allocations; F23 pays a specified unbounded additional source domain; F24 remains unpaid. |

Two additional paper-test predictions were recorded before explicit rational validation, after the mechanisms were selected: the Y=3 cut violation (probability .85) and a prime-assisted tail allocation below 1/16 receiving load (probability .80). Both are CONFIRMED by F11 and F23 at PAPER scope. They are not forecasts of an independent checker, and no source-numerical forecast was invented.

What became smaller is the unpaid source domain and the surviving certificate class. The full I far tails and two unbounded wedges have explicit allocations; increasing the count of continuous short steps cannot repair the cut obstruction. What remains open is the entire signed residual F24, not the existence of a canonical radical or another upper trial estimate.

```yaml
iteration:
  target: GOAL058_FULL_SOURCE_LOCATION_DEPENDENT_PATH_ALLOCATION
  status: OPEN
  progress_class: PROOF_PROGRESS
  cognitive_operator_used: DUALIZE
  failed_strategy: global_continuous_only_path_allocation_even_with_arbitrary_step_count
  new_gap_name: location_dependent_middle_allocation_after_disjoint_dyadic_tail_supply
  invariant_learned: prime_crossings_change_cut_capacity_and_must_be_charged_as_atomic_resources
  forbidden_future_move: apply_the_y_ge_2_theta_ratio_bound_at_the_original_central_join
  next_decisive_test: JOIN_LOCATION_MIXTURE_CAPACITY
  route_score: 4
```

### Verification and publication handoff

Only EXPECTED_VERDICT_PATH is authorized for repository publication. No Lean source was written; there are no Lean blob hashes, build commands or axiom profiles to report. No Lean result would follow from this Markdown commit. The next independent paper check should verify F11's exact product exponent, the 6 and 72 inverse-Jacobian factors, the k-independent atomic bound in F21a, and the complete source partition F22 before accepting the new lemmas. Those are checks of this submitted result, not a new source-energy campaign.

The existing central bundle can be checked without rerunning its adaptive search: authenticate its raw SHA-256 and the 16 decoded text hashes, then run its already preserved coverage checker on its preserved rational outputs. Until that occurs in an independently observed execution, this verdict does not promote its false verification flag. The actual commit, parent, changed-path set, file hashes, LF counts and remote publication result are supplied in the external delivery receipt rather than embedded self-referentially here.

## 9. PROSHKA'S OWN LINE

The cut test is useful because it removes an entire family of evasions at once.
More short steps cannot create extra capacity across the same physical cut.
That is a sharper diagnosis than another failed choice of three coefficients.
The prime resource is not a small correction to that diagnosis.
It changes which paths can cross the cut without spending short-edge capacity.
I chose an inward prime detour only where the actual theta ratios justify it.
The location gate is part of the construction, not a qualification added after a fit.
The old join obstruction therefore remains respected rather than challenged by another decimal.
The dyadic extension is attractive because its arithmetic bookkeeping is exact for every length.
Its eight short edges keep the small lengths safely inside the positive continuous interval.
Its final edge has the actual von-Mangoldt weight of a prime power.
I did not choose an operator inverse because this question already exposes the receiving resource directly.
I did not choose a new central density because the existing central charge must remain paid.
The new estimates deliberately leave substantial unused capacity in the remote receiving region.
That reserve is real, but it does not automatically transport back to the middle.
The first move beyond this batch is a location-dependent join mixture with its complete receiving measure.
A strict dual price against all mixing functions would kill that selected mixture class.
The second move is a signed use of the retained path slacks on the long central-crossing strip.
Its failure would be a concrete negative remainder estimate, not a failure of the tail theorem.
Neither move is accomplished merely by observing that all path energies are nonnegative.
The data I would request are the already existing certificate bundle as directly readable exact bytes.
That would close a verification gap, not change the proof target.
I would not request a new eigenvalue table or a denser theta grid for the tail bounds proved here.
The surprising feature is how cheaply remote negative demands can use the inward prime conductances.
The troublesome feature is that the near-join resource is shared by many unrelated demands.
I distrust any argument that replaces that shared measure by a per-path success ratio.
I also distrust a certificate whose completeness is represented only by its largest printed decimal.
The present result separates a new proved tail mechanism from precisely those remaining issues.

## 10. RESEARCH LOG

### Sources consulted

**READ:** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` on rh_clean, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`; judging, source-lock and publication protocol, not an analytic premise.

**READ, full attachment and exact-commit connector:** the FLOW request at commit `4695e21604af1fbe721cd6670707ff109c4352b9`, with both hashes/counts recomputed; definitions, scope, immutable central responsibility, tests and response schema.

**READ, selected proofs:** X at SOURCE_BASE, CAN/FT/ENV, L2 RAD, L3a GS and L3b DOM; raw normalization, exact signed form and radical-to-difference algebra. Its cited external explicit-formula theorem remains a historical source dependency, not a newly fetched paper in this batch.

**READ, relevant excerpts and receipts:** R at SOURCE_BASE, D14-D26; the failed deterministic join, variable-law charge isolation, central convolution law and numerical certificate structure. Some fetched ranges also exposed D10-D13; those continuation/fixed-half-jump results were not re-audited or imported into the new proof. All numerical witness verifications not completed here are marked as reported evidence.

**READ, partial only:** C at SOURCE_BASE, schema `q3_three_edge_central_certificate.v1`, embedded `q3_three_edge_source_kernel.md`, interval/adaptive evaluator excerpts and reported coverage procedure. Raw bundle hash, all embedded hashes and full region coverage were not independently checked. It is not the premise of F7-F23.

**READ, full and rehashed:** `docs/BATCH_PATTERNS.md` at SOURCE_BASE; 11341 bytes, 79 lines, matching SHA and blob. Only this explicitly requested non-Route-B documentation was opened.

**FAILED ACQUISITION:** the exact raw GitHub locator for C; container DNS/download failures and web 404 produced no raw local bundle. The subsequent GitHub blob read returned the matching object metadata and truncated encoded content, not a completed local verification. No external mathematical theorem was imported from that attempt.

**READ, tool metadata:** GitHub file/blob and write-action schemas, solely for pinned source access and authorized publication. Their availability is not evidence for a mathematical assertion.

### Tried or abandoned branches

Continuous-only global routing with arbitrary adaptive finite paths: rejected by F10-F14, not by a restriction to two or three steps.

Inward prime routing at the original join: not rerun; the exact y>=2 premise of the new proof is absent there, and the pinned D24 obstruction remains a separate warning.

Location-gated prime/q/q routing on I: retained with the explicit full density bounds F16-F18.

Dyadic overshoot followed by eight short inward steps: retained in the stated wedges, with all k-branches and their prime weights included in F20-F21a.

Immediate extension of the dyadic law to all locations: not justified; its uniform prime bound uses y>=t+2, which the unpaid middle region does not supply. No global feasibility claim results from the successful wedge calculation.

Replacing central authentication by its upper decimal or by a Git blob metadata match: rejected as insufficient verification; the construction is preserved without claiming a new certificate check.

### Reusable identities and exact controls

The actual theta envelopes F7 and ratio estimates F8-F8a have constants independent of the far-tail location and do not use the normalization A numerically.

For every Y>=3, the exact cut quantities satisfy F14 and D_Y>2C_Y. The fifth-term rational lower check is 35496425/5971968>2.

For a deterministic equal-short detour t=kp-mu with receiving edge y=x-iu, the inverse source-to-receiver Jacobian is m. The two constructions use m=2 and m=8; the physical factors are 3m=6 and 9m=72, respectively.

The cut test does not license a negative theta-source energy: adding prime-crossing capacity changes its necessary inequality. The three-vertex control retains positive, zero and negative cases exactly.

The complete residual identity F24 keeps both path slacks. A future signed proof may spend them; requiring a positive allocation of its remaining demand is not asserted necessary for DOM.
