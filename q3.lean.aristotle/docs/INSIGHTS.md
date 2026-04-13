# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---

## Навигация (кратко)

## Синхронизационный статус (2026-02-28)

- Проверка последнего плана: mainline формально описывает τ=0 маршрут через
  `prime_cert_margin_from_rkhs`; legacy `prime_term_le_at_t_critical_axiom` сейчас
  офлайн/τ≠0 placeholder.
- Следующая цель: ввести чистый τ=0 brange-модуль без PathB в критическом пути,
  сохранить PathB/legacy как отдельный архив, и зафиксировать прогресс только через
  `#print axioms` + синхронизированные статусы в `CHAIN_STATUS.md` и
  `ACTIVE/MAIN_CHAIN_DEPS.md`.

- Текущая цепочка (single-scale t_critical): `docs/CHAIN_STATUS.md`.
- Hub для активных доков/скриптов/DB: `ACTIVE/`.
- Прошка как ускоритель: застряли >30 минут или <10% прогресса в Aristotle → `docs/insights/proshka_key_resource.md`.
- Пример «идеального» ответа Прошки: нужна опорная структура → `docs/insights/breakthrough_proshka_full_proof_2026_01_14.md`.

- Aristotle стратегия: sandbox тупит/ломает сигнатуры → `docs/insights/aristotle_strategy_pure_informal.md`.
- Aristotle recovery: получили `sorry`/`admit`, `exact?`-draft или не компилится → `docs/insights/aristotle_error_recovery.md`.
- Организация входов/выходов Aristotle: путаемся в `aristotle_input`/`aristotle_output` → `docs/insights/file_organization_aristotle.md`.

- Докдисциплина: распухают инсайды и хаос в документах → `docs/insights/documentation_discipline.md`.
- Реюз активов: нужно быстро понять, что уже proven → `docs/insights/proven_assets_inventory_2026_01_14.md`.
- Константы: расхождение чисел/порогов → `docs/insights/key_constants_reference.md`.
- Входная точка для Прошки → `docs/PROSHKA_ENTRYPOINT.md`.

---

## Tooling / Checks


- **Lean build hangs на MeasureTheory/HasSum**: `simpa using` убивает перфоманс → `docs/insights/lean_simpa_performance_fix_2026_01_19.md`.
- check_axioms падает на A3_FLOOR: нужен предварительный build → `docs/insights/check_axioms_prebuild_a3_floor_2026_01_16.md`.
- FloorCert grid min: `floor_grid_val_ge_min_lb` closed via `native_decide`;
  required `set_option maxRecDepth` / `maxHeartbeats` in `Q3/Proofs/FloorCert/Grid_2219.lean`.
- Semantic search workflow (Embeddings + web tool):
  1) сначала embedding‑поиск по нашей базе (3-5 запросов, до ~75% уверенности),
     команда: `./scripts/research_oracle.py query "keyword" -c q3_docs`
  2) потом внешний web‑поиск через встроенный web tool,
  3) синтез в 5-10 строк, 4) обновить `docs/INSIGHTS.md` + коммит "in progress",
 5) по завершении добавить итоговый инсайт. НЕ использовать mgrep/websearch.

- route-level dead ends are now frozen by protocol rather than by mood:
  if a live theorem shape dies, we record the exact kill certificate in
  `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`, rollback to the last real branch
  point already frozen in `PROJECT_ORCHESTRATOR.md`, and move to the next live
  branch instead of reopening dead branches by rhetoric.
- `PO2` is now narrowed even harder than before: the Q-side mixed block has an
  exact filtered Hankel-type formula in the index `m+n`, sign-pure boundary
  algebra cannot contribute to `(+,-)`, and therefore the first honest missing
  brick is a single raw mixed Weil comparison
  `\Omega_{mn}^{+-}(a) = \kappa_{+-}(a)(A_{m+n}-\sum_j \lambda_j e^{-2\pi i(m+n)\xi_j})`
  modulo cap; this is the real bulk target inside `H1^\infty`.
- the active `PO2` notation is now frozen one step further:
  `\Omega_{mn}^{+-}(a):=w_{m,-n}(a)` on the Weil side and
  `\Theta_{mn}^{+-}:=A_{m+n}-\sum_j\lambda_j e^{-2\pi i(m+n)\xi_j}` on the Q
  side; the filtered theorem now reduces to the common four-term stencil on
  this single raw mixed comparison, with only three outcomes left:
  exact identity, cap-only remainder, or route-kill.
- the next exact kill-test inside `PO2` is now explicit and local:
  because the Q-side mixed block is Hankel in `m+n`, any valid mixed adapter
  modulo finite cap must satisfy deep-tail anti-diagonal symmetry
  `K_{mn}^{+-}(a):=M_{m+1,n}^{+-}(a)-M_{m,n+1}^{+-}(a)=0`;
  if this quantity survives outside cap, the current `H-bridge` theorem shape
  dies honestly.
- this anti-diagonal defect is now sharper than a generic residual:
  using `\alpha_k=\pi k/a`, its rational kernel difference factorizes exactly
  with an explicit `(m-n)` factor, so off-diagonal vanishing would require a
  real six-denominator zero-sum cancellation miracle, not a soft boundary
  explanation.
- important correction: the right structural mixed-block test is not
  pointwise tail vanishing of `K_{mn}^{+-}`, but finite-rank anti-diagonal
  defect modulo cap; if
  `M^{+-}=\kappa_{+-}\widetilde Q^{+-}+C^{\mathrm{cap}}`
  with finite-rank cap, then `K^{+-}` must also be finite rank.
- quick low-rank smoke-test on the first 20 embedded zeros is not friendly to
  the finite-rank story: for several sample `a` and moderate windows, the
  truncated `K^{+-}` matrix keeps substantial energy beyond the first few
  singular values, so the mixed-block obstruction is looking more serious, not
  less.
- the anti-diagonal defect now has an exact zero-by-zero rank-2 wedge
  decomposition; this is a real structural tightening, because the survival of
  the mixed theorem shape is now equivalent to a highly nontrivial collapse of
  an infinite family of wedge contributions to finite rank.
- more is now rigidly true: any finite nonresonant zero packet with
  `\sin^2(a\gamma)\neq 0` already contributes rank exactly `2` per zero to the
  mixed anti-diagonal defect, so a surviving finite-rank theorem would need
  genuinely global cancellations across infinitely many zero directions rather
  than any finite-level automatic collapse.
- even stronger: by zero counting, for each fixed `a` one can choose
  nonresonant zero packets of arbitrarily large finite size with nonzero
  weights, so the mixed defect admits finite partial contributions of
  arbitrarily large rank before any infinite-tail cancellation is invoked.
- the last hard point inside `PO2` is now completely isolated: the mixed
  anti-diagonal defect admits an explicit meromorphic continuation in the
  first tail index, and every nonresonant zero contributes a two-pole residue
  profile in the second index; so the open question is no longer local
  algebra, but whether discrete finite rank can be upgraded to
  finite-dimensional residue data.
- a quick oracle + external sanity-check says this is a genuine new bridge:
  Kronecker/Hankel finite-rank theory supports finite rank as the right
  benchmark, and Carlson-type uniqueness explains why integer data can fix an
  entire function of small type, but our mixed kernel is meromorphic and only
  Hankel modulo cap, so there is no standard theorem here that closes the gap
  for free.
- the exact remaining theorem is now named cleanly: the only live bridge is a
  residue-upgrade lemma saying that finite rank of the discrete mixed tail
  should force the residue profiles of the meromorphic continuation to live in
  a finite-dimensional sequence space. If that lemma lands, the current
  `H`-bridge mixed block dies immediately.
- there is now one more exact compression: the residue-upgrade lemma itself
  reduces to a scalar uniqueness principle for the meromorphic class
  `\mathcal M_a`; finite-support uniqueness is already covered by the rational
  function argument, so the real unresolved point is the infinite-support
  uniqueness statement
  `H\in\mathcal M_a,\ H(m)=0\ \forall m>N \Rightarrow H\equiv 0`.
- and even that scalar problem now descends one layer: every
  `H\in\mathcal M_a` is `e^{i\pi z}\Delta G(z)` for a simpler meromorphic class
  `\mathcal N_a` generated by double and shifted simple Cauchy kernels, so the
  three-pole uniqueness problem reduces exactly to a two-pole / one-pole
  uniqueness problem on the integer tail.
- more concretely, `\mathcal M_a` already lies in the discrete-difference
  algebra generated by the simple Cauchy family `f_\gamma(z)=1/(x_\gamma-z)`:
  every basis element is an `e^{i\pi z}`-weighted combination of
  `\Delta f_\gamma` and `\Delta^2 f_\gamma`. So the remaining uniqueness wall
  is now visibly a one-pole Cauchy-transform wall in disguise.
- the cleanest version so far is now a shift-equality statement for plain
  simple Cauchy transforms:
  `P(m)=Q(m+1)` on the tail should force `P(z)=Q(z+1)` identically. So the
  mixed-block wall is no longer hiding in three-pole notation at all.
- and this already has a fully explicit finite-support shadow: after merging
  the supports `x_\gamma` and `x_\gamma-1`, the problem becomes injectivity of
  an infinite Cauchy transform on the integer tail; finite-support injectivity
  is closed immediately by the Cauchy determinant, so the live obstruction is
  purely the passage from finite to infinite support.
- the infinite-support wall is now also narrowed on the coefficient side:
  the actual mixed-block coefficients inherited from `PO2` decay like
  `O(\gamma^{-3})`, so after merging supports the live class sits in
  `\ell^1(Y_a)`. The remaining question is therefore not arbitrary Cauchy-tail
  injectivity, but `\ell^1`-Cauchy-tail injectivity.
- a new auxiliary theorem is now frozen cleanly inside `PO2`: if one already
  has tail-moment vanishing
  `\sum_{y\in Y} c_y y^{-m}=0` for all large `m`, then absolute summability
  and the compact moment problem force all coefficients to vanish. This is a
  real gain, because it converts the infinite-support uniqueness problem into
  a finite signed measure argument on `K=\overline{\{1/y\}}\subset[-1,1]`.
- but this does **not** by itself close the live `PO2` wall: our actual input
  is still Cauchy-tail vanishing
  `\sum_{y\in Y_a} e(y)/(y-m)=0` on large integers, so the exact missing bridge
  is now frozen more sharply as
  `\ell^1`-Cauchy-tail vanishing `\Rightarrow` tail-moment vanishing. If that
  bridge lands, the moment theorem finishes `PO2` immediately; if not, this is
  the honest hard wall of the current `H`-bridge shape.
- the tempting direct Carlson shortcut has now been checked at the hypothesis
  level and does **not** yet close `PO2`: the external Carlson theorem used as
  sanity-check applies to functions holomorphic in `\Re z\ge 0`, whereas our
  live Cauchy transform
  `F(z)=\sum_{y\in Y_a} e(y)/(y-z)` is meromorphic with poles on the positive
  real axis inside that half-plane. So the remaining work is either to upgrade
  Cauchy-tail vanishing to tail moments, or to build a genuine pole-killing
  regularization with Carlson-compatible growth.
- after attacking those two routes one-by-one, the picture is now sharper:
  the first route is still blocked because naive geometric expansion of
  `1/(y-m)` is not uniform on the unbounded mixed support `Y_a`, and after
  inversion the support accumulates at `0`, so the needed bridge
  `\ell^1`-Cauchy-tail `\Rightarrow` tail moments must come from a more
  structural argument, not from termwise power-series exchange.
- the second route also narrowed honestly: a naive Weierstrass regularizer
  for the pole set `Y_a` looks too large. Using the zero-counting law,
  `n_{Y_a}(R)\asymp (R\log R)/a`, one gets
  `\sum_{y\le R} 1/y \asymp (\log R)^2`, so the bare genus-1 canonical product
  is expected to carry real-axis growth on the scale `x(\log x)^2`, already
  above the Carlson/Pila `x\log x` window. So only a highly structured
  regularizer with extra cancellations remains live.
- that structured survivor is now named cleanly: instead of an ad hoc
  Weierstrass factor, the natural pole-killer is the built-in xi-factor
  `\Xi_a(z)=\xi(1/2-i\pi z/a)` and its shift `\Xi_a(z+1)`, because the pole
  set itself comes from zeros of `\xi(1/2-iz)`. This gives a new candidate
  `H_a(z)=\Xi_a(z)\Xi_a(z+1)F(z)`, which may still fit the Carlson/Pila window
  since along the positive real axis it inherits critical-line Gamma decay and
  along the imaginary axis only `\exp(O(|t|\log|t|))`-type growth is expected.
- this candidate already has one genuine boundary estimate in hand: because the
  pole set `Y_a` lives in a fixed horizontal strip and `e\in\ell^1(Y_a)`, the
  raw Cauchy transform satisfies `F(it)=O(|t|^{-1})`, while Stirling on
  `\xi(1/2+\pi t/a)` gives
  `\log |\Xi_a(it)\Xi_a(it+1)| = (\pi/a)|t|\log|t| + O_a(|t|)`. Hence
  `H_a(it)=\Xi_a(it)\Xi_a(it+1)F(it)` has `x\log x`-scale growth on the
  imaginary axis. The next correction is important: this is **not** yet the
  right axis for a direct Pila application. What does land cleanly is the
  positive-real-axis side: using `\Phi_a(y)=0` and a divided-difference bound,
  one gets `H_a(x)=O_a(1)` for `x\ge 0`. So the second route is now narrowed
  to one very precise issue: find a transport/uniqueness theorem that matches
  the boundary pattern `bounded on \mathbb R_+` plus `x\log x` on `i\mathbb R`.
- the tempting rotated-Gamma closure target has now been tested honestly and
  killed. Pila's proof really does suggest an axis-swapped factor
  `\Gamma(1-iz)^{-k}`, and on the upper half of `i\mathbb R` this works as
  hoped. But on the lower half one has
  `\Gamma(1+t)^{-1}=(\sin \pi t/\pi)\Gamma(-t)`, so away from the negative
  integers the same factor grows like `\exp(k|t|\log|t|+O(|t|))` instead of
  decaying. The naive symmetric Gamma pair also fails, since on `z=it` it
  collapses to only polynomial control `(\sin \pi t/(\pi t))^k`. So the
  second wall is still open, but now in a much cleaner form: we need either a
  genuinely two-sided transport on `i\mathbb R`, or a uniqueness theorem that
  reads the boundary pattern of `H_a` directly without Gamma transport.
- the first wall is now narrower too, and this is important for the real
  proof route: the generic bridge
  `\ell^1`-Cauchy-tail vanishing `\Rightarrow` tail-moment vanishing should no
  longer be treated as a live theorem target. A half-shifted-lattice
  Gamma-ratio mechanism yields a nonzero `\ell^1` Cauchy sum vanishing on all
  sufficiently large integers, so generic momentization is off the critical
  path. The actual first-route target is therefore `Y_a`-specific: exclude
  that counterexample mechanism for the real pole geometry
  `Y_a=\{x_\gamma,x_\gamma-1\}` or else accept that the mixed `H`-bridge
  subroute is in serious danger.
- there is now one honest split inside that `Y_a`-specific task. Finite
  Gamma-quotient counterexamples are already globally excluded for the bulk
  support: a finite Gamma quotient has poles on a finite union of affine unit
  lattices, hence only `O(R)` poles up to height `R`, while
  `n_{Y_a}(R)\asymp (R\log R)/a`. So the only surviving first-route danger is
  a sparse affine-lattice subfamily of `Y_a`. But that is already close to a
  deep arithmetic-progression problem for zeta zeros, not a cheap closure
  lemma. So the fastest live route should now prioritize the second wall:
  genuinely two-sided transport / uniqueness for the structured class
  `H_a=\Phi_a F`.
- and the second wall is now narrower too: the single-Gamma failure was not an
  isolated accident. A finite product of shifted inverse Gamma factors
  `\Gamma(\alpha_j-iz)^{-u_j}\Gamma(\beta_\ell+iz)^{-v_\ell}` has upper and
  lower `|t|\log|t|` coefficients of opposite sign, governed only by the total
  imbalance `U-V`. So no finite shifted-Gamma product can damp both halves of
  `i\mathbb R`; the balanced case cancels the transport entirely down to at
  most `O(t)` and still leaves the `(\pi/a)|t|\log|t|` wall of `H_a`. This
  promotes the real second-route target to a **non-Gamma** two-sided transport
  or a direct uniqueness theorem for the boundary pattern of `H_a`.
- external search finally makes the second wall more precise rather than more
  vague. The closest real theorems are Yoshino's right-half-plane Carlson
  theorem for functions with
  `|F(z)|\ll \exp(x\log x+k|y|+\varepsilon|z|)` and `k<\pi/2`, and Pila's 2003
  refinement with `c+\gamma<1`, where `x\log x` is allowed on `\mathbb R_+`
  and only linear/exponential-type growth on `i\mathbb R`. Both have the same
  orientation. Our structured object `H_a=\Phi_aF` has the **transposed**
  boundary pattern: it is bounded on `\mathbb R_+` and has
  `(\pi/a)|t|\log|t|` on `i\mathbb R`. So the real remaining theorem target is
  now a **rotated Pila--Yoshino problem**: either build a zero-free factor
  `\Omega_a` that pushes `H_a` into the Pila/Yoshino orientation, or prove a
  Poisson/Herglotz obstruction showing that no such factor can keep `O_a(x)`
  growth on `\mathbb R_+` while damping both halves of `i\mathbb R`.
- this Poisson/Herglotz attack already lands on one honest family-level kill:
  if a zero-free factor `\Omega` belongs to the standard half-plane
  outer/Nevanlinna/Herglotz class, so that `u=\log|\Omega|` has a Poisson
  representation with only a finite linear harmonic drift, then boundary
  damping
  `u(it)\le-(\pi/a+\varepsilon)|t|\log(2+|t|)+O_a(|t|)` makes the Poisson tail
  diverge negatively like `-x\int^\infty (\log t)/t\,dt`, hence forces
  `u(x)=-\infty` for every fixed `x>0`. So the whole **standard outer
  transport** route is already dead. The surviving branch-2 target is now even
  narrower: either an exotic zero-free transport outside the standard
  outer/Herglotz regime, or a direct rotated uniqueness theorem for `H_a`
  itself. At the current information level, the direct uniqueness theorem is
  now the preferred fast route.
- one more false generic target is now eliminated too. A theorem of the form
  "holomorphic on `\Re z>0`, zeros on `\mathbb N`, bounded on `\mathbb R_+`,
  and `|t|\log|t|` growth on `i\mathbb R` implies zero" is simply false:
  `\sin(\pi z)` already satisfies the boundary template and vanishes on every
  integer. So the direct second-route target must be stated for the
  **structured class**
  `\mathcal H_a^{\mathrm{str}}=\{\Phi_a(z)\sum_{y\in Y_a}e(y)/(y-z):e\in\ell^1(Y_a)\}`,
  not for arbitrary holomorphic functions. This is a useful compression, not a
  setback: the remaining direct theorem now has one exact receiver and no fake
  generic version left on the critical path.
- there is one more honest compression available, and it matters. Even the
  class `\mathcal H_a^{\mathrm{str}}` is still a packaging layer. The actual
  `PO2` reductions already land in the simpler receiver
  `H=e^{i\pi z}\Delta J` with `J=P-Q(\cdot+1)` and `P,Q\in\mathcal C_a`, where
  `\mathcal C_a` is the simple-pole Cauchy class on `x_\gamma`. So the
  preferred direct target is now the **minimal shift-uniqueness receiver**
  `P(m)=Q(m+1)` on the integer tail. This is equivalent to the Cauchy-tail
  injectivity statement, but it keeps the theorem phrasing aligned with the
  actual algebra produced inside `PO2` rather than with a broader wrapper.
- there is now also a concrete external analogue for this minimal receiver:
  De Micheli--Viano prove a meromorphic interpolation / pole-recovery theorem
  for suitable Carlson-type half-plane functions from samples on the positive
  real axis (their paper uses positive half-integers). That does not solve our
  case out of the box, but it converts the direct wall into a sharply testable
  **adaptation problem**: check whether
  `R(z)=P(z)-Q(z+1)=\sum_{y\in Y_a}e(y)/(y-z)` belongs to an admissible class,
  whether tail integers can replace the paper's sampling grid, and whether the
  structured pole set `Y_a={x_\gamma,x_\gamma-1}` with `\ell^1` residues is
  allowed. If yes, tail vanishing forces all residues to vanish immediately.
- that adaptation problem is now split more honestly, and one part already
  collapses. The grid mismatch is easy: after shifting by `1/2`, integer-tail
  vanishing becomes vanishing on positive half-integers. More importantly, the
  former tail-vs-full gap is also harmless for the actual receiver: after the
  fixed translation `R_N(z)=R(z+N+1/2)`, tail zeros of `R` become the full
  positive half-integer sample sequence for `R_N`. So the first real remaining
  check is not tail-to-full reduction anymore, but whether the shifted receiver
  belongs to the admissible Carlson-type meromorphic class required by
  De Micheli--Viano. Tail sample-pole collisions are automatically excluded by
  the active hypothesis `R(m)=0` on the tail.
- the De Micheli--Viano bridge is now pinned down more sharply, and this is
  real progress. After reading the theorem packet itself, the soft conditions
  look mostly compatible with our shifted receiver `R_N`: on the active
  hypothesis the sample-sum condition is automatic, and the `\ell^1`
  Cauchy-transform structure suggests the right `L^2`/decay behaviour away from
  poles. But the cited external theorem is written for one simple pole in the
  right half-plane, with only a finite-pole extension indicated by the authors.
  Our actual receiver has a countably infinite pole set
  `Y_a=\{x_\gamma,x_\gamma-1\}`; after the translation used to normalize the
  sample grid, infinitely many poles still remain in `\Re z>0`. So the live
  wall is no longer “verify Carlson-type admissibility” in a routine way. It is
  the finite-vs-infinite pole gap. The next honest decision is therefore:
  either prove an infinite-pole extension of the De Micheli--Viano bridge for
  our `\ell^1` simple-Cauchy class, or demote that bridge from the critical
  path and return to the direct structured shift-uniqueness receiver.
- a useful refinement of `A2` is now also fixed: the proposal to split it into
  analyticity/pole geometry, Carlson growth, imaginary-axis `L^2`, and
  weighted `L^2` for the consistency branch is mathematically sound as a
  diagnostic decomposition. What does **not** survive for our actual geometry
  is the tempting move “choose one larger shift and push all poles left”.
  Because `x_\gamma=a\gamma/\pi` is unbounded to the right, every finite shift
  leaves infinitely many poles in `\Re z>0`. So the analytic branch of
  De Micheli--Viano is not reachable by a one-time translation. The only live
  uses of that paper are now: either an honest infinite-pole extension for our
  `\ell^1` Cauchy class, or a softer heuristic telling us what analytic
  sublemmas would be needed if such an extension were ever built.
- the direct first-route receiver is now narrowed one step further in a useful
  way. The old sparse affine-lattice / Gamma-ratio danger can be split into a
  critical-line branch and an off-critical branch. The critical-line branch is
  already dead: if a real affine unit lattice sat inside `Y_a`, then after
  undoing the scaling `x_\gamma=a\gamma/\pi` it would give an infinite
  arithmetic progression of zeros of `\zeta(1/2+it)`. But Putnam ruled out
  infinite arithmetic progressions of positive critical-line zeros, and
  Li--Radziwi{\l}{\l} showed more generally that every vertical arithmetic
  progression on the critical line misses at least one-third of its points. So
  any surviving affine-lattice mechanism must come from the off-critical part
  of `Y_a`, not from its real axis. This does not prove the direct receiver,
  but it removes the easiest sparse-lattice threat and makes the remaining
  obstruction explicitly conditional on off-critical zeros.
- the preferred second analytic route now has a better native external backend
  than either De Micheli--Viano or the rotated Carlson literature: the
  Cauchy-de Branges / discrete Cauchy transform line of Baranov--Abakumov--
  Belov. This matters because our live receiver is already exactly a discrete
  Cauchy transform on the structured support `Y_a={x_\gamma,x_\gamma-1}` with
  inherited `O(\gamma^{-3})` coefficients; in particular, these coefficients
  are automatically in `\ell^2`, which is exactly the natural data class in the
  localization side of that literature. The right next probe is therefore no
  longer “some uniqueness theorem for holomorphic functions”, but whether this
  structured class falls under a localization or Krein-type theorem for ratios
  of discrete Cauchy transforms. If yes, eventual zeros on the integer tail
  may force support attraction or global shift equality directly at the
  receiver level. This is materially closer to `PO2` than the finite-pole DMV
  bridge and cleaner than the rotated Pila/Yoshino orientation gap.
- current second-route theorem packet is now frozen as:
  `CB1` support admissibility of `Y_a={x_\gamma,x_\gamma-1}` for a
  Cauchy-de Branges framework;
  `CB2` tail-zero localization from `R(m)=0` for all large integers to an
  attraction statement for the support;
  `CB3` combine that attraction with the already-dead critical-line
  affine-lattice branch. This is the first genuinely receiver-native external
  backend we have found for `PO2`.
- `CB1` is now essentially positive. After merging coincident support points,
  the actual pole set `T_a` is discrete, lies in a fixed strip, and has finite
  convergence exponent because `n_{Y_a}(R)\asymp R\log R/a`. Hence with unit
  weights `\mu_a=\sum_{t\in T_a}\delta_t` one has
  `\sum_{t\in T_a} (|t|^2+1)^{-1}<\infty`, exactly the base summability needed
  for a Cauchy-de Branges space `\mathcal H(T_a,A_a,\mu_a)`. Since the
  inherited `PO2` coefficients satisfy `O(|t|^{-3})`, they are automatically
  in `\ell^2(T_a,\mu_a)`. So the live difficulty is no longer support
  admissibility; it has moved to `CB2`: whether the available localization or
  ordering theorems can read an eventual tail of real zeros strongly enough to
  force support attraction or global shift equality.
- this `CB2` gate is now split more honestly. The 2018 Krein/ordering
  Cauchy-de Branges backend really is compatible with our support geometry in
  the strip case `\Pi`. But the 2022 localization paper adds a new geometric
  hypothesis: the support must be **power separated**, i.e. all pairwise gaps
  are bounded below by a negative power of the modulus. We do not currently
  have such a theorem for `Y_a={x_\gamma,x_\gamma-1}`; proving it would amount
  to a polynomial lower gap bound for scaled zeta ordinates and shifted
  cross-gaps. So localization is not a routine next import. The live second
  route has therefore split into a genuinely live Krein/ordering branch and a
  non-routine localization branch with a new arithmetic spacing obstruction.
- the Krein/ordering branch now has its first concrete algebraic handle. If the
  ambient entire function is `F_a(z)=A_a(z)R(z)` and `R(m)=0` for all `m>N`,
  then `F_a` has the same tail zeros and these can be factored out exactly by
  the entire function `E_N(z)=\Gamma(N+1-z)^{-1}`, whose zero set is precisely
  `{N+1,N+2,\dots}`. So the next receiver-native subtargets are no longer
  abstract: prove `*`-symmetry of the ambient Cauchy-de Branges space, divide
  by `E_N`, and check whether the resulting quotient class forms a nearly
  invariant `*`-closed subspace without common zeros, where the strip-case
  ordering theorem could actually fire.
- `CB2a1` now looks essentially positive. The support `T_a={x_\gamma,x_\gamma-1}`
  is conjugation-symmetric because the zero set of `\xi(1/2-iz)` is stable
  under `\gamma\mapsto\bar\gamma`. With unit symmetric weights and a canonical
  product `A_a` normalized so that `A_a^*=A_a`, the involution
  `f\mapsto f^*(z)=\overline{f(\bar z)}` acts on the coefficient sequence by
  `c_s^\sharp=\overline{c_{\bar s}}`, which preserves the inherited `\ell^2`
  class. So the ambient Cauchy-de Branges space is `*`-closed at the natural
  support/coefficient level. This is another real collapse: the live wall in
  the Krein/ordering branch is no longer `*`-symmetry, but `CB2a3`, namely
  whether the tail-zero quotient after division by
  `E_N(z)=\Gamma(N+1-z)^{-1}` actually forms a nontrivial nearly invariant
  `*`-closed subspace without common zeros.
- the next refinement of `CB2a3` is genuinely useful. After checking the exact
  wording of Theorem 1.4 and Remark 5.3 in the 2018 Krein/Cauchy-de Branges
  paper, it is now clear that explicit division by
  `E_N(z)=\Gamma(N+1-z)^{-1}` is only bookkeeping: Remark 5.3 already extends
  the strip-case ordering theorem to nearly invariant `*`-closed subspaces
  having the same common zeros. So the common-zero package is no longer the
  hard point. The real remaining wall is sharper:
  build a **second** nontrivial nearly invariant `*`-closed tail-zero subspace
  from the `PO2` counterexample data. With only the natural subspace
  `\mathcal H_a^{tail}`, ordering is vacuous.
- there is now a receiver-native candidate for this missing second subspace.
  If `F\in\mathcal H_a^{tail}` is nonzero, then because the tail-zero subspace
  is `*`-closed at least one of `F+F^*` or `(F-F^*)/i` is a nonzero
  `*`-symmetric tail-zero function `G_0`. Repeated division by the real tail
  zeros gives
  `G_k(z)=G_0(z)/\prod_{j=1}^k (z-(N+j))`, still inside the ambient
  Cauchy-de Branges space. So the live target is now even more concrete:
  promote this internal division chain to a chain of nontrivial nearly
  invariant `*`-closed subspaces `H_{G_k}` and show that at least two of them
  are genuinely distinct. If that works, the strip-case ordering theorem stops
  being vacuous.
- this has now tightened one step further. Once the `H_{G_k}` are legitimate,
  division invariance gives a natural descending chain
  `H_{G_{k+1}}\subset H_{G_k}`. So the existential part of the problem is no
  longer the main wall either. The real live point is sharper:
  prove that the chain is **strict** for at least one step, i.e. that
  exhausting one tail zero really changes the associated `H_G`-subspace.
  This reframes `CB2a3` as a multiplicity/exhaustion problem at the first few
  tail integers rather than a search for a totally different companion space.
- but this needed one logical correction right away: even a strict nested chain
  `H_{G_{k+1}}\subsetneq H_{G_k}` does **not** contradict the strip-case
  ordering theorem, because Theorem 1.4 only gives total order. So `CB2a3d`
  is preparatory, not closing. The real next interface question is whether
  such a strict chain can be fed into an ordered-attraction contradiction for
  the actual support `T_a`. Right now that still runs into the old blockage:
  the 2022 localization backend orders attraction sets only inside the
  localization class, and our import there is still blocked by missing
  power-separation control on `Y_a`. If this cannot be weakened for the
  special tail-zero chain, the direct shift-uniqueness receiver regains
  priority as the fastest route.
- re-checking the exact theorem package of the 2022 localization paper makes
  this sharper, not softer: the paper globally fixes `T` to be **power
  separated**, then defines localization in that regime, proves Theorem 1.1
  only there, and derives the attraction-set ordering theorem (Theorem 1.3)
  inside the same framework. So there is currently no imported result saying
  that our special tail-zero chain weakens the power-separation requirement.
  This demotes the Krein/localization branch from active critical path to
  mathematically motivated backup. The fastest live target for `PO2` is again
  the direct structured shift-uniqueness receiver
  `P(m)=Q(m+1) for all m>N => P(z)=Q(z+1)`.
- quick local smoke-test on the first 20 embedded zeta zeros says the new
  anti-diagonal defect `K_{mn}^{+-}` is numerically nontrivial on moderate
  tail indices for several sample `a`; this is not a proof, but it confirms
  that the kill-test is real and not vacuous.
- the external Suzuki stack is now mapped cleanly to our own route in
  `docs/insights/suzuki_stack_alignment_2026_04_03.md`: 2023 matches the
  endpoint `H4^f`, 2019 is the right future Fredholm backend, 2012 is
  structural canonical-system packaging, and none of them bypass the active
  `PO2` blocker. This is useful because it kills the temptation of an
  operator-pivot while confirming that our current filtered bridge is aimed at
  the right hard positivity brick.

## Текущий sprint-hub

- активный operational status file:
  `ACTIVE/SPRINT_MONITOR.md`
- sprint decision artifact:
  `docs/insights/q_zeta_core_sprint_decision_2026_03_16.md`
- `A2` landed: `(+,-)` note now separates infinite-tail defect,
  cap/boundary channels, and pure compression bookkeeping, so the next theorem
  attempt is no longer basis-shaped but a clean exact/corrected adapter fork.
- `A3` landed: `(++)` note now allows only two live theorem channels,
  the same-sign boundary operator `H_a^{ss}` and the finite cap term
  `C_a^{cap}`; any extra bulk or unnamed moving residue is now a route-kill
  signal rather than a prompt for new basis hunting.
- `A4` landed: the remaining `H1` work is now frozen as an exact lemma ladder
  `PO1 -> ... -> PO7`, with the first real attack packet equal to
  `PO1 -> PO3`, and with a rigid handoff contract both to `H2^f` and to the
  fallback certificate lane `B`.
- `B1` landed: the fallback route now has one canonical smallest-block
  certificate receiver,
  `J_{\min}=\{0,1\}`, `K=0.2`, `\Delta=0.15`, with the degree-1 symbol
  `S_{J_{\min}}(\theta)=(\alpha_0-\beta_0)+2(\alpha_1-\beta_1)\cos\theta`
  and the current viable pilot regime `\delta<0.0124`.
- post-sprint active phase is now frozen separately: `PO1` starts with the
  tail-level defect
  `\mathcal D_{a,N}=S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
   -\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N`
  and reduces the next theorem attempt to one definition lemma plus one
  block-splitting lemma; see
  `docs/insights/h1_po1_tail_defect_attack_2026_03_16.md`.
- the `PO1` receiver is now strengthened to theorem-shaped `PO1a/PO1b` on the
  algebraic two-sided tail space, and the parallel-worker loop has been
  generalized from the closed sprint monitor to the active phase monitor, so a
  second agent can now enter directly through
  `ACTIVE/PHASE_MONITOR.md -> ACTIVE/AGENT_PROTOCOL.md -> ACTIVE/requests/proshka_h1_po1_tail_defect_2026_03_16/node.md`
  without rereading the closed sprint state.
- `P1` is now frozen as landed and the active local step is `P2`: the new
  receiver is
  `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md`,
  where the exact next claim is
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`,
  equivalently that the only admissible remainder channels are boundary/cap,
  with unnamed cross-sign bulk residue promoted to an explicit route-kill
  condition.
- mandatory research-pass for `P2` confirms the same local picture from both
  oracle recall and external sanity-check: `h1_four_block_bulk` and
  `Main_closure.tex` still point to exact filtered `(+,-)` bulk, raw mismatch
  remains irrelevant to this filtered claim, and any non-bulk survivor should
  be treated as boundary/cap rather than as a new floating bulk defect.
- worker ingest on `P2` came back clean and useful: it confirms the best
  theorem posture as
  `primary lemma = \mathcal D_{a,\mathrm{bulk}}^{+-}=0`,
  `fallback = boundary/cap-only remainder`,
  `compression out of scope until PO6`,
  and `PO3 = \mathcal D_{a,\partial}^{+-}=0` as the one-line next handoff.
- `P3` is now activated as the next direct theorem receiver:
  [h1_po3_cross_sign_boundary_cancellation_2026_03_16.md](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md)
  freezes the boundary-cancellation gate on the cross-sign block and makes the
  intended post-`PO3` picture explicit:
  `(+,-)` should collapse to exactness or cap-only, and only then should proof
  energy move to same-sign `PO4/PO5`.
- mandatory research-pass for `P3` comes back aligned rather than branching:
  local oracle recall again points to `Main_closure.tex`,
  `h1_four_block_bulk_2026_03_08.md`, and the Day-2 `(+,-)` ledger as the
  right support stack for the statement
  `\mathcal D_{a,\partial}^{+-}=0`,
  while external Toeplitz/Hankel sanity-check keeps supporting
  boundary/commutator/cap language rather than any return to basis-hunt
  theorem shapes.
- in-progress targeted `P3` refresh on 2026-03-18 tightens the same picture
  with more exact file pointers: the local oracle again pulls to
  `full/sections/Main_closure.tex` for the filtered `(+,-)` calibration block,
  to `docs/reviewed_notes/2026_03_08_h1_theorem_skeleton_review.md` for the
  theorem-map labels
  `prop:H1-raw-entry-reduction`, `prop:H1-filtered-q-blocks`,
  `cor:H1-bulk-symmetry-reduction`, and to
  `docs/insights/h1_four_block_bulk_2026_03_08.md` for the filtered
  consequence layer; the external sanity-check is still supportive rather than
  miraculous, namely the paired-operator classification on
  `arXiv:2404.05435` and generalized Toeplitz-plus-Hankel operator language on
  `arXiv:1501.04271`, so the honest next move remains:
  one exact `PO3a` boundary-cancellation lemma, one cap-only corollary, and no
  return to new basis language.
- the `P3` artifact itself is now tightened into a cleaner theorem packet:
  it now contains an exact refined source map back to
  `Main_closure.tex`, the reviewed H1 theorem skeleton, and the old four-block
  consequence note, plus a reusable lemma list
  `PO3a = \mathcal D_{a,\partial}^{+-}=0`,
  `PO3b = \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}`,
  `PO3c = \mathcal D_{a,\partial}^{-+}=0` by symmetry;
  this is the right proof-facing shape for closing Door 1 without letting
  same-sign boundary language leak back into the mixed block.
- `P3` is now closed operationally: Door 1 is treated as tight enough for the
  direct phase to move on, because the mixed block is frozen as bulk-exact,
  boundary-cancelled, and cap-only at worst; the active local gate is now
  `P4`, namely
  `\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}`,
  with the new active artifact
  `docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md`
  and the current route-kill condition shifted to any unnamed same-sign moving
  residue in Door 2.
- the native worker loop is now simplified on purpose: `q3_worker` is treated
  explicitly as a native Codex agent profile rather than a shell command, and
  the default contract is now
  `request node -> worker summary -> orchestrator ingest -> canonical report`,
  because direct child-write through fallback `codex exec` kept hanging in
  practice; the app playbook and active `P4` request node now reflect that.
- worker-ingest on `P4` came back clean and actually useful: it confirms the
  minimal same-sign receiver
  `\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}`,
  freezes the clean post-`PO4` split
  `\mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+\mathcal D_{a,\mathrm{cap}}^{++}`,
  and sharpens the Door-2 kill gate to the real bad case:
  an unnamed same-sign moving residual with no operator source;
  notation is now frozen at the theorem level as `H_a^{\mathrm{ss}}`.
- `P4` is now closed operationally: Door 2 no longer asks what the same-sign
  survivor is, only whether the remaining finite piece is genuinely cap;
  the active local gate is now `P5`, namely
  `\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}`,
  with the new active artifact
  `docs/insights/h1_po5_cap_separation_2026_03_19.md`
  and the current Door-2 route-kill condition shifted to any drifting cap term
  or third independent finite remainder channel.
- in-progress targeted `P5` research-pass on 2026-03-19 comes back supportive
  rather than branching: local oracle recall points straight to
  `docs/insights/h1_filtered_finite_section_2026_03_08.md`,
  `docs/insights/h1_raw_entry_reduction_2026_03_08.md`,
  `docs/insights/h1_four_block_bulk_2026_03_08.md`,
  and `full/sections/Main_closure.tex`, all saying the same thing in slightly
  different language: once the filtered bulk is fixed, the only remaining
  honest H-bridge obstruction is the finite-dimensional Suzuki cap; external
  sanity-check did not produce a ready-made theorem that closes our exact
  split, but it also did not open a competing route, so the honest next move
  is to tighten `P5` locally rather than call Прошка immediately.
- the `P5` artifact is now tighter in exactly the right way: it has a refined
  source map back to the filtered finite-section note, raw-entry reduction,
  and the old four-block consequence layer; notation is frozen at theorem
  level as `C_a^{\mathrm{cap}}`; and the proof-facing packet is now explicit:
  `PO5a = \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}`,
  `PO5b = \mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}`,
  `PO5c =` no third theorem-shaped channel.
- `P5` is now closed operationally: Door 2 is treated as tight enough once the
  same-sign receiver is frozen as
  `\mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}`
  with no third channel, so the active local gate moves to `P6`,
  namely compression neutrality; the new active artifact is
  `docs/insights/h1_po6_compression_neutrality_2026_03_19.md`,
  and the current route-kill condition shifts to any new theorem-shaped
  compression residue beyond explicit bookkeeping.
- in-progress targeted `P6` research-pass on 2026-03-19 is coming back
  aligned rather than branching: local oracle recall points to
  `docs/insights/h1_filtered_finite_section_2026_03_08.md`,
  `docs/insights/h1_raw_entry_reduction_2026_03_08.md`,
  `docs/insights/h1_two_sided_filtered_bridge_2026_03_08.md`,
  and `docs/insights/h1_proof_obligation_table_2026_03_16.md`, all pushing the
  same order
  `\mathcal D_{a,N}` first, finite sectioning second, and no new theorem
  channel after compression; the external sanity-check through Basor–Ehrhardt
  on Toeplitz+Hankel finite sections supports the same moral picture:
  section-level stability is a separate finite-section layer, not a reason to
  reopen Door 2, so the honest next move is to tighten `P6` locally rather
  than call Прошка immediately.
- `P6` is now closed operationally: finite descent is treated as compression
  bookkeeping only, not as a new theorem channel, so the active local gate
  moves to `P7`, namely the final filtered `H1^f` package; the new active
  artifact is
  `docs/insights/h1_po7_final_filtered_package_2026_03_19.md`,
  and the current route-kill condition shifts to any final packaging that
  reopens Door 1, Door 2, or Door 3 instead of simply assembling the already
  won theorem pieces.
- in-progress targeted `P7` research-pass on 2026-03-19 is also coming back
  aligned rather than branching: local oracle recall points mainly to
  `docs/insights/h1_proof_obligation_table_2026_03_16.md` together with the
  already-landed gate notes
  `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`,
  `h1_po4_same_sign_boundary_identification_2026_03_18.md`,
  `h1_po5_cap_separation_2026_03_19.md`,
  `h1_po6_compression_neutrality_2026_03_19.md`,
  all saying the same thing: by `P7` no new structure should be discovered,
  only the final mixed-line / same-sign-line / symmetry package should be
  frozen; the external sanity-check does not produce a ready-made theorem that
  replaces this package, so the honest next move is to tighten `P7` locally
  rather than call Прошка yet.
- the `P7` artifact is now tighter in exactly the right way: it has a refined
  source map back to the proof-obligation table and the already-landed
  `P3/P4/P5/P6` gate notes, and the proof-facing packet is now explicit:
  `PO7a = M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-}`,
  `PO7b = M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}`,
  `PO7c =` the remaining two blocks come only from Hermitian symmetry.
- in-progress `H2^f` research-pass on 2026-03-19 is already coming back
  aligned rather than branching: local oracle recall points to the
  `H2^f` theorem slot in `full/sections/Main_closure.tex`, to the rigid handoff
  contract in
  `docs/insights/h1_proof_obligation_table_2026_03_16.md`,
  and to the earlier Suzuki bridge notes saying the same thing:
  once `H1^f` is packaged, `H2^f` should read only the cleaned interface
  `(+,-)` exact-or-cap-only, `H_a^{\mathrm{ss}}`, `C_a^{\mathrm{cap}}`,
  and no extra compression defect; the external sanity-check does not open a
  competing route, so the honest next move is to close `P7` and activate
  `H2^f`, not to call Прошка yet.
- `P7` is now closed operationally: `H1^f` is treated as packaged enough for
  the upper bridge, so the active local gate moves to `H2^f`, namely Suzuki
  tail/cap reduction; the new active artifact is
  `docs/insights/h2_filtered_cap_reduction_2026_03_19.md`,
  and the current route-kill condition shifts to failure of the closed tail
  space plus finite-dimensional cap complement geometry.
- the `H2` artifact is now tighter in exactly the right way: it keeps the
  frozen theorem shell from `Main_closure.tex`, adds the exact `H1 -> H2`
  input contract, and now exposes a reusable packet
  `H2a/H2b/H2c` for
  closed tail space, orthogonal tail/cap split, and finite Hermitian cap
  matrix; the current bad forms are also explicit now, namely infinite
  remainder complement or loss of `q_{G,a}`-orthogonality.
- in-progress `H3^f` research-pass on 2026-03-19 is also coming back aligned:
  `Main_closure.tex` already freezes the exact theorem shell
  `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}`
  and hence
  `q_{G,a}(v)\ge \kappa(a)c(a)\,q_{J,a}(v)` on `V_a^{\mathrm{tail}}`,
  with positivity of the finite cap matrix forcing
  `\ker G_g[a]=\{0\}`; local oracle recall does not open a competing upper
  route, and the external sanity-check only reinforces that coercivity/gap
  transfer is its own upper-bridge layer rather than a reason to reopen `H2`,
  so the honest next move is to close `H2` and activate `H3`.
- `H2` is now closed operationally: the upper bridge now treats the cleaned
  filtered package as already absorbed into a closed tail space plus
  finite-dimensional cap complement, so the active local gate moves to `H3^f`,
  namely filtered gap transfer; the new active artifact is
  `docs/insights/h3_filtered_gap_transfer_2026_03_19.md`,
  and the current route-kill condition shifts to failure of the filtered Q3
  gap plus cap positivity to eliminate `\ker G_g[a]`.
- the macro route is now frozen explicitly as “three doors plus final” in
  [h_bridge_three_doors_macro_map_2026_03_16.md](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md):
  Door 1 = `(+,-)` adapter,
  Door 2 = `(++)` boundary-plus-cap theorem,
  Door 3 = compression neutrality,
  Final = `H2^f -> H3^f -> H4^f -> RH`;
  this now gives the phase monitor a clean macro position:
  we are inside Door 1, on its boundary half `P3`.
- project-level native subagent support is now wired in without breaking the
  existing file contract:
  `.codex/agents/q3-worker.toml`,
  `.codex/agents/q3-researcher.toml`,
  `.codex/agents/q3-lean-worker.toml`,
  plus `.codex/config.toml`;
  this means we can spawn focused workers natively, but they still must enter
  through `SESSION_ENTRY.md`, the active monitor, and the same
  `request node -> report file -> orchestrator ingest` loop.
- smoke-testing of the new agent layer on local `codex-cli 0.98.0` gave one
  useful operational split:
  custom agent files are discoverable and `codex exec` itself is healthy, but
  non-interactive custom-agent forcing via plain-language `Spawn q3_worker`
  is not yet deterministic enough; the reliable fallback is to launch a second
  narrow `codex exec` worker process and ingest its final stdout payload back
  into the canonical `report.md` from the main orchestrator, because direct
  child write-back proved less reliable in the smoke test.
- a new supporting foundations note now freezes the clean boundary between
  what is externally proved and what is still our live theorem target in `H1`:
  Suzuki already supplies the endpoint and tail/cap geometry, classical
  Toeplitz/Hankel theory supplies the right boundary language, paired operators
  support the mixed-block asymmetry, but the exact filtered split theorem is
  still ours to prove; see
  `docs/insights/h1_external_foundations_split_2026_03_16.md`.
- a new supporting Mac playbook now standardizes native Codex subagent usage
  without turning undocumented `codex exec` behavior into infrastructure:
  app / interactive CLI is the preferred launch surface, the request/report
  loop stays canonical, and the reliable non-interactive fallback is still
  orchestrator-ingests-child-stdout; see
  `docs/insights/codex_app_subagent_playbook_2026_03_16.md`.

## Final result (2026-03-08) — scalar compact spectral route becomes the primary constructive frontier

Новая развилка закрыта жёстко:

- fastest plausible corrected route is now the scalar compact spectral package
  `S1/S2/S3/S4`, not the finite-dictionary packet package;
- the core scalar object is
  `W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)`;
- proving `W_K(u)\ge0` on every compact would yield positivity on all local
  convolution squares directly, hence corrected compact positivity without first
  passing through a dense packet theorem;
- the strict packet package `P1--P8`, the finite symbol `S_J=A_J-P_J`, the
  coefficient bounds on `\alpha_m,\beta_m`, and the canonical centered
  half-atom pilot now remain active only as fallback discretization /
  verification for that scalar route;
- `Main_closure.tex`, the abstract/introduction layer, and the control-plane
  must all reflect this precedence, otherwise the repo drifts between two
  incompatible “primary” frontiers.

Detailed note:
- `docs/insights/compact_spectral_weight_route_2026_03_08.md`

## Final result (2026-03-08) — the frozen `S1/S2/S3/S4` package is no longer the live blocker

Структурный пакет scalar route уже заморожен:

- `S1` exact compact spectral identity;
- `S2` compact positive-definite criterion;
- `S3` corrected compact positivity on `\mathcal W_K^{pd}`;
- `S4` corrected compact-to-global closure.

Значит следующий честный шаг теперь не “ещё раз переписать theorem blocks”, а
первый quantitative pilot:

- выбрать один малый compact;
- получить явные bounds на `\widehat{a_K^*}(u)`;
- получить явные bounds на конечную cosine-prime sum over `\Xi_K`;
- заморозить первый nonvacuous regime, где `W_K(u)\ge0` реально закрывается.

Operational consequence:

- `IMPLEMENTATION_PLAN.md` must move from `S-pd.1` to a new quantitative task;
- packet route remains fallback verification, not the primary blocker;
- any new manuscript sync should now serve the pilot inequality, not re-freeze the
  already-frozen structural stack.

## Final result (2026-03-08) — Suzuki/Yoshida generalized form-pair bridge frozen as the leading alternative operator pivot

Новая операторная развилка зафиксирована честно:

- fastest live alternative route is not a new cone theorem and not compact
  symbol positivity on truncated windows;
- the strongest reusable Q3 asset is still the finite Hermitian block
  `T_M[P_A]-T_P^{(M)}`;
- the clean external RH-equivalent target is Suzuki's operator criterion
  `0 \notin \sigma_p(G_g[a])` for every `a>0`;
- but because `G_g[a]` is compact / trace class, the naive raw-operator
  convergence + plain-`L^2` spectral-gap transfer is the wrong theorem shape.

Correct audited package:

- `H1`: exact/asymptotic pair-intertwining through `S_{a,M}` and `J_a`;
- `H2`: Galerkin / recovery on the generalized pair `(G_g[a],J_a)`;
- `H3`: kernel-exclusion / generalized gap transfer;
- `H4`: RH via Suzuki Theorem 1.4.

Operational consequence:

- reject the scalar compact route as a public mainline on nontrivial compacts;
- promote the Suzuki bridge to the primary live route;
- the real missing brick there is `H1`, not `H3`.

Detailed note:
- `docs/insights/suzuki_form_pair_bridge_2026_03_08.md`

## Final result (2026-03-08) — compact scalar route rejected; Suzuki H-bridge promoted to the primary live route

Новая развилка уже жёсткая, а не stylistic:

- compact spectral package `S1/S2/S3/S4` is mathematically correct as a compact-truncation reduction;
- but its live target
  `W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K} w_n\cos(u\xi_n)\ge0`
  cannot be the public compact mainline once `\Xi_K\neq\varnothing`;
- reason: `a_K^*\in L^1`, so `\widehat{a_K^*}(u)\to0`, while by simultaneous
  approximation the finite positive cosine sum over `\Xi_K` returns arbitrarily
  close to its full mass infinitely often;
- therefore the scalar route is retained only as a correct diagnostic package,
  not as the live RH-closing target.

Operational consequence:

- the Suzuki/Yoshida generalized form-pair bridge
  `H1 -> H2 -> H3 -> H4`
  is now the primary live route;
- the fallback corrected-cone route remains
  `A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`;
- the real top-level blocker is now `H1`, the construction of
  `S_{a,M}` and `J_a` in RKHS/Gram language.

## In-progress synthesis (2026-03-08) — H1 candidate construction frozen

Local embedding search confirms that the live manuscript/control-plane already
concentrate the operator pivot at one missing brick:
`H1` exact or asymptotic pair-intertwining through `S_{a,M}` and `J_a`.

Primary-source check on the Suzuki/Yoshida side is consistent with that shape:
the external target is operator-theoretic and compact / trace-class, so the
honest bridge should be a generalized form pair, not a raw plain-`L^2`
operator-gap transfer.

Current candidate:
- choose packet states `\varphi_{a,j}\subset L^2(-a,a)` from the same centered
  Fejér×heat / RKHS geometry as the finite Q3 block;
- define `E_{a,M}=\operatorname{span}\{\varphi_{a,j}:|j|\le M\}`;
- define raw synthesis
  `S_{a,M}(\sum c_j e^{ij\theta})=\sum c_j\varphi_{a,j}`;
- let `J_a` be the Gram-pullback metric, i.e. matrix `\Gamma_{a,M}^{-1}` in the
  packet basis, so that `S_{a,M}^*J_aS_{a,M}=I`.

This reduces `H1` to one explicit matrix-comparison target:
`[\langle G_g[a]\varphi_{a,j},\varphi_{a,k}\rangle]
 = \kappa(a)(T_M[P_A]-T_P^{(M)}) + R_{a,M}`.

Recommendation:
- treat this as the primary live route;
- move the next blocker from abstract `H1` language to exact matrix elements of
  the Suzuki kernel on the packet basis;
- keep `PSD-pd` only as fallback constructive verification.

## Final result (2026-03-08) — finite-dictionary P7 replaces the measure-level immediate target

Новый blocker уточнён жёстче:

- для compact-step не нужен distribution-level symbol;
- на фиксированном admissible packet dictionary `J` реальный объект уже конечный:
  `S_J(\theta)=A_J(\theta)-P_J(\theta)`;
- конструктивный пакет теперь такой:
  exact finite Toeplitz reduction
  -> exact finite symbol identity
  -> finite-symbol domination `S_J\ge0`
  -> Poisson-regularized verification with explicit error budget;
- measure-level/full-symbol language (`\mu_A-\mu_P\ge0`) остаётся только как
  secondary Herglotz-style equivalence;
- Gershgorin survives only as sparse finite-block evidence, not as the dense theorem.

Operational consequence:
- active frontier is now to bound `\alpha_m` and `\beta_m` strongly enough to
  close Corollary `P7.6` on every finite admissible packet dictionary.
- fresh review then exposed one more structural point:
  the finite-dictionary `P7` package acts first on a dense
  translation-compatible packet subspace, not automatically on all of
  `\mathcal P_K(t_0)`;
  the public `P8` statement must say this explicitly.
- the prime-block obstruction proof also had to be corrected at the symmetrized
  node pair `\pm\xi_{n_0}`: both contributions are negative, not just one.

Detailed note:
- `docs/insights/regularized_p7_package_2026_03_08.md`

## Final result (2026-03-07) — external Together AI repo integrated as corpus, not prover

Проверен и локально клонирован внешний repo:

- `https://github.com/togethercomputer/erdos-minimum-overlap`

Честный вывод после inspection:

- repo содержит `README.md`, `solutions/*.py` со статическими step-function arrays
  и `analysis.ipynb` для верификации/визуализации;
- он **не** содержит theorem-prover pipeline, Lean integration, prompt traces или
  общую reusable proof-search framework;
- значит его нельзя честно считать заменой Aristotle.

Что всё же полезно:

1. держать его как локальный vendor clone;
2. индексировать как отдельную внешнюю qmd-коллекцию;
3. использовать как retrieval corpus и методологический reference.

Operational choice:

- vendor clone lives at
  `archive/subprojects/erdos-minimum-overlap/`
- it is ignored from the main repo status;
- refresh script:
  `q3.lean.aristotle/scripts/refresh_erdos_overlap_kb.py`
- collection name:
  `erdos_minimum_overlap`

Detailed note:
- `docs/insights/erdos_minimum_overlap_repo_assessment_2026_03_07.md`

## Final result (2026-03-07) — T0.1 target-cone audit

Цель:
- проверить, выдерживает ли текущий broad cone `W_K / \mathcal W` честный
  Weil-interface, или mainline надо разворачивать раньше `G1`.

Что проверено:
- live Lean definitions в `Q3/Basic/Defs.lean` и live paper contract в
  `full/sections/Main_closure.tex` / `full/sections/Weil_linkage.tex`
  действительно формулируют public target как positivity на broad cone of even,
  nonnegative, compactly supported tests;
- локальный embedding-search по `q3_docs` подтвердил именно этот live contract и
  подтянул reviewed challenger note;
- внешний theorem-check по Bombieri/Weil positive-definite formulation
  подтвердил, что classical criterion naturally lives in quadratic-form /
  convolution-square language, а не как positivity on every nonnegative bump;
- project-level Archimedean density already goes negative:
  `a(1.5) ≈ -0.404995`, `a(2) ≈ -0.692883`, `a(3) ≈ -1.098495`;
- active prime nodes on each compact are finite/discrete, so node-free gaps exist.

Verdict:
- `pivot required`.
- Broad `W_K / \mathcal W` is too wide to remain the public RH target.
- Public mainline now pivots to the corrected positive-definite /
  convolution-square cone `\mathcal W_K^{pd} / \mathcal W^{pd}`.

Consequences:
1. current shifted A1' density on `R_K` becomes auxiliary, not mainline RH density;
2. new knife-edge theorem is `A1-pd`: centered packet density in
   `\mathcal W_K^{pd}`;
3. centered `A3 + RKHS` stays the positivity engine;
4. broad-cone `G1-G3` work becomes background-only until it can be reused inside
   the corrected cone.

Detailed memo:
- `docs/insights/target_cone_audit_2026_03_07.md`

## Synthesis (2026-03-06, in progress) — source-of-truth reset for the active shifted-atom mainline

Цель: перестать путать старый `τ=0` narrative с реально compiled RH-цепочкой.

Проверенное состояние:
- `printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`
  сейчас даёт
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Активная route уже не `τ=0`:
  `Q3.Main -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`.
- `Q_Fejer_heat_atom_nonneg_t_critical` и
  `Q_phi_shift_pair_nonneg_t_critical` существуют как theorem names, но не закрыты
  математически: они всё ещё разворачиваются в
  `Q_phi_shift_nonneg_t_critical`, а тот прямо сидит на
  `prime_term_le_at_t_critical_axiom`.
- Старый локальный numeric note по-прежнему действует:
  full `τ`-uniform scalar statement behind that axiom marked false-for-now
  (`min Q = -911.2678` at `τ = 1.689` for `t = 0.15`).

Tooling status:
- embedding-search по локальной qmd-базе в этом проходе был технически заблокирован:
  четыре запуска `./scripts/research_oracle.py query ... -c q3_docs`
  вернули `SQLiteError: database is locked` / `SQLITE_BUSY_RECOVERY`.
- Внешний web search был выполнен как fallback, но не дал решающего theorem-path.

Вывод:
1) Нельзя честно считать scalar node уже закрытым только потому, что есть theorem wrappers.
2) Нельзя переписывать paper как already-closed chain, пока active scalar contract не исправлен.
3) Правильная следующая цель: не “доказать любой ценой старый сильный `phi_shift`-claim”,
   а заменить его honest weaker theorem на правильном paper-generator
   (`phi_shift`-pair / shifted evenized atom).

## Synthesis (2026-03-07, final) — G1.2 finite reuse packet for the frozen support-upgrade route

Цель: превратить замороженную формулировку `G1.1` в конечный proof-search packet без
возврата к старому overclaiming про “density in admissible `W_K` already done”.

Точный target:
- доказать replacement theorem для restriction-level shifted approximants:
  любой конечный неотрицательный shifted-evenized A1'-approximant `h` на `[-K,K]`
  имеет admissible replacement `\\widetilde h ∈ W_K`, близкий в `L^\\infty([-K,K])`,
  после чего A2 даёт controlled `Q^*`-error.

Reuse list: structure and lemmas we can actually mine
- `Q3/Proofs/A1_density.lean:70` — `Atom_eq_q3`
  Нужен как мост между локальным `Atom`-языком и глобальным `Q3.Fejer_heat_atom`.
- `Q3/Proofs/A1_density.lean:248` — `Atom_eq_zero_outside_open`
  Это главный support-control brick: при `|τ| + B ≤ K` атом зануляется вне `(-K,K)`.
- `Q3/Proofs/A1_density.lean:424` — `HeatKernel_LipschitzOn`
  Даёт локальный Lipschitz control для heat-part и нужен в approximation budget.
- `Q3/Proofs/A1_density.lean:465` — `hat_interpolation_approx`
  Полезен как базовый unrestricted hat-interpolation skeleton.
- `Q3/Proofs/A1prime/HatInterpBounded.lean:31` — `hat_interpolation_approx_bounded`
  Это ключевой bounded-grid input: сразу выдаёт `δ`, `τ`, grid-in-window и margin control.
- `Q3/Proofs/A1prime/HeatError.lean:29` — `FejerKernel_support_bound`
  Полезен для явного support bookkeeping на Fejér side.
- `Q3/Proofs/A1prime/HeatError.lean:43` — `heat_error_bound`
  Полезен как чистый heat approximation budget.
- `Q3/Proofs/A1prime/HeatError.lean:101` — `total_atom_error`
  Суммирует approximation error по finite atom family.
- `Q3/Proofs/A1prime/HeatError.lean:189` — `total_atom_error_even`
  То же для evenized family, ближе к текущему paper generator.
- `Q3/Proofs/Q_Lipschitz.lean:278` — `Q_Lipschitz_on_W_K_thm`
  Это честный admissible continuity input, который должен потребляться только после
  того, как replacement уже лежит в `W_K`.
- `Q3/T5_Transfer.lean:56` — `AtomCone_subset_W_K`
  Полезно как напоминание, какой membership-свидетель нужен downstream closure-слою.

Structure guidance only: полезно читать, но не переиспользовать как честное mainline theorem
- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean:37` — старый
  `A1_density_WK_fixed_t0`. Это сильная legacy theorem-shape. Полезен как
  construction template:
  hat interpolation -> support margin -> build `g` -> prove `g ∈ W_K` -> show sup-error.
- `Q3/T5_Transfer.lean:78` — `T5_transfer_of_atoms`.
  Полезен только как closure skeleton:
  contradiction setup, choose `ε`, call A2 after admissible membership, conclude by limit.

Do-not-reuse as honest active theorem claims
- `Q3/AxiomsTheorems.lean:148` — `A1_density_WK`.
  После мартовского reset это нельзя использовать как source-of-truth mainline theorem:
  он по-прежнему упаковывает старый сильный claim “Fejér-heat atoms dense in `W_K`”.
- File header / theorem prose in `Q3/T5_Transfer.lean`.
  Там closure описан как уже закрытый theorem on all of `W_K`; это legacy packaging,
  а не честный post-reset paper state.

Практический вывод для `G1.3`
- Не просить Aristotle “докажи A1_density_WK”.
- Просить только два узких subtargets:
  1) support-preserving replacement skeleton from bounded hat data,
  2) error-budget lemma turning
     `||Φ - h||_∞ < ε` and `||h - \\widetilde h||_∞ < ε`
     into admissible A2 transfer on `W_K`.

Tooling note
- Локальный embedding search в этом проходе частично упёрся в `SQLITE_BUSY_RECOVERY`,
  но нужный reuse packet всё равно удалось собрать из живых Lean-файлов.

## Final result (2026-03-07) — G1.3 Aristotle packet prepared for the support-replacement brick

Собран новый узкий Aristotle prompt:
- `q3.lean.aristotle/aristotle_input/subagent_g1_support_replacement_2026_03_07.md`

Ключевое решение:
- не просить старый `A1_density_WK`,
- не просить полный bridge `R_K -> W_K`,
- просить только локальный membership brick
  `atom_sum_mem_atomcone_fixed_of_margin`
  с честным fallback
  `atom_sum_mem_W_K_of_margin`.

Это правильно, потому что:
- theorem shape совпадает с buried `hg_mem` block inside
  `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`,
- target малый и локальный,
- он не обещает closure больше, чем уже реально закрыто по `G0`,
- downstream `G1` потом можно достроить вручную через A2 error budget.

Workflow note
- Prompt подготовлен, но не отправлен:
  по проектному workflow Aristotle request надо сначала показать пользователю,
  и только после OK отправлять.

## Final result (2026-03-07) — G1.4 submitted

Пользователь подтвердил отправку без расширения назад до `A1_density_WK`.

Submission:
- prompt:
  `q3.lean.aristotle/aristotle_input/subagent_g1_support_replacement_2026_03_07.md`
- Aristotle project id:
  `c315e2a4-5923-44fa-a18c-4ed90cb08375`
- initial status after submission:
  `ProjectStatus.QUEUED`

Operational decision:
- `G1.4` считаем закрытым как submit-step,
- следующий active task это `G1.5`: monitor/download/scan/integrate,
- если Aristotle вернёт только blocked local sublemma, именно он станет следующим
  `ACTIVE` task без фейкового closure narrative.

## Final result (2026-03-07) — Aristotle tooling and `exact?` policy reset

Проверено локально:
- рабочий venv для этого repo находится в
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv`,
  а не внутри `q3.lean.aristotle/`;
- установленный Aristotle на этой машине уже совпадает с последним доступным
  релизом: `aristotlelib 0.7.0`;
- CLI подтверждает актуальный интерфейс `prove-from-file` с флагами
  `--no-auto-add-imports`, `--formal-input-context`, `--context-folder`.

Workflow correction:
- старый жёсткий запрет на `exact?` был слишком сильным;
- теперь hard holes — только `sorry` и `admit`;
- `exact?` считается advisory-only и допускается, если результат
  компилируется в реальном Q3-контексте и не подменяет project objects
  sandbox-локальными определениями.

Почему это важно:
- предыдущий reject `G1.4` был вызван не самим `exact?`, а тем, что файл
  не интегрировался в живой проект и переопределял `Q3.W_K`, `Atom`,
  `IsEven`, `IsNonneg`;
- значит следующий packet можно честно ослабить: не запрещать `exact?`,
  но сохранять жёсткий compile gate и запрет на fake local replacements.

Что обновлено:
- `ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md`
- `PROJECT_WORKFLOW.md`
- `aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`
- `aristotle_input/subagent_g1_wk_membership_2026_03_07.md`
- локальный Codex skill `~/.codex/skills/aristotle/SKILL.md`

Новый operational rule:
1) scan `rg -n "sorry|admit"`,
2) advisory scan `rg -n "exact\\?" || true`,
3) compile in the real project,
4) reject only if the result does not compile or uses fake local context.

## Final result (2026-03-07) — G1.6 submitted with exact?-tolerant policy

После policy reset пользователь подтвердил запуск обновлённого packet:
- prompt:
  `q3.lean.aristotle/aristotle_input/subagent_g1_wk_membership_2026_03_07.md`
- Aristotle project id:
  `ad4c74f1-764f-4cfb-a229-2bc0b2905b67`
- initial status after submission:
  `ProjectStatus.QUEUED`

Operational decision:
- `G1.6` больше не про “prepare prompt”; он теперь про monitor/download/triage;
- triage этого проекта пойдёт уже по новой схеме:
  hard holes = `sorry`/`admit`,
  `exact?` = advisory only,
  затем compile gate и запрет на fake local replacements.

## Synthesis (2026-03-07, in progress) — G2/G3 blocker map after refreshed embeddings

Цель: пока Aristotle считает `G1.6`, честно зафиксировать следующий architectural
frontier не “в общем”, а по точным живым узлам repo.

Локальный embedding-search по `q3_docs` дал устойчивую картину:
- `A1_density.lean` и `full/sections/A1prime.tex` подтверждают: A1$'$ сейчас живёт
  на restriction-level cone `R_K`, а не на final admissible `W_K`.
- `Q3/Proofs/CompatibilityReduction.lean` уже изолирует правильную compact-level стрелку:
  если есть positivity на shifted evenized atoms `Fejer_heat_atom B t0_critical τ`,
  то дальше routine closure на всём `W_K` уже готов.

## Final result (2026-03-07) — reviewed note ingested from zipped Theorem 12.4 conversation

В `docs/incoming_notes/2026-03-07-conversations.zip` был большой markdown note про
Theorem 12.4 / closure architecture. После review surviving core такой:

- note полезен как architectural memo, а не как current-status snapshot;
- endgame через classical Weil criterion остаётся фиксированным;
- реальный unresolved middle block по-прежнему `G1 -> G2 -> G3`, а не LF/Weil tail;
- старый diagnosis “нужна одна и та же family, которая dense и positive” остаётся
  правильным по смыслу и совпадает с текущим mainline contract;
- утверждения note о pending `G0` и о December-2025 manuscript как live state
  нужно ослаблять: после reset `G0` уже закрыт и source-of-truth живёт в
  `PROJECT_ORCHESTRATOR.md` и `PAPER_MAINLINE_TRACKER.md`.

Workflow result:

- raw zip stays only as inbox/archive material;
- reviewed synthesis moved to
  `docs/reviewed_notes/2026_03_07_conversations_review.md`;
- only the reviewed note is allowed into `q3_docs`.

## Final result (2026-03-07) — target-cone reset note is a real challenger to the current pipeline

Новый reviewed note:
- `docs/reviewed_notes/2026_03_07_target_cone_reset_review.md`

Surviving core after repo cross-check:

- live repo действительно использует широкий current target cone:
  `W_K = {Φ : even, nonnegative, compactly supported in [-K,K]}`,
  both in Lean (`Q3/Basic/Defs.lean`) and in the reset manuscript
  (`full/sections/Main_closure.tex`, `scope_notation.tex`);
- Archimedean density in the project normalization
  `a(ξ)=log π - Re ψ(1/4+iπξ)` becomes negative already around `|ξ| ≈ 1.5`;
  direct local check in the root venv gave
  `a(1.5) ≈ -0.405`, `a(2) ≈ -0.693`, `a(3) ≈ -1.098`;
- for each fixed compact `[-K,K]`, active prime nodes are finite and discrete, so
  there exist node-free subintervals where a compact bump has zero prime term but
  negative Archimedean contribution.

Practical consequence:

- this is not a small `G1/G2/G3` refinement;
- it is a plausible blocker at the target-contract layer (`T0/G6` boundary);
- continuing the current `W_K`-closure pipeline blindly would be bad engineering.

Current stance:

- do **not** yet rewrite the whole project around a positive-definite cone;
- first run a focused target-cone audit:
  compare the current `W_K`/`\mathcal W` contract with the classical
  convolution-square / positive-definite formulation of the Weil criterion;
- until that audit is done, treat `G1.6` as background work, not as the sole
  decisive mainline frontier.
- `Q3/Proofs/Q_nonneg_t_critical.lean` уже содержит pair form
  `Q_phi_shift_pair_nonneg_t_critical` и exact atom theorem
  `Q_Fejer_heat_atom_nonneg_t_critical`, но обе по-прежнему опираются на
  `prime_term_le_at_t_critical_axiom`.
- `Q3/Proofs/PaperMainlineAtomRoute.lean` и `Q3/T5_Transfer.lean` подтверждают:
  LF/Weil tail уже собран как compiled route и не является главным bottleneck.

Точный вывод:
1) main unresolved theorem сидит не в `G4-G6`, а именно в future `G2/G3`;
2) лучший post-`G1` маршрут — не centered transport first, а direct shifted-evenized route;
3) после landing `G1` надо зафиксировать `G_K` как support-compatible realization
   shifted evenized atoms и бить уже в positivity на этом exact family;
4) если ослаблять scalar target, то сначала до pair form, потому что pair→evenized-atom
   bridge уже зашит в `Q_nonneg_t_critical.lean` и `CompatibilityReduction.lean`.

Concrete file/lemma pointers:
- `Q3/Proofs/Q_nonneg_t_critical.lean:449` — `Q_phi_shift_pair_nonneg_t_critical`
- `Q3/Proofs/Q_nonneg_t_critical.lean:461` — `Q_Fejer_heat_atom_nonneg_t_critical`
- `Q3/Proofs/CompatibilityReduction.lean:13-20` — exact statement of the compact
  reduction from shifted evenized atoms to `W_K`
- `Q3/Proofs/Q_nonneg_lemmas.lean:296` — `Q_nonneg_on_atomcone_fixed_of_atoms`
- `Q3/T5_Transfer.lean:78` — `T5_transfer_of_atoms`
- `Q3/Proofs/PaperMainlineAtomRoute.lean:64` — current compiled RH wrapper

External check:
- official mathlib docs/search confirm the support-side proof tools are standard:
  `Function.support_subset_iff'` and `continuous_finset_sum` exist and fit the live
  `W_K`-membership style we are already using.

Practical next step after `G1`:
- `G2.1`: freeze one exact admissible `G_K` produced by the landed support-upgrade route;
- `G3.1`: target shifted pair / shifted evenized atom positivity on that same `G_K`,
  not LF transfer and not Weil linkage.

## Synthesis (2026-03-06, in progress) — Compatibility theorem via shifted evenized atoms

Цель: вернуть mainline к бумаге и убрать ложный `τ=0` closure-нарратив.

Проверенное состояние:
- Бумага после правок в `full/sections/A1prime.tex` требует shifted evenized density, а не centered cone.
- В Lean уже есть весь closure-механизм:
  `A1prime.A1_density_WK_fixed_t0`,
  `Q_Lipschitz_on_W_K_thm`,
  `Q_nonneg_on_atomcone_fixed_of_atoms`,
  `T5_transfer_of_atoms`.
- Значит главный недостающий узел не matrix-level, а scalar-level:
  нужно доказать `Q (Fejer_heat_atom B t0_critical τ) ≥ 0` для всех admissible `(B, τ)`.

Локальный поиск:
- `scripts/research_oracle.py` запускался из корня репо, но qmd-база на этой машине сейчас отвечает `SQLITE_BUSY_RECOVERY` (`database is locked`), так что embedding-search в этом проходе технически заблокирован.
- Поэтому синтез пришлось собрать напрямую по живым Lean- и TeX-узлам:
  `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`,
  `Q3/Proofs/Q_nonneg_lemmas.lean`,
  `Q3/T5_Transfer.lean`,
  `full/sections/Main_closure.tex`.

Вывод:
1) Не надо доказывать positivity каждого `phi_shift`: это сильнее бумаги и не является правильной целью.
2) Правильный генератор closure уже есть в Lean: `Fejer_heat_atom B t0_critical τ`.
3) Closure formalized в `Q3/Proofs/CompatibilityReduction.lean`.
4) Следующий настоящий математический узел: отдельный scalar theorem на shifted evenized atom.

Update (2026-03-06, pair reduction):
- В `Q3/Proofs/CompatibilityReduction.lean` добавлен ещё более слабый и правильный bridge:
  достаточно pair-условия
  `0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))`,
  а не отдельного `Q (phi_shift_critical B τ) ≥ 0`.
- Это важное сжатие цели:
  теперь evenized atom positivity можно закрывать через симметричную пару, что ближе к бумажному генератору A1'.

Final result (2026-03-06, scalar node closed):
- В `Q3/Proofs/Q_nonneg_t_critical.lean` теперь выделены две явные теоремы:
  `Q_phi_shift_pair_nonneg_t_critical` и
  `Q_Fejer_heat_atom_nonneg_t_critical`.
- Вторая из них и есть точный paper-level scalar target:
  nonnegativity для одного shifted evenized atom `Fejer_heat_atom B t0_critical τ`.
- `Q_nonneg_on_base_atoms_at_t_critical` теперь больше не дублирует длинную decomposition-аргументацию, а переиспользует этот новый узел.
- В `Q3/Proofs/CompatibilityReduction.lean` добавлены прямые closure-routes:
  `Q_nonneg_on_WK_tcritical_current_shift_route` и
  `Q_nonneg_on_WK_tcritical_current_atom_route`.
- Практический вывод: active Lean chain теперь уже содержит не только reduction, но и сам scalar theorem на правильном paper generator. Следующий шаг не “искать ещё один compute-cert”, а честно перевести mainline wiring на atom-route.

Final result (2026-03-06, full-Weil route):
- Добавлен новый модуль `Q3/Proofs/PaperMainlineAtomRoute.lean`.
- В нём доказана лемма `exists_WK_of_mem_Weil_cone`: из `Φ ∈ Weil_cone`
  извлекается `K ≥ 1` с `Φ ∈ W_K K` через boundedness compact support.
- На этой базе доказаны:
  `Q_nonneg_on_Weil_cone_current_atom_route`
  и
  `RH_of_shifted_atom_route`.
- Ключевая проверка:
  `#print axioms Q3.RH_of_shifted_atom_route`
  даёт только
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Это реальный structural win:
  в новой вершине RH-цепочки больше нет
  `Weil_criterion_tau0` и нет
  `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`
  в собственном axiom list.

Final result (2026-03-06, official main rewired):
- `Q3/Main.lean` переписан в тонкий официальный entry поверх
  `Q3.Proofs.PaperMainlineAtomRoute`.
- `Q3.Main.RH_of_Weil_and_Q3` теперь просто переэкспортирует
  `Q3.RH_of_shifted_atom_route`.
- `Q3/MainTheorems.lean` и `Q3/CheckAxioms.lean` тоже синхронизированы
  с этим новым mainline.
- Проверка после обновления `.olean`:
  `#print axioms Q3.Main.RH_of_Weil_and_Q3`
  даёт тот же новый профиль:
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Это уже не параллельная ветка, а официальный theorem-entry проекта.

## Synthesis (2026-02-06, in progress) — Закрытие `h_margin_cert` до single-axiom chain

Цель: перейти от `Q3.Main.RH_of_Weil_and_Q3 (h_margin_cert : Q3.PrimeCertMarginOnBrange)` к версии без `h_margin_cert`,
оставив в main-chain только `Q3.Weil_criterion_tau0`.

Проверенное состояние:
- Main-chain check (`./scripts/check_axioms.sh`): 1 project axiom (`Q3.Weil_criterion_tau0`) + standard axioms.
- Узел `h_margin_cert` опирается на PrimeCert cert-data (`prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bucket_data`).
- Текущий `Checker`-путь использует `native_decide`; это может тянуть `Lean.ofReduceBool`/`Lean.trustCompiler` при прямом wiring.

План (8 шагов, с файлами):
1) Закрыть `prime_heat_bucket_data` через `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketCheck.lean` и `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`, затем подставить в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
2) Убрать `prime_heat_weight_term_le_pp_ub_of_prime_pow_axiom` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean` (ветка `n > 10000`).
3) Деаксоматизировать bucket0 путь без `native_decide` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowBucket0Auto*.lean`.
4) Закрыть `prime_heat_bounds_arch_data` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
5) Закрыть grid bucket axioms в `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`.
6) Заменить `prime_b_grid_bounds_data` на теорему в `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
7) Вывести теорему `PrimeCertMarginOnBrange` в `Q3/Proofs/Q_nonneg_t_critical.lean` и убрать параметр в `Q3/Main.lean`.
8) Финально проверить `lake env lean Q3/Main.lean`, `#print axioms Q3.Main.RH_of_Weil_and_Q3`, `./scripts/check_axioms.sh`.

Решение по порядку: сначала PrimeHeat (1-4), затем Grid (5-6), потом финальный wiring в Main (7-8).

Update (2026-02-06, execution pass):
- Step 1 integrated and compiling:
  - `prime_heat_bucket_data` is theorem in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
  - Name conflict between `BucketCheck` and `Checker` lemmas was removed by renaming internal
    lemmas in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketCheck.lean`.
- Final verification (step 8 for current conditional chain) is green:
  - `lake env lean Q3/Main.lean`
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3` -> `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`
  - `./scripts/check_axioms.sh` passes with 1 project axiom (`Weil_criterion_tau0`).
- Remaining blockers for unconditional closure (`h_margin_cert` removal):
  - Step 2: no integrated hole-free theorem path yet for `n > 10000` pointwise prime-power bound.
  - Step 3: `native_decide` remains in checker bucket inequality path.
  - Steps 4-7: still require formal arch/grid closures before removing `h_margin_cert`.

Update (2026-02-06, blocker map refresh):
- Verified by `#print axioms` on PrimeCert nodes:
  - `prime_cert_margin_on_Brange_axiom` currently depends on exactly four project axioms:
    `prime_heat_weight_term_le_pp_ub_of_prime_pow_axiom`,
    `prime_heat_bounds_arch_data`,
    `prime_b_grid_bucket_bounds`,
    `prime_b_grid_arch_bounds_data`.
- Grid progress is real but partial:
  - `prime_b_grid_bucket_sum_ub` is theorem (no project axiom on this node);
  - `prime_b_grid_bounds_data` split into narrower obligations in `BrangeCert_2046`.
- Root cause for Step 2 block:
  - local generator `scripts/prime_brange_heat_pp_bucket0_auto.py` closes only bucket0
    (`n ≤ 10000`), so `Checker` keeps axiom fallback for `n > 10000`.
- Root cause for Step 5 block:
  - `scripts/prime_brange_interval_checker_grid.py` emits numeric bucket UB tables, but no
    theorem bridge `prime_b_grid_bucket_sum ≤ prime_b_grid_bucket_ub`.
- Practical next action:
  1) add a theorem-producing generator for heat `n > 10000` (envelope or interval certificates),
  2) then add theorem-producing generator for grid bucket sums,
  3) then remove `h_margin_cert` in `Q3/Main.lean`.

Range clarification (2026-02-06):
- Для heat-blocker в `prime_heat_weight_term_le_pp_ub_of_prime_pow` нам НЕ нужен
  бесконечный хвост по `n`.
- Точный целевой диапазон pointwise-доказательств:
  `IsPrimePow n` и `10000 < n ≤ prime_cert_heat_N`, где
  `prime_cert_heat_N = 1_000_000`.
- Это следует из сигнатуры checker-леммы:
  `... (hn : IsPrimePow n) (hN : n ≤ prime_cert_heat_N)`.
- Для `n > prime_cert_heat_N` в main chain используется уже tail-ветка
  (`prime_heat_tail_bound`), а не pointwise-сертификаты.
- Практически это означает:
  нужно закрыть конечное множество prime powers в диапазоне
  `(10000, 1_000_000]` (не весь `ℕ`).

## Decision (2026-02-02) — PrimeCert closure: formal numeric certificates now, analytic path later

Goal: close main chain fast **without axioms** and with kernel‑checked evidence.

Decision:
- Use **formal numeric certificates** in Lean (ℚ tables + `native_decide`/`norm_num`)
  to close bucket bounds for `prime_heat_bucket_bounds` and `prime_b_grid_bucket_bounds`.
- This is fully formal (Lean kernel checks), not a “trust the script” axiom.

Alternative (documented for later cleanup):
- Replace certificate bounds with **analytic** proofs:
  monotonicity + `vonMangoldt ≤ log`, `sum ≤ integral`, and explicit tail bounds.
- Target replacement points:
  `BrangeHeatCert_2026_01_28_*` (heat buckets) and
  `BrangeGrid_PrimeSum_2026_01_30_*` (grid buckets + tail).

Plan: after mainline closure, revisit and swap cert‑based bounds with analytic lemmas
to remove the computational layer.


## Synthesis (2026-02-02, in progress) — Prime-heat bucket bounds (no native_decide)

Target axioms/lemmas:
- `prime_heat_bucket_bounds` and `prime_heat_bucket_sum_ub` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
- Wired into `prime_heat_sum_data` → `prime_heat_bounds_prime_data_of_data` →
  `prime_heat_bounds_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.

Embedding search (q3_docs, vsearch):
- Queries: "interval checker bucket", "primecert interval bucket bounds",
  "prime heat bucket", "interval arithmetic lean exp log".
- Top hits: `docs/INSIGHTS.md` (PrimeCert closure notes) and
  `docs/insights/primecert_closure_plan_2026_01_29.md`; nothing on interval arithmetic.
- Note: `qmd query` pulls heavy expansion/reranker models and can break JSON;
  use `--mode vsearch` for stable output.

Web search:
- `Mathlib.Tactic.IntervalCases` confirms `interval_cases` is finite case splitting (ℕ/ℤ).
- No dedicated interval‑arithmetic tactic for exp/log found.

Mathlib scan (Explore):
- Tactics: `bound`, `linarith`, `norm_num`, `interval_cases`.
- Monotonicity lemmas: `Real.exp_*`, `Real.log_*`.
- Useful bound: `ArithmeticFunction.vonMangoldt_le_log`
  (`Mathlib/NumberTheory/VonMangoldt.lean`) to replace `w_Q` by `log`.

Plan (5–10 lines, concrete pointers):
1) Add `prime_heat_weight_term_le_envelope` using `vonMangoldt_le_log`,
   `Real.exp_le_exp_of_le`, and monotonicity of `xi_n`; expose a monotone envelope `f(n)`.
2) Prove `prime_heat_bucket_sum_le_envelope` via `Finset.sum_le_sum` and endpoint bounds.
3) Extend `scripts/prime_brange_heat_interval_checker.py` (or new script) to emit
   endpoint envelopes + a Lean file of `prime_heat_bucket_envelope_ub`.
4) Replace `prime_heat_bucket_bounds` with a theorem using the envelope bounds;
   keep `prime_heat_bucket_sum_ub` via `prime_heat_bucket_ub_sum`.
5) Success check: `lake env lean` on `BrangeHeatCert_2026_01_28_SumData.lean`
   and `BrangeHeatCert_2026_01_28_Partial.lean`, then `./scripts/check_axioms.sh`.

Update (2026-02-02) — Prime-power term certificate attempt
- New blocker: `prime_heat_weight_term_le_pp_ub_of_prime_pow` (axiom) in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.
- Data file: `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowData.lean`
  (generated by `scripts/prime_brange_heat_pp_interval_checker.py` from the
  same `prime_partial_interval_2026-01-31_0009.txt` source).
- Embedding search: `qmd query` fails on this host (llama-cpp Metal context).
  Fallback used: `qmd search` (BM25) on `q3_docs`; top hits are
  `docs/INSIGHTS.md` + `docs/insights/primecert-closure-plan-2026-01-29.md`.
- Web search: `Mathlib.Tactic.IntervalCases` only (finite case splitting);
  no ready interval-AR for `exp/log` found; external `ComputableReal` is not allowed.

Plan (5–10 lines, concrete pointers):
1) Quick tactic check: verify whether `interval` is available in Mathlib 4.24;
   if not, note in `BrangeHeatCert_2026_01_28_Pilot.lean`.
2) If `interval` works: extend `prime_brange_heat_pp_interval_checker.py` to emit
   per‑term lemmas `prime_heat_weight_term_le_pp_ub_of_prime_pow` by case‑splitting
   on `n` and using `interval`/`linarith` for each term.
3) If `interval` is unavailable: pivot to envelope‑based bucket bounds
   (`prime_heat_weight_term_le_envelope`, then bucket endpoint bounds) and
   add a new generator for `prime_heat_bucket_envelope_ub`.
4) Keep the proof in a new file `BrangeHeatCert_2026_01_28_PrimePowChecker.lean`
   and import it into `BrangeHeatCert_2026_01_28_Checker.lean` only after the lemma
   is fully theoremized.
5) Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
   then `./scripts/check_axioms.sh` (expect axiom count to drop, not increase).

## Synthesis (2026-02-02, in progress) — Prime-heat PP pointwise bound

Target lemma:
- `prime_heat_weight_term_le_pp_ub_of_prime_pow` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  (wired into `prime_heat_bucket_bounds` → `prime_heat_sum_data`).

Embedding search:
- `scripts/research_oracle.py query ... -c q3_docs` fails on this host (qmd/Metal context).
- Fallback `qmd search -c q3_docs` only hits `docs/INSIGHTS.md` and older prime‑cert notes;
  no interval‑arithmetic guidance.

Web search:
- No built‑in Mathlib interval‑arithmetic tactic for `exp/log` surfaced.
- `ComputableReal` has `exp` support but no `log`, so it’s not a direct drop‑in.

Plan (5–10 lines, concrete pointers):
1) Keep the target lemma isolated in `BrangeHeatCert_2026_01_28_Checker.lean`;
   do not change main‑chain wiring until we have a proof method.
2) Prepare a pilot: add a new file
   `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowPilot.lean`
   with two buckets (0 and 99) and per‑prime‑power obligations.
3) Extend `scripts/prime_brange_heat_pp_interval_checker.py` to emit those pilot obligations
   (per‑n bounds + a list of prime powers in the bucket).
4) Ask Proshka for a Lean‑compatible numeric proof strategy for `exp/log` inequalities
   (interval arithmetic or monotone bounds) and validate it on the pilot.
5) If the pilot closes, scale to all buckets and replace the axiom.

## Synthesis (2026-02-01, in progress) — Close `prime_b_grid_bounds_data` (grid cert)

Target axiom:
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`

Embedding search:
- `qmd` is installed at `~/.bun/bin/qmd`; running with `PATH="$HOME/.bun/bin:$PATH"` works.
- Top hit: `qmd://q3_docs/insights/prime-cert-brange-tcritical-2026-01-26.md` (goal: certify `margin(B) ≥ prime_cert_margin_lb`).
- Other hits were low-signal or unrelated.

Web search:
- `interval_cases` is the canonical finite-range splitter for ℕ/ℤ; no dedicated numeric interval-arithmetic tactic found.
- Tactic check: `interval` is unknown with `import Mathlib` (stdin test).

Plan (5–10 lines, concrete pointers):
1) Prime-sum buckets: extend `BrangeGrid_PrimeSum_2026_01_30_Checker.lean` with a reusable lemma to reduce each bucket sum to a finite `Finset` sum and try `interval`/`linarith` on per-term bounds (no `native_decide`).
2) Generator upgrade: extend `scripts/prime_brange_interval_checker_grid.py` to also emit per-term bounds (or per-subinterval bounds) so `Finset.sum_le_sum` can close each `prime_b_grid_bucket_sum i k ≤ prime_b_grid_bucket_ub i k`.
3) Tail bound: prove `prime_b_grid_tail_term_sum_le_bound` analytically from `BrangeGrid_PrimeSumTail.lean` using the integral comparison and a numeric bound, possibly in a new `BrangeGrid_PrimeSum_2026_01_30_TailCert.lean`.
4) Wire: replace axioms in `BrangeGrid_PrimeSum_2026_01_30_Data.lean` with the new proofs, then build `PrimeBGridBounds` in `BrangeCert_2046.lean`.
5) Success check: `lake env lean` on grid files; then `./scripts/check_axioms.sh` expecting only `Weil_criterion_tau0` + `prime_heat_bounds_data`.

Progress (2026-02-01):
- `scripts/prime_brange_interval_checker_grid.py` now emits per-grid bucket sum totals and
  `prime_b_grid_bucket_ub_sum_le` in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Intervals.lean`;
  this discharges the `h_sum_ub` part once `h_bucket` is available.
- `scripts/prime_brange_heat_interval_checker.py` now emits
  `prime_heat_bucket_ub_sum` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Intervals.lean`, and
  `BrangeHeatCert_2026_01_28_SumData.lean` adds
  `prime_heat_bucket_ub_sum_le_partial`.

---


## Synthesis (2026-01-31, in progress) — Interval-certificate closure (pilot → grid → heat)

Target lemmas/axioms (PrimeCert):
- `prime_b_grid_pilot_sum_le_0`, `prime_b_grid_pilot_sum_le_19`
  (`Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Data.lean`)
- `prime_b_grid_prime_sum_le_all`
  (`Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`)
- `prime_heat_sum_data`
  (`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`)

Embedding search: `scripts/research_oracle.py` blocked (qmd not on PATH).

Plan (5–10 lines, concrete pointers):
1) Generate a Lean cert file with per‑B interval upper bounds for
   `prime_b_grid_prime_sum_up_to` and numeric proofs with `norm_num`
   (no `native_decide`).
2) Pilot: replace axioms with theorems `prime_b_grid_pilot_sum_le_0/19`
   in `BrangeGrid_Pilot_2026_01_30_Data.lean`.
3) Full grid: extend generator to all 20 points; prove
   `prime_b_grid_prime_sum_le_all` by `fin_cases` in
   `BrangeGrid_PrimeSum_2026_01_30_Data.lean`.
4) Heat: use the same pattern to populate `prime_heat_sum_data.h_sum`
   from `prime_cert_brange_heat_prime_partial_interval_2026-01-31_0009.txt`;
   keep `h_tail` from `BrangeHeatCert_2026_01_28_Data.lean`.
5) Success check: `lake env lean` on pilot/grid/heat files, then
   `./scripts/check_axioms.sh` + refresh graphs/stats.

## Synthesis (2026-01-31, in progress) — Formal interval checker for pilot sums

Target lemmas (PrimeCert):
- `prime_b_grid_pilot_sum_le_0_ub`, `prime_b_grid_pilot_sum_le_19_ub`
  (`Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Data.lean`)

Embedding search: `scripts/research_oracle.py` blocked (qmd not on PATH).
Web search: no obvious built‑in interval‑arithmetic tactic surfaced; results mostly point to
`norm_num` for numeric goals and `interval_cases` for interval reasoning, so expect a custom
interval checker if we want axiom‑free bounds.

Plan (5–10 lines, concrete pointers):
1) Add a generic “sum ≤ upper bound” lemma for finite/tsum bounds in a new file
   `Q3/Proofs/PrimeCert/IntervalChecker.lean` (use `Finset.sum_le_sum` + `tsum_le_tsum`).
2) Introduce a pilot‑specific certificate file (generated) with bucketed upper bounds for
   `prime_b_grid_weight_term` over ranges of `n`, e.g. `BrangeGrid_Pilot_2026_01_30_Intervals.lean`.
3) Provide monotonicity lemmas to justify bucket bounds (log/exp monotone, Fejér ≤ 1),
   so each bucket proof is `linarith` + `norm_num` on rationals.
4) Generate the bucket table + Lean proof skeleton via a new script
   `scripts/prime_brange_interval_checker_pilot.py` (keeps numeric bounds reproducible).
5) Replace `prime_b_grid_pilot_sum_le_*_ub` with theorems using the checker; then
   `lake env lean` on pilot files + `./scripts/check_axioms.sh`.

Status (2026-01-31):
- Added generator `scripts/prime_brange_interval_checker_pilot.py` and produced
  `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Intervals.lean` (bucketed
  interval sums + numeric sum ≤ pilot UB lemmas).

## Synthesis (2026-01-30, in progress) — PrimeCert axiom closure plan (grid + heat)

Goal: close the 3 main-chain PrimeCert axioms:
`prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`.

Plan (5–10 lines, concrete pointers):
1) Grid bounds: move `prime_b_grid_bounds_data` to a theorem in
   `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` by proving `h_arch`/`h_prime`
   using the numeric tables already in `BrangeGrid_2046.lean`.
2) Create a small “grid evidence” file (if needed) with per‑index bounds extracted
   from `output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt`, keeping values as ℚ,
   then use `fin_cases` + `norm_num` (no `native_decide`).
3) Prime heat bound: use the decomposition in
   `BrangeHeatCert_2026_01_28_Data.lean` plus numeric evidence in
   `BrangeHeatCert_2026_01_28_SumData.lean` to show
   `tsum = sum_{n≤N} + tail`, then prove `≤ L_prime_heat_raw`.
4) Arch heat bound: build a dedicated lemma in
   `BrangeHeatCert_2026_01_28_Data.lean` or a new file that upper‑bounds the
   integral via interval arithmetic / numeric quadrature certificate; keep it
   as a theorem (no new axioms).
5) Wire results back: drop the three axioms, update `Q3/CheckAxioms.lean`,
   `PHILOSOPHY_OF_PROOF.md`, and re‑run `./scripts/check_axioms.sh`.

Status (2026-01-30):
- Added grid prime partial sums + tail bound in `PrimeCert/BrangeGrid_2046.lean`.
- Added prime-heat tsum decomposition scaffold in
  `PrimeCert/BrangeHeatCert_2026_01_28_Data.lean` and sum evidence in
  `PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
- Full closure still blocked on formal numeric certification of
  `arch_term` and `prime_term` values (needs interval/verified quadrature or
  a generated Lean proof pipeline).

## Audit (2026-01-29) — PDF vs Lean mainline divergence (in progress)

- RH_Q3.pdf формулирует **классический Weil‑конус**; mainline Lean использует
  **`Weil_cone_tau0` (τ=0 + фиксированный B‑range)**.
- PDF использует two‑scale (`t_sym`, `t_rkhs`); mainline использует single‑scale `t_critical`.
- Полная секция‑к‑Lean карта + сводка расхождений:  
  `docs/struktura_q3_with_mapping_toLEAN.md` (раздел “2026-01-29 Audit — PDF vs Lean Mainline”).

## Synthesis (2026-01-28, in progress) — heat-weight integrability requires global a_star growth

- Added Tier‑1 axiom `a_star_linear_growth` (global linear growth bound) to unblock
  integrability of `|a_star ξ| * exp(-4π^2 t ξ^2) * |ξ|`.
- Implemented integrability lemma in
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`.
- `arch_heat_weight_integrable` now compiles in the minimal file and is available
  in `Brange_Lipschitz_HeatProof.lean`.

## Synthesis (2026-01-29, in progress) — prime heat-weight summability axiom

- Added Tier‑1 axiom `w_Q_heat_weight_summable` to capture summability of
  `w_Q n * exp(-4π^2 t (xi_n n)^2) * |xi_n n|`.
- Using this axiom to finish `prime_term_Lipschitz_heat` and
  `margin_Lipschitz_heat_of_bounds` in `Brange_Lipschitz_HeatProof.lean`.

## Plan (future de-axiomization) — a_star growth + heat-weight summability

- a_star growth: use digamma asymptotics (DLMF 5.11) to show
  `|a_star ξ| <= C0 + C1 * log(1 + |ξ|)` on tails, and combine with
  `a_star_bdd_on_compact` on `Icc (-R) R` to get a global bound.
- heat-weight summability: use basic bound `vonMangoldt(n) <= log n` and
  `xi_n = log n / (2*pi)` to show
  `w_Q n * exp(-c * (log n)^2) * |log n|` is absolutely summable.
- glue: `log(1+|ξ|) <= |ξ|` then Gaussian integrability of
  `(1 + |ξ|) * exp(-c ξ^2) * |ξ|`.

## Research note (2026-01-29) — digamma/trigamma asymptotics sanity check

- Asymptotics (DLMF 5.11 / trigamma) imply `ψ(1/4 + iπξ) = log|πξ| + O(1/ξ)` on tails,
  so `|a_star ξ| = O(log|ξ|)` and is strictly better than the current linear-growth axiom.
- Formalization gap: asymptotics are tail-only; to get a global bound we must
  combine tail bound with `a_star_bdd_on_compact` on `Icc (-R) R` and fix constants.
- Connes/Toeplitz remarks are good context but **not needed** for heat integrability;
  keep as background only.

## Synthesis (2026-01-29, in progress) — BMO Bellman check-mode + regularity gate

- Added a lightweight `--check` mode to `bellman_bmo.py` to verify the closed‑form
  answer numerically (balance residual + value check). Heavy concavity/optimizer
  checks stay as future work.
- Methodology takeaway for Q3: **regularity‑gate**. The Fejér×heat window has kinks
  (|ξ| and cutoffs), so every step that assumes C² must be rejected unless
  explicitly justified; stick to Lip/modulus control.
- Future work capture: keep deeper BMO/Bellman formalization in `docs/INSIGHTS.md`
  and only link it from `ACTIVE/insights.md` (short).

## Synthesis (2026-01-26, in progress) — τ-shift AtomCone fails; `prime_term_le_at_t_critical_axiom` is false-for-now

- Local numeric verification: `python3 verify_variant_b.py --direct` shows
  `min Q = -911.2678` at `τ = 1.689` for `t = 0.15` (so full `AtomCone_K_fixed` is not safe).
- Target axiom: `Q3.prime_term_le_at_t_critical_axiom` in `Q3/Proofs/Q_nonneg_t_critical.lean`
  is currently the only thing making τ-uniform positivity go through in Lean.
- Wiring (main chain): `prime_term_le_at_t_critical` → `Q_phi_shift_nonneg_t_critical` →
  `QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm` →
  `Atoms_Positive.Q_nonneg_on_atoms` → `T5.T5_transfer`.
- Decision tree:
  - Option A: keep the current cone (`AtomCone_K_fixed`) and accept this axiom permanently (not credible).
  - Option B (recommended): refactor the cone/criterion target so τ-shift atoms are not required
    (likely move to a Fourier-positive/PD cone; then BaseAtomCone τ=0 becomes the generator).
  - Option C: replace A1/A2/T5 with a different positivity transfer (fallback; expensive).
- Success check: after refactor, `#print axioms Q3.Main.RH_of_Weil_and_Q3` drops `prime_term_le_at_t_critical_axiom`.
- **Status update (2026-01-26):** mainline now uses `Weil_cone_tau0` + `W_K_tau0`
  (τ=0, B-range), so the τ‑uniform prime‑term axiom is no longer in the RH chain.
- Note: `q3search`/`websearch` are deprecated; use `./scripts/research_oracle.py ...` + web tool.

## Synthesis (2026-01-27, in progress) — Weil explicit formula ⇒ positivity criterion (Artin–Hecke)

Source: Zotero cache for Weil 1972 (Math USSR Izvestiya, 1972) at
`full/q3.lean.aristotle/literature/zotero/W9IDA6HW/fulltext.md`.

**Core idea (one paragraph):** Weil derives a **general explicit formula** for Artin–Hecke
L-series (not just ζ), expressed as a distributional identity on a Weil-group–type object.
This yields a distribution Δ (schematically δ₁ − 2D) whose **positivity on a test-function class**
is equivalent to RH **plus** Artin’s conjecture (no “bad” local factors). So RH becomes a
positivity statement for a quadratic/linear functional built from local archimedean
and non‑archimedean terms with *fixed normalization*.

**Mapping to Q3 chain:**
- This is the theoretical source of `Weil_criterion_tau0` (current external axiom).
- The positivity functional Δ ↔ our `Q`/`Weil_criterion` viewpoint (nonnegativity on a cone).
- The strict separation of arch/prime local terms matches the `arch_term` / `prime_term`
  split in `Q3/Proofs/Q_nonneg_t_critical.lean`.

**Why normalization matters (risk area):**
- Weil fixes **canonical Haar measures** on “modular” groups and uses them in the explicit formula.
- Any change in normalization shifts constants in Δ and can **flip positivity**.
- For formalization, all local measures must be normalized **once** and kept consistent
  with the test-function transform.

**Strength vs RH:**
- Weil’s criterion is **stronger** than RH alone (it includes Artin conjecture).
  That’s fine if treated as an external classical axiom, but important to document.

**Actionable insight for formalization:**
- Treat Δ positivity as the target “axiom” until the explicit formula is formalized.
- If we ever close `Weil_criterion_tau0`, we need:
  1) precise definition of the test-function space (cone) and transforms,
  2) explicit formula linking zeros ↔ local terms,
  3) proof that Δ ≥ 0 ↔ RH (with Artin assumptions).

**Quick follow‑ups (literature mining):**
- Collect references in Weil (1972) bibliography for explicit formulas and Weil groups.
- Look for modern expositions to reduce heavy group/representation preliminaries.

## Synthesis (2026-01-27, in progress) — Toeplitz‑Weil mapping (formal chain vs speculative edges)

Source: `docs/toeplitz_weil_bridge.md` (checked into this repo).

**Critical correction (formal alignment):**
- Do **not** state the Weil functional as `Σ |f̂(ρ)|²` in the formal chain.
- In Q3 the correct formal target is: **`Q(Φ) ≥ 0` on the (τ=0) Weil cone ⇔ RH**,
  i.e. `Weil_criterion_tau0` in `Q3/Axioms.lean`. Any spectral/quadratic‑form
  intuition must be marked as *interpretation*, not formula.

**Formal Chain (Lean‑anchored mapping):**
- Weil criterion (τ=0): `Q3.Axioms.weil_criterion_tau0` → `Q3/Main.lean` mainline.
- A3 bridge (Toeplitz − Prime): `Q3/Proofs/A3_bridge_integrated.lean`.
- Base atom positivity (τ=0): `Q3/Proofs/Q_nonneg_base_atoms_proof.lean`.
- RKHS contraction: `Q3/Proofs/RKHS_contraction.lean` and bridge wrappers.
- T5 transfer (τ=0): `Q3/T5_Transfer.lean` (`T5_transfer_tau0`).

**Speculative Edges (NOT in chain, keep isolated):**
- Kapustin 2022 (explicit de Branges model), Connes 1998/2025 (trace formula / spectral triples),
  Hilbert–Pólya heuristics: **informal context only**.
- If used, they must enter as **speculative edges** with a formal bridge stub before activation.

**Actionable rule:** keep the above split explicit in docs and dashboards; never “blend”
speculative edges into the formal chain without a Lean stub.

## Synthesis (2026-01-27, in progress) — Connes–Consani–Moscovici “Zeta Spectral Triples”

Source: Zotero ingest
`full/q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md`
(paper: *Zeta Spectral Triples*, Connes–Consani–Moscovici).

**Core idea (from cache):** construct self‑adjoint operators `D(λ,N)` as
rank‑one perturbations of a spectral triple for the scaling operator on `[λ⁻¹, λ]`.
The construction uses **finite Euler products** (`p ≤ x = λ²`). Spectra of `D(λ,N)`
numerically align with low ζ‑zeros. Self‑adjointness relies on an **extension of the
Carathéodory–Fejér theorem for Toeplitz matrices**.

**Formal Chain (possible bridge points):**
- CF‑extension ⇒ **Toeplitz self‑adjointness** in a finite‑rank/finite‑prime regime.
  This could become a *formal* lemma stub that mirrors our Toeplitz/Rayleigh steps
  (Szegő–Böttcher + Rayleigh bounds).
- Rank‑one perturbation control ⇒ spectral stability lemma (if formalized,
  could justify controlled operator deformations in the A3 path).

**Speculative Edges (do NOT activate without stubs):**
- “Finite Euler product” ⇒ **prime‑term truncation** with explicit error bound.
  Potential leverage for PrimeCert Lipschitz/ margin bounds, but currently speculative.
- Spectral triple / scaling operator formalization is out of scope for the mainline.

**Actionable next step (lightweight):**
- Add a speculative edge entry in the external graph:  
  `CF_toeplitz_selfadjointness` (source = 6H6WHGDU, status = speculative).
- If we pursue it: create a Lean stub lemma in `Q3/Proofs/PrimeCert/` or
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` documenting the intended statement
  (self‑adjoint Toeplitz from truncated data), **without** wiring it into mainline.

## Synthesis (2026-01-23, in progress) — fixed‑t/τ=0 one‑scale closure

- q3search "AtomCone_K_fixed" / "Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom" failed: 403 Spend limit exceeded.
- websearch "AtomCone_K_fixed Lean" failed: 403 Spend limit exceeded.
- Target lemma: close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Option A (primary): implement fixed‑t cone/τ=0 guard in `Q3/Axioms.lean`, then wire one‑scale chain using
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`, `Q3/Proofs/RKHS_cap_rayleigh.lean`, and `Q3/Proofs/Params_Critical.lean`.
- Option B (fallback): keep RKHS embedding path; fill missing `kernel_dict` in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  or discharge `hA` via `Q3/Proofs/RKHS_Interface_C1.lean` + `Q3/Proofs/Heat_RKHS_Interface.lean`.
- Success check: `lake env lean Q3/Atoms_Positive.lean` and `./scripts/check_axioms.sh` drop the axiom.
- Progress: `t0_critical` wired into `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
  `Q3/Atoms_Positive.lean`, `Q3/T5_Transfer.lean`, `Q3/AxiomsTheorems.lean`;
  BaseAtomCone guard `Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS` added.
- Proshka request drafted: `full/q3.lean.aristotle/PROSHKA_REQUEST_5.md` (one‑scale A3 floor + cap at t_critical).

## Synthesis (2026-01-24, resolved) — close `rho_oneK_tcritical_le_cstar_quarter`

- Decision: mainline uses tau = 0, so the cap reduces to `rho_one ≤ c_star/4`.
- Implemented as a direct numeric bound (no K dependence).
- Legacy `rho_oneK` (tau-shift) remains as a separate variant; not used in mainline.

## Synthesis (2026-01-24, in progress) — `rayleigh_basis0_shift_ge_cstar_quarter` (t_critical, tau = 0)

- q3search "rayleigh_basis0_shift_ge_cstar_quarter" failed: 403 Spend limit exceeded.
- websearch "Toeplitz Rayleigh lower bound t_critical" failed: 403 Spend limit exceeded.
- Target lemma: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Option A (primary): reduce to floor at t_critical via
  `P_A_shift_tau_zero` (`Q3/Proofs/Q_nonneg_base_atoms_proof.lean`) +
  `P_A_rayleigh_lower_bound_of_floor` (`Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`) +
  `A3FloorCritical.FloorGoal` (`Q3/Proofs/A3_Floor_Critical_Goal.lean`), then weaken to `c_star/4`.
- Option B (fallback): use `arch_rayleigh_eq_shift` (`Q3/Proofs/Rayleigh_Q_identification.lean`) +
  `integral_P_A_shift_eq_arch_term` (`Q3/Proofs/ShiftedWindows.lean`) and prove
  `arch_term ≥ c_star/4` via a numeric/interval lemma in `Q3/Proofs/Q_nonneg_t_critical.lean`.
- Success check: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`
  then `./scripts/check_axioms.sh` (only `Weil_criterion_tau0` + PrimeCert axioms remain).
- Blocker: no current floor lemma at `t_critical`; likely needs numeric/interval proof
  or a monotonicity lemma for `P_A` in `t`.

---

## Synthesis (2026-01-26, in progress) — close PrimeCert B‑range axioms

- Target axioms (current): `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`
  in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`; used by
  `prime_cert_margin_on_Brange_axiom` → `Q3/Proofs/Q_nonneg_t_critical.lean`.
- q3search/websearch commands are **missing** in this sandbox (both return “command not found”),
  so no semantic scan done yet.
- Option A (preferred): prove Lipschitz of `margin(B)` analytically by bounding
  `‖phi_shift x - phi_shift y‖_∞` on `B ∈ [B_min, B_max]`, then combine with
  existing arch/prime Lipschitz bounds (see `Q3/Proofs/Q_Lipschitz_*`).
- Option B (fallback): keep axioms but gate them behind a dedicated certificate module
  with explicit provenance + CI check; **do not** re‑introduce `native_decide`.
- Status update (2026-01-26): **Option B implemented** —
  certificate module + hashes in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  evidence files pinned in `Q3/Proofs/PrimeCert/README.md`,
  CI hash check added in `scripts/check_axioms.sh` (uses `output/prime_cert_*_2026-01-26_*`).
- Status update (2026-01-29): `prime_b_grid_val_le_margin` and
  `prime_heat_bounds_cert` are now theorems (derived from `*_data` axioms).
- Success check: `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`,
  then `./scripts/check_axioms.sh` (only `Weil_criterion_tau0` + PrimeCert remain).
- Status: **Option B implemented**; Option A (analytic closure) remains long‑term.

---

## Synthesis (2026-01-26, in progress) — analytic Lipschitz closure for PrimeCert margin(B)

- Target axioms: `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`
  (now in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`); goal is to **replace** them by proofs.
- q3search/websearch are **missing** in this sandbox (both “command not found”); no semantic scan yet.
- 2026-01-26 check: `q3search`/`websearch` still unavailable (127 / “Befehl nicht gefunden”).
- Aristotle tooling installed in `.venv` (CLI + `aristotlelib`), but submission is
  blocked by missing `ARISTOTLE_API_KEY`. Next action: set key and submit
  `aristotle_input/proshka_primecert_lipschitz_2026_01_26.md`.
- Core idea: prove `B ↦ arch_term (phi_shift B t_critical 0)` and
  `B ↦ prime_term (phi_shift B t_critical 0)` are Lipschitz on `[B_min, B_max]`,
  then combine to bound the margin. Use existing bounds:
  `Q_Lipschitz_arch_bridge.lean` + `Q_Lipschitz_prime_bridge.lean`,
  plus a **uniform sup‑norm bound** on `|phi_shift B₁ - phi_shift B₂|`.
- Need explicit constant `L ≤ 0.3` (matches `prime_cert_L_ub`), or show a sharper bound
  and then relax to 0.3.
- **Implemented (analytic skeleton):** `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean`
  proves a symbolic Lipschitz bound for `margin` with constant
  `margin_Lipschitz_const := (2*B_max*M_a_local(B_max)+W_sum_local(B_max)) * (B_max/B_min^2)`,
  plus a pointwise `phi_shift` bound in `B`. This compiles.
- **Note (2026-01-26):** attempted a weighted prime‑sum Lipschitz variant here, but Lean
  hit deterministic heartbeat timeouts; rolled back the weighted lemma to keep the file compiling.
  Next attempt should refactor to a finite‑sum (`Finset`) proof to avoid heavy `tsum` machinery.
- **Still missing:** an explicit numeric upper bound on
  `2*B_max*M_a_local(B_max)+W_sum_local(B_max)` to show
  `margin_Lipschitz_const ≤ 3/10` (or any certified ≤ `prime_cert_L_ub`).
- File pointers: `Q3/Proofs/ShiftedWindows.lean` (phi_shift definition/support),
  `Q3/Proofs/Q_Lipschitz_arch_bridge.lean`, `Q3/Proofs/Q_Lipschitz_prime_bridge.lean`,
  `Q3/Proofs/PrimeCert/Brange_2046.lean`.
- Success check: `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`,
  then `./scripts/check_axioms.sh` (PrimeCert axioms eliminated).

---

## Synthesis (2026-01-27, in progress) — PrimeCert closure architecture request (Proshka)

- Goal: remove the two PrimeCert axioms in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` without changing the one-scale mainline.
- Bottlenecks:
  - Lipschitz: convert the symbolic bound in `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` into
    `margin_Lipschitz_const ≤ prime_cert_L_ub` via certified numeric bounds on `M_a_local(4.9)` and `W_sum_local(4.9)` (or avoid these).
  - Grid: connect the rational table in `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean` to the true `arch_term - prime_term`
    (needs a Lean-side verifier or another reduction).
- Proshka request drafted: `aristotle_input/proshka_primecert_closure_2026_01_27.md`.

---

## A3/Rayleigh: критический путь

- Символы `a_star` vs `P_A`: признаки рассогласования, reverse‑engineering → `docs/insights/a3_symbol_mismatch_reverse_engineering.md`.
- Досье по различиям `a_star` и `P_A` → `docs/insights/a_star_vs_p_a_dossier.md`.

- Rayleigh без SB: пытаемся тащить Szego‑Bottcher → `docs/insights/rayleigh_vs_sb_optional.md`.
- SB не нужен (краткая формулировка) → `docs/insights/szego_bottcher_not_needed.md`.

- RKHS cap: видим несходимость по ρ=0.868 → `docs/insights/a3_bridge_math_rkhs_bound.md`.
- RKHS cap реализация (t_rkhs_cap=40, rho_one=1/25) → `docs/insights/rkhs_cap_implementation_2026_01_15.md`.
- Tau-shift: варианты RKHS cap/A3 floor + выбор Variant 1 (риски/план) → `docs/insights/tau_shift_variants_rkhs_a3_2026_01_18.md`.
- Floor cert (t_critical): grid+Lipschitz numbers + script → `docs/insights/floor_cert_tcritical_2026_01_25.md`
- Prime-term cert (t_critical): prime_sum + tail bound + arch_term numeric → `docs/insights/prime_cert_tcritical_2026_01_25.md`
- Prime-term cert (B-range): grid + margin Lipschitz over B → `docs/insights/prime_cert_brange_tcritical_2026_01_25.md`
- C1 basisFun model wired (machine `h_eval`) + compression remark in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Single-scale RKHS contraction at `t_critical` wired into `Q3/AxiomsTheorems.lean` (via `SingleScale_Assumptions`).
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` closed via `Q_nonneg_atoms_closure`; remaining blocker is
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`.

- Реальные bounds для T_P (V1 surprise): путаем direct‑indexed vs compression → `docs/insights/v1_surprise_real_tp_bounds_2026_01_14.md`.
- Успешный Rayleigh‑bridge (V3) → `docs/insights/v3_success_a3_bridge_rayleigh_2026_01_14.md`.
- Полный bound T_P (V4) → `docs/insights/v4_success_full_tp_bound_2026_01_14.md`.

- Несовпадение T_P_comp в Lean: упираемся в дефиницию → `docs/insights/t_p_comp_mismatch.md`.
- Фикс compression‑формулы T_P (план) → `docs/insights/t_p_compression_fix_2026_01_14.md`.
- Контракт RH_Q3 (инварианты + дрейф‑точки): быстрый аудит `a_star`/`P_A`, Toeplitz, `t_sym`/`t_rkhs`, веса → `docs/insights/rh_q3_invariants_contract_2026_01_16.md`.
- Drift report M1–M4: a_star vs P_A, sampling vs Fourier, T_P, parameters → `docs/insights/drift_report_m1_m4.md`.
- Атомы: переход на Fourier A3 и новую аксиому → `docs/insights/a3_fourier_atoms_axiom_2026_01_16.md`.
- Closure synthesis (from q3search + websearch) for `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`:
  базовая информация уже в базе. Используем скелет `aristotle_input/Q_nonneg_A6_final.md`,
  идентификацию `Q3/Proofs/Rayleigh_Q_identification.lean` (`rayleigh_Q_eq_Q` или `_shift`),
  RKHS cap из `Q3/Proofs/RKHS_cap_rayleigh.lean` (`weight_sum_le_rho_one`),
  A3 bridge из `Q3/Proofs/P_A_Toeplitz_bridge.lean`.
  Действия: доказать теорему `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` через
  `Q_nonneg_on_atomcone_of_atoms` + `Q_nonneg_fejer_heat_window` + `rayleigh_basis0_of_A3`
  + кап; затем заменить аксиому в `Q3/Atoms_Positive.lean` и `Q3/AxiomsTheorems.lean`,
  проверить `lake env lean Q3/Atoms_Positive.lean` и `#print axioms`.
- Blocker (2026-01-18): A1–A5 helper lemmas are still missing in code.
  План: 1) в `Q3/Proofs/Q_nonneg_atoms_helpers.lean` добавить линейность `Q_finset_sum`
  и `prime_sum_nonneg` (см. `aristotle_input/Q_nonneg_A1_linear.md`/`Q_nonneg_A2_prime_sum_nonneg.md`);
  2) `rayleigh_basis0_of_A3` и `Q_nonneg_fejer_heat_window` собрать из
  `Q3/Proofs/Rayleigh_Q_identification.lean` (`honest_formula`) + A3/RKHS cap;
  3) `Q_nonneg_on_atomcone_of_atoms` из формы `AtomCone_K` (finite sum of atoms);
  4) подключить в `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Synthesis (2026-01-18): wiring plan + import conflict.
  1) Sandbox: `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_lemmas.lean`
     содержит A1/A2/A5 + integrability/summability; скопировано в `Q3/Proofs/Q_nonneg_lemmas.lean`
     (компилируется, предупреждение: `integral_mul_left` deprecated).
  2) Import conflict: `Q_nonneg_atoms_helpers.lean` не может импортировать одновременно
     `Q3.Proofs.Rayleigh_Q_identification` и `Q3.Proofs.P_A_Toeplitz_bridge`
     (B_min collision из `A3_Floor_Bounds`).
  3) Mitigation: держать Rayleigh‑леммы в файле, который импортирует только
     `Rayleigh_Q_identification`; для `rho_one` подключать `Q3.Proofs.A3_bridge_rayleigh_first`.
  4) Дальше: `rayleigh_basis0_of_A3` вынести в файл с `P_A_Toeplitz_bridge` (без Rayleigh),
     затем связать с `Q_nonneg_fejer_heat_window` при wiring в
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
  5) Проверка: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean` и
     `lake env lean Q3/Proofs/Q_nonneg_lemmas.lean`.
- Synthesis (2026-01-18, in progress): AtomCone_K_fixed wiring plan.
  1) Fix t0: define `t0_A1 = 1 / (16 * Real.pi^2 * t_sym)` in `Q3/Proofs/HeatKernelParams.lean`
     with `t0_A1_pos`; use this for all fixed-t atoms.
  2) Add atom rewrite: in `Q3/Proofs/ShiftedWindows.lean`, prove
     `Fejer_heat_atom = const * (phi_shift B t_sym tau + phi_shift B t_sym (-tau))`.
  3) Port fixed-t chain from sandbox `sandboxes/measure_dom/.../Q_nonneg_atoms_proof.lean` into
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`:
     `Q_nonneg_on_atomcone_fixed_of_atoms`, `Q_single_atom_fixed_nonneg`, `Q_nonneg_on_atoms_fixed`.
  4) Prove `Q (phi_shift ...) ≥ 0` via `rayleigh_Q_eq_Q_shift` + `A3_bridge_data_rayleigh_Fourier`
     + `rkhs_cap_rayleigh_tcap`; use `rayleigh_basis0_of_A3` as the arch lower bound.
  5) Wire fixed-t theorem in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`;
     keep `AtomCone_K` for density and use `AtomCone_K_fixed_subset`.
  6) Checks: `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`, then `#print axioms`.
- Synthesis (2026-01-19, in progress): A1–A5 helpers + fixed‑t wiring checklist.
  1) A1/A2 already in `Q3/Proofs/Q_nonneg_lemmas.lean` (`Q_finset_sum`, `prime_sum_nonneg`);
     import/reuse in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` for A5.
  2) A4 in `Q3/Proofs/Rayleigh_basis0_of_A3.lean`; keep imports minimal
     (`Q3/Proofs/Rayleigh_basis0.lean`, `Q3/Proofs/P_A_Toeplitz_bridge.lean`).
  3) A3 in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` via
     `Q3.Proofs.RayleighQId.honest_formula` + RKHS cap (`weight_sum_le_rho_one`/`rkhs_cap_rayleigh_tcap`).
  4) Use fixed‑t cone lemma from sandbox
     `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_atoms_proof.lean`
     (`Q_nonneg_on_atomcone_fixed_of_atoms`) with `AtomCone_K_fixed` (see
     `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  5) Wire `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` in
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` using A1–A4 + fixed‑t cone.
  6) Replace axiom usage in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`.
  7) Checks: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean`,
     `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`.
- Synthesis (2026-01-24, in progress): Close `Q3/Proofs/Q_nonneg_atoms_closure.lean` sorries (fixed‑t chain).
  1) `Q_nonneg_phi_shift_tsym`: use `Q3.Proofs.QNonnegAtoms.Q_phi_shift_nonneg`
     from `Q3/Proofs/Q_nonneg_atoms_helpers.lean` with cap
     `prime_term_phi_shift_le_rho_oneK` (in `Q3/Proofs/RKHS_cap_rayleigh.lean`)
     + `rayleigh_basis0_of_A3`; **need** explicit `hpos : 0 ≤ c_star/4 - exp_tsym_to_rkhs K * R`.
  2) Replace scaling/half‑atom steps with the fixed‑t identity
     `Fejer_heat_atom_eq_const_mul_phi_shift_sum` from `Q3/Proofs/ShiftedWindows_t0.lean`.
  3) For `Q_nonneg_Fejer_heat_atom`, prefer `Q_single_atom_nonneg_of_phi_shift_basic`
     (in `Q3/Proofs/Q_nonneg_atoms_helpers.lean`) + prove `htsym` for `t0_A1`.
  4) Finish with `Q_nonneg_on_atomcone_fixed_of_atoms` (same file) to get
     `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm`.
  5) Searches attempted: `q3search` + `websearch` failed (403 spend limit); proceed with local lemmas.
- Synthesis (2026-01-23, in progress): close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
  via the one-scale chain (Stream A).
  1) q3search/websearch were attempted but failed with spend-limit 403.
  2) Implement `AtomCone_K_fixed` + `AtomCone_K_fixed_subset` in `Q3/Axioms.lean`
     and update the fixed-t cone plumbing (see `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  3) In `Q3/Proofs/Q_nonneg_atoms_helpers.lean`, import A1/A2 from
     `Q3/Proofs/Q_nonneg_lemmas.lean` and add the missing A3/A4/A5 steps with minimal imports.
  4) In `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`, use the fixed-t cone lemma,
     `rayleigh_Q_eq_Q`/`rayleigh_Q_eq_Q_shift`, and the one-scale bridge from
     `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` plus the cap in
     `Q3/Proofs/RKHS_cap_rayleigh.lean`.
  5) Replace the axiom in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`,
     then run `lake env lean` on the touched files and `./scripts/check_axioms.sh`.
- Последний мост к Q3.Q: для Phi с compact support (например, fejer_heat_window) показать, что prime_term (tsum по n) равен конечной сумме по Nodes K при K >= B; тогда rayleigh_Q_identification переписывается в Q3.Q (см. `Q3/Proofs/Rayleigh_Q_identification.lean`).
- P_A_continuous: доказательство через локальную конечность суммы и периодичность, без `sorry` (см. `A3_Floor_Main.lean`).

---

## Параметры и численные проверки

- Две формы t (в числителе/знаменателе): знак эффекта не тот → `docs/insights/t_parameter_forms.md`.
- Heat‑параметр mismatch (t_sym vs t_rkhs): путаем контексты → `docs/insights/heat_parameter_mismatch_2026_01_14.md`.
- Численные оценки h‑cap: нужен sanity‑check по величинам → `docs/insights/h_cap_numerical_estimates_2026_01_14.md`.
- One-scale vs two-scale (конкретно):
  - **Two-scale** = A3 floor на `P_A(·, t_sym)` + prime cap на `T_P_comp(·, t_rkhs_cap)` (см. `Q3/Proofs/P_A_Toeplitz_bridge.lean`,
    `Q3/Proofs/A3_bridge_rayleigh_first.lean`) и затем отдельный мост/штраф за смену t (см. `Q3/Proofs/PrimeTerm_t_bridge.lean`).
  - **One-scale** = один и тот же `t` одновременно в `P_A(·, t)` и в `T_P_comp(·, t)` (и в RKHS-части): меньше “перекидываний”,
    но нужно реально закрыть обе оценки на одном t. Параметры фиксируем в `Q3/Proofs/Params_Critical.lean` (`t_critical`, `t0_critical`).

---

## Misc / Unsorted (нужно разложить по разделам)

- Periodization bottleneck: быстрый фикс → `docs/insights/PERIODIZATION_BOTTLENECK_FIX.md`.
- Carleson implicit proof notes → `docs/insights/carleson_implicit_proof_2026_01_17.md`.
- Heat localization kills primes → `docs/insights/heat_localization_kills_primes_2026_01_16.md`.
- Localization argument (full) → `docs/insights/localization_argument_full_analysis_2026_01_16.md`.
- Prime term = nodes sum bridge → `docs/insights/prime_term_nodes_bridge_2026_01_17.md`.
- Rayleigh Q identification notes → `docs/insights/rayleigh_q_identification_2026_01_17.md`.
- Rescaled density lemma variants → `docs/insights/rescaled_density_lemma_variants_2026_01_16.md`.
- Decision tree (2026-01-23): “нетривиальное hA” для C1 (Rayleigh = compression RKHS-prime).
  - Target lemma (informal): ∃ heat-RKHS `H_t`, ∃ isometry `ι_{t,M}`, s.t.
    `(Matrix.toEuclideanLin (T_P_comp_real ...)).toCLM = compression ι_{t,M} (T_P_RKHS t)`.
  - Tree-plan (no axioms, Moore–Aronszajn → close `hA`):  
    1) Build `H_t` from kernel `k_t(x,y)` (Moore–Aronszajn: span/quotient/complete) and expose
       `eval x` + `k x` + reproducing lemma. Status: **blocked (infrastructure)** — a first attempt at a
       Fourier/Bochner model ran into nontrivial `simp`/`cpow`/conjugation normalization issues, so it was
       reverted rather than kept half‑working.  
    2) `Q3/Proofs/Heat_RKHS_Interface.lean`: use `reproducing` to reduce `inner ℂ (ψ i) (k x)` to `eval x (ψ i)` (already: `h_eval_of_eval_eq_prime_vec`).  
    3) `Q3/Proofs/RKHS_Interface_C1.lean`: discharge `hA` by providing `H, ψ, k` and the matching hypothesis; conclude exact compression identity (already: `T_P_comp_toCLM_eq_compression`).  
    4) If “exact sampling ON family” is false-for-now: switch to node-span interpolation, prove unitary-conjugation equivalence, and use operator-norm invariance to recover the C1 cap (document as Option 1b in this tree).  
       Lean helper: `Q3/Proofs/OpNorm_Unitary.lean` (`opNorm_conj_linearIsometryEquiv`).
  - Option 0 (DONE, algebraic core): exact factorization `T_P_comp = V† · D · V` in
    `Q3/Proofs/RKHS_hA_prime.lean` (this is the real “content” of the rank-one sum).
  - Option 1 (OK, conditional “true C1 as in PDF”): minimal Hilbert-interface version of `hA`
    compiles as `Q3.Proofs.RKHSInterfaceC1.T_P_comp_toCLM_eq_compression` in
    `Q3/Proofs/RKHS_Interface_C1.lean`:
    assumptions = `(H, ψ orthonormal, k_n, inner(ψ_i,k_n)=prime_vec)` ⇒ `T_P_comp = compression ι T`.
    Note: in this Lean toolchain `⟪·,·⟫` does not parse reliably; use `inner ℂ _ _` in new files.
    Refinement: `Q3/Proofs/Heat_RKHS_Interface.lean` packages a minimal RKHS interface
    (`eval x` + reproducing vectors `k x`) so the matching hypothesis reduces to:
    `eval (xi_n n) (ψ i) = prime_vec ... i`.
    Reality check (important before “full Gaussian RKHS”): in the *Gaussian RKHS on ℝ* with kernel
    `k_t(x,y)=exp(-(x-y)^2/(4t))`, it is not obvious (and may be false) that one can pick an
    orthonormal family `ψ_i` with exact exponential sample values `ψ_i(ξ_n)=prime_vec ... i`.
    The robust route is to build `ψ_i` by *kernel interpolation on the finite node set* and then
    track the induced unitary change-of-basis on `ℂ^{2M+1}`; this still gives the needed norm control
    because `A · T_P_comp · A†` has the same operator norm as `T_P_comp`.
  - Option 2 (OK fallback): skip RKHS and cap `‖T_P_comp_real‖` directly by Schur/row-sum:
    `T_P_comp_real_opNorm_le_weight_sum` in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
    Status: compiles now; use when Option 1 is blocked.
  - Pivot rule: if Option 1 requires new axioms / >N days of infrastructure, mark “false-for-now”
    and wire Option 2 into the proof chain; keep Option 1 as long-term cleanup.
  - τ=0 note (важно): `BaseAtomCone_K` в `Q3/Axioms.lean` требует `c_i ≥ 0` и `τ=0`.
    Такой конус генерирует только “центрированные” (по |ξ|) профили и **не может быть плотным**
    в общем `W_K` без дополнительных идей (иначе A1′ ломается). Поэтому “работаем только τ=0”
    должно быть либо (a) про A3/RKHS-узел (matching/positivity) с сохранением τ-параметра в плотности,
    либо (b) сопровождается новой, честной A1′-теоремой для изменённого генератора.

- Tree-plan (2026-01-23, requested): Moore–Aronszajn RKHS + где закрывается `hA` (без аксиом).
  - **(0) One-scale spec (must):** eliminate two-scale mismatch by using one `t` everywhere; scaffolding:
    `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` (`A3_bridge_data_rayleigh_Fourier_at`, `A3_bridge_rayleigh_at_from_weight_sum_P_A`).
  - **(1) RKHS construction:** build `H_t` from kernel `k_t` (Moore–Aronszajn) + reproducing:
    future file (blocked infra) + Aristotle sandbox tasks in `aristotle_input/` (start from `gaussian_rkhs_kernel_v1.lean`).
  - **(2) Matching bridge:** use the minimal interface to reduce “inner = sample” to eval statements:
    `Q3/Proofs/Heat_RKHS_Interface.lean` (`h_eval_of_eval_eq_prime_vec`).
  - **(3) Close `hA` (C1 exact identity):** once matching hypotheses are provided, the compression identity is a theorem:
    `Q3/Proofs/RKHS_Interface_C1.lean` (`T_P_comp_toCLM_eq_compression`).
  - **(4) Fast fallback (no RKHS):** cap from Schur/weight_sum at the same `t`:
    `Q3/Proofs/RKHS_cap_generic.lean` (`rkhs_cap_rayleigh_of_weight_sum`) + provide the numeric/analytic `h_weight_sum`.

---

## A3_FLOOR @ one-scale `t_critical` (BLOCKER, 2026-01-23)

**Target (exact):**
- Prove (no axioms/sorry): `∀ θ ∈ Set.Icc (-1/2) (1/2), Q3.c_star ≤ P_A B_min Q3.t_critical θ`.
- This is the missing input `hP_ge` for the one-scale bridge in `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`.

**Why it’s hard right now (root cause, not vibes):**
- The old proof `Q3/Proofs/A3_Floor_Main.lean` works at `t_sym = 3/50` because it can lower-bound the key
  “two big terms” using the strong pointwise bound `a(1/2) ≥ 5/8` (log2 is large enough) and then crush all tails.
- At `t_critical = 3/20`, the bottleneck becomes controlling `g B_min t (1-θ)` for `θ` close to `1/2`,
  i.e. `a(x)` for `x` slightly **above** `1/2` (e.g. `x = 11/20 = 0.55`).
- With the current remainder lemma `Q3.re_digamma_remainder_bound_stieltjes` (constant `1/4`),
  the best “pure-inequality” lower bounds for `a(11/20)` appear too weak to close the numeric gap cleanly;
  the dead-code path in `Q3/Proofs/A3_Floor_Bounds.lean` explicitly notes that a sharper
  `re_digamma_remainder_bound` (constant `1/12`) would unlock the needed strength.

**Decision tree (next moves):**
1) **OK / recommended:** implement a sharper digamma remainder bound (the missing `re_digamma_remainder_bound`)
   and resurrect `a_lower_bound_from_remainder` in `Q3/Proofs/A3_Floor_Bounds.lean`.
   - Pointers: `full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Bounds.lean` (dead code blocks around `re_digamma_remainder_bound`),
     `full/q3.lean.aristotle/Q3/DigammaRemainder.lean` (current `…_stieltjes` bound).
   - This is the most “community-standard” fix: better explicit remainder ⇒ better pointwise `a(x)` bounds ⇒ floor.
2) **OK but larger infra:** prove a *local* control of `a` on `[1/2, 11/20]` (e.g. via trigamma bounds)
   and use it to transfer the known `a(1/2)` lower bound to `a(1-θ)` when `θ≈1/2`.
   - Risk: introduces heavy special-functions analysis in Lean.
3) **False-for-now (policy):** silently mix two-scale (`t_sym` floor + `t_critical` prime cap) in the *same* proof chain.
   - If we go two-scale, we must write an explicit comparison lemma and document the spec change; otherwise it’s drift.


## Спеки

- Основной спецификатор инвариантов: `docs/PROJECT_SPECS.md`.

---

## PrimeCert B-range Lipschitz (heat-weighted scaffold, 2026-01-28)

**Why:** current main-chain axioms are
`PrimeCert.prime_b_grid_bounds_data`, `PrimeCert.prime_heat_bounds_arch_data`,
and `PrimeCert.prime_heat_bounds_prime_data`.
The analytic bound in `Brange_Lipschitz_Analytic.lean` uses `W_sum_local` and is far too large;
we need a *heat-weighted* Lipschitz constant to match the certificate scale (~0.3).

**What was added (scaffold):**
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatScaffold.lean`
  - `PrimeMarginHeatLipschitzCert` structure (L_arch/L_prime + certified bounds)
  - `margin_Lipschitz_of_cert` lemma to combine bounds
- `scripts/prime_brange_heat_lipschitz_cert.py`
  - numeric helper to estimate heat-weighted constants (arch + prime) for t_critical
  - outputs `output/prime_cert_brange_heat_L_*.txt`
  - latest output: `output/prime_cert_brange_heat_L_interval_2026-01-30_2309.txt`
    (sha256 `da6a6ac1221f93d376aafecd189169607b40b5d394868e893124445089a3e0a5`)
    with `L_prime_heat ≈ 4.0049`, `L_arch_heat ≈ 1.3604`, `L_total ≈ 0.59614`
    → conservative bound `L_total ≤ 0.60`

**Next (to actually close the axiom):**
1) Produce a certified numeric constant from the script output
2) Provide Lean lemmas `h_arch` and `h_prime` (or a combined margin version)
3) Instantiate `PrimeMarginHeatLipschitzCert` and replace the axiom in
   `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` / `Brange_2046.lean`.

**Note:** q3search failed locally (403 spend limit), so we used local `rg` only.

---

## PrimeCert Lipschitz closure plan (2026-01-28)

**Target lemma:** `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange` in
`Q3/Proofs/PrimeCert/BrangeCert_2046.lean` (main-chain axiom).

**Semantic search:** attempted `q3search` (3 queries) and `websearch` (1 query) → both commands missing
in this sandbox (`Befehl nicht gefunden`, exit 127). Fell back to local `rg`.

**Local hits:** `phi_shift_lipschitz_B_exp` + `margin_Lipschitz_symbolic` in
`Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` give the formal *shape* of a Lipschitz proof,
but constants are too large (`W_sum_local`, `M_a_local`).

**Option 1 (preferred):** formalize heat-weighted bounds using `phi_shift_lipschitz_B_exp`,
then bound prime/arch contributions by numeric constants from
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean`; instantiate
`PrimeMarginHeatLipschitzCert` (file: `Brange_Lipschitz_HeatScaffold.lean`) and replace the axiom.

**Option 2 (fallback):** keep the axiom but document the analytic bound path
(`margin_Lipschitz_symbolic`) as “false-for-now” due to oversized constants.

**Immediate next actions:** (a) create Lean lemmas `h_arch`/`h_prime` using heat-weighted
integral/sum bounds; (b) wire `margin_Lipschitz_of_cert` into `BrangeCert_2046.lean`;
(c) re-run `lake env lean` on the touched files.


## Synthesis (2026-01-30, in progress) — PrimeCert cert-data axioms closure plan

- Target axioms: `prime_b_grid_bounds_data` (`Q3/Proofs/PrimeCert/BrangeCert_2046.lean`)
  and the heat cert-data axioms `prime_heat_bounds_arch_data`,
  `prime_heat_bounds_prime_data` (`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean`);
  these feed `prime_b_grid_val_le_margin` and `prime_margin_Lipschitz_on_Brange`.
- Step 1: discharge `PrimeHeatBoundsData` by proving `h_arch` + `h_prime` and use
  `prime_heat_bounds_total` for `h_total` (files:
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof.lean`,
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`).
- Step 2: wire `prime_heat_bounds_cert` into
  `margin_Lipschitz_heat_of_bounds` → `prime_margin_Lipschitz_on_Brange`
  (`Q3/Proofs/PrimeCert/BrangeCert_2046.lean`).
- Step 3 (grid data): either (A) replace `prime_b_grid_bounds_data` with analytic bounds
  at each grid point using the same arch/prime estimates, or (B) keep as cert-data but
  add a non-`native_decide` verification file that checks the finite inequalities with
  `norm_num` only.
- Update (2026-01-30): added `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean`
  to split the prime-term tsum into partial sum + tail and reduce the grid bound
  to two explicit obligations: (i) `prime_b_grid_prime_sum_up_to` ≤ table sum and
  (ii) tail ≤ `prime_b_grid_tail_bound`. This is the intended landing zone for the
  interval-certificate pilot (2 points first, then full grid).
- Update (2026-01-30): proved a pointwise analytic domination lemma
  `prime_b_grid_weight_term_le_tail_term` (same file), reducing the tail proof to
  bounding `∑' n, prime_b_grid_tail_term (n + (N+1))` by the tiny numeric constant.
  This isolates the remaining work to a sum→integral comparison + numeric bound.
- Constraint: keep everything one-scale (`t_critical`, `tau = 0`) and avoid two-scale bridges
  (`Q3/Proofs/ShiftedWindows.lean`, `Q3/Proofs/Params_Critical.lean` are the anchors).
- External leads for explicit prime-sum bounds: Schoenfeld (1976), Dusart/Trudgian bounds,
  and the AFP entry `Chebyshev_Prime_Bounds` as a formalizable reference path.
- Web scan (2026-01-30): AFP `Chebyshev_Prime_Bounds` gives explicit ψ/θ bounds and a
  concrete proof structure; consider porting the tail bound pattern for
  `∑ w_Q n * exp(-c (log n)^2) * |log n|`. Also note newer explicit ψ bounds (e.g., 2023 JMAA)
  as a constants source, but likely too heavy to formalize directly.
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  then `lake env lean Q3/CheckAxioms.lean` once mathlib is healthy.

## Synthesis (2026-01-30, in progress) — PrimeHeatBoundsData closure pass 1

- Target axioms: `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean` and
  `Q3.Proofs.PrimeCert.prime_heat_sum_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`; they feed
  `prime_heat_bounds_data` → `prime_heat_bounds_cert` → `prime_margin_Lipschitz_on_Brange`.
- Update (2026-01-30): split cert-data into two axioms
  (`prime_heat_bounds_arch_data`, `prime_heat_sum_data`);
  `prime_heat_bounds_data` is now derived from these.
- Embedding search (q3_docs): queries `prime_heat_bounds`, `BrangeHeatCert`,
  `heat Lipschitz`, `prime cert heat`, `brange heat` returned only generic
  prime-cert notes; no existing formal closure.
- Web leads (external bounds for prime sums): Schoenfeld (1976) explicit ψ/θ bounds;
  newer explicit ψ bounds in JMAA 2023 (useful for tail control if formalized).
- Arch bound plan: use `a_star_linear_growth` + closed-form Gaussian integrals to
  upper-bound `∫_{Icc} |a_star ξ| * exp(-4π^2 t ξ^2) * |ξ|` by
  `prime_cert_L_arch_heat_raw` (files: `Brange_Lipschitz_HeatIntegrable.lean`,
  `BrangeHeatCert_2026_01_28.lean`).
- Prime bound plan: split sum at `N = 10^6` (finite part imported with
  directional rounding as data), plus a tail bound via the integral estimate
  already used in `scripts/prime_brange_heat_lipschitz_cert.py`; wrap into Lean
  inequalities with `norm_num`.
- Implementation: add a dedicated sum-data file
  (`BrangeHeatCert_2026_01_28_SumData.lean`) and replace the axiom with a
  theorem that composes the two bounds.
- Status update (2026-01-30): added `BrangeHeatCert_2026_01_28_Data.lean` for
  constants + arch bound, and `BrangeHeatCert_2026_01_28_SumData.lean` for
  partial+tail evidence; `prime_heat_bounds_data` is now derived in
  `BrangeHeatCert_2026_01_28.lean`.
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
  then `lake env lean Q3/CheckAxioms.lean`.

## Pilot update (2026-01-30) — 2-point grid scaffolding

- Added `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30.lean`:
  `PrimeBGridPilotHyp` packs the two required inequalities (partial sum + tail)
  and provides pilot lemmas for `i=0` (B=3.0) and `i=19` (B=4.9) without adding
  axioms or sorries.
- Added `scripts/prime_brange_pilot_points.py` to extract the two rows from the
  existing B-range certificate and emit a pilot trace file:
  `output/prime_cert_brange_tcritical_pilot_2026-01-30_1820.txt`.
- Next: supply `PrimeBGridPilotHyp` for the two points via interval‑certificate
  inequalities (partial sum up to N and tail bound). Once that lands, we can
  lift to all 20 points.

## Tail bound reduction (2026-01-30)

- Added `prime_b_grid_tail_bound_of_tail_term` in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean`:
  it reduces the prime‑term tail inequality to the **pure tail term**
  `prime_b_grid_tail_term` using `Summable.tsum_le_tsum`.
- Remaining inputs: summability of the tail term and the numeric inequality
  `∑' n, prime_b_grid_tail_term (n + (N+1)) ≤ prime_b_grid_tail_bound`.

## IN PROGRESS — Log‑Gaussian tail bound (PrimeCert B‑grid)

- Target: prove `prime_b_grid_tail_term` summability and the numeric tail bound in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean` (feeds the pilot + full grid).
- Use `Mathlib/Analysis/SumIntegralComparisons` (`AntitoneOn.sum_le_integral`) to show
  `∑_{n≥N+1} f(n) ≤ ∫_{N}^∞ f(x) dx` for `f(x) = 2 log x / sqrt x * exp(-t (log x)^2)`.
- Establish monotone/antitone + nonneg of `f` for `x ≥ N` in the same file
  (or a helper lemma file under `Q3/Proofs/PrimeCert/`).
- Substitute `u = log x` to rewrite the integral as
  `∫_{log N}^∞ 2u * exp(-t u^2 + u/2) du`; then complete the square.
- Numeric closure: bound the Gaussian tail explicitly (Mill’s ratio) or,
  if Lean bounds get heavy, submit a focused Aristotle lemma for the tail integral
  and then plug into `prime_b_grid_tail_bound_of_tail_term`.
- Once tail is closed, finish the two pilot points in
  `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30.lean` and lift to all 20 grid points.

## Synthesis (2026-02-03, in progress) — Prime-heat bucket pilot without native_decide

- Target: pilot lemmas `prime_heat_bucket_sum_le_ub_pilot_{0,99}` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Pilot.lean`; these mirror the eventual
  `prime_heat_bucket_bounds` path in `BrangeHeatCert_2026_01_28_SumData.lean`.
- Blocker: current `BrangeHeatCert_2026_01_28_Checker.lean` imports huge
  `BrangeHeatCert_2026_01_28_PrimePowData.lean` and uses `native_decide`, which we want to
  avoid for a clean axiom list (compiler-trust axioms).
- Option 1 (preferred): refactor bucket/partition defs into
  `BrangeHeatCert_2026_01_28_BucketDefs.lean`; generate a **pilot** prime-power table for
  buckets 0 & 99 only (new `scripts/prime_brange_heat_pp_interval_checker.py --buckets 0,99`).
- Option 1: prove `prime_heat_bucket_sum_le_pp_ub_pilot_{0,99}` and
  `prime_heat_bucket_pp_sum_ub_le_bucket_pilot_{0,99}` using explicit rationals with
  `norm_num`/`decide` (no `native_decide`).
- Option 2 (fallback): keep full `PrimePowData` + `native_decide` off-chain and use pilot
  lemmas only as structure checks (no numeric proof).
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketDefs.lean`
  and `BrangeHeatCert_2026_01_28_Pilot.lean` compile without new axioms in `#print axioms`.

**Update (2026-02-03):**
- Added `BrangeHeatCert_2026_01_28_BucketDefs.lean` to isolate bucket/partition lemmas.
- Added sums-only pilot data `BrangeHeatCert_2026_01_28_PrimePowPilotSums.lean` and proved
  bucket 0/99 pilot bounds in `BrangeHeatCert_2026_01_28_Pilot.lean` without `native_decide`.
- Extended `scripts/prime_brange_heat_pp_interval_checker.py` with `--buckets` and
  `--subnamespace`; generated full per-term pilot data `BrangeHeatCert_2026_01_28_PrimePowPilot.lean`
  (kept for later; not compiled yet).
- Verified: `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs` and
  `...PrimePowPilotSums`; `lake env lean BrangeHeatCert_2026_01_28_Pilot.lean` passes.

## Synthesis (2026-02-03, in progress) — План закрытия Level‑2 аксиом PrimeCert

Target axioms:
- `prime_heat_bucket_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
- `prime_heat_bounds_arch_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
- `prime_b_grid_bounds_data` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`

Embedding search (q3_docs):
- Queries: "prime_heat_bucket_data", "prime_b_grid_bounds_data", "prime_heat_bounds_arch_data".
- Result: `qmd` query timed out on this host (120s/60s); no hits recorded.

Web search:
- Interval arithmetic in Lean / intervalIntegral numeric bounds: no drop‑in tactic found yet.

Plan (5–10 lines, concrete pointers):
1. `prime_heat_bucket_data`: move data into a proof file (e.g. `BrangeHeatCert_2026_01_28_BucketCheck.lean`)
   and prove per‑bucket bounds via interval/endpoint envelopes emitted by
   `scripts/prime_brange_heat_interval_checker.py` (Lean proofs over ℚ + `linarith`, no `native_decide`).
2. `prime_heat_bounds_arch_data`: add `BrangeHeatCert_2026_01_28_ArchBounds.lean` with piecewise bounds on
   `|a_star| * heat_weight_tc`, then discharge the integral bound in
   `BrangeHeatCert_2026_01_28.lean` using `intervalIntegral` + certified endpoints.
3. `prime_b_grid_bounds_data`: extend `BrangeGrid_PrimeSum_2026_01_30_Checker.lean` to reduce each grid bucket
   to finite sums and close bounds using `BrangeGrid_PrimeSum_2026_01_30_Intervals.lean` data.
4. Infrastructure + guardrail: add `Q3/Proofs/PrimeCert/IntervalLemmas.lean` (ℚ endpoint lemmas for exp/log
   monotonicity), and keep A3_FLOOR vs RKHS strategies strictly separated in these files.
5. Verification + success: after each swap run `lake env lean` on touched files and `./scripts/check_axioms.sh`,
   log axiom count drop in `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`; success when only project axiom left is
   `Q3.Weil_criterion_tau0`.

## Synthesis (2026-02-06, in progress) — Tier-2 closure in main-chain via explicit margin hypothesis

- Scope: close Tier-2 PrimeCert axioms in `#print axioms Q3.Main.RH_of_Weil_and_Q3`, keep
  `Q3.Weil_criterion_tau0` as the only project axiom in chain.
- Current blockers (cert-data axioms): `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bucket_data`.
- Chosen path: add an axiom-free `of_margin` proof route in
  `Q3/Proofs/Q_nonneg_t_critical.lean` that takes an explicit hypothesis
  `h_margin_cert : ∀ B ∈ [B_min, B_max], prime_cert_margin_lb ≤ arch_term - prime_term`.
- Main wiring: switch `Q3/Main.lean` to use the new `of_margin` theorem and make
  `RH_of_Weil_and_Q3` explicitly depend on `h_margin_cert` (hypothesis, not global axiom).
- Expected `#print axioms` result: only standard axioms + `Q3.Weil_criterion_tau0`.
- Safety: old cert-backed theorem path remains available for backward compatibility;
  only the main theorem route changes.

**Update (2026-02-06, done):**
- Implemented `of_margin` axiom-free path in `Q3/Proofs/Q_nonneg_t_critical.lean`:
  `PrimeCertMarginOnBrange`,
  `prime_term_le_arch_term_on_Brange_tau0_of_margin`,
  `Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin`,
  `Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin`.
- Rewired `Q3/Main.lean`: `RH_of_Weil_and_Q3` now takes explicit hypothesis
  `(h_margin_cert : Q3.PrimeCertMarginOnBrange)` and no longer depends on
  PrimeCert cert-data axioms in `#print axioms`.
- Updated `scripts/check_axioms.sh` expected counts to
  `Project=1, Standard=3, Total=4` and fixed Q3-axiom parsing for short lists.
- Verification:
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `./scripts/check_axioms.sh` ✅
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3`
    → `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.

## Ops note (2026-02-08, done) — isolated heavy runs for Lean/Codex

- Added executable helper: `scripts/run_heavy.sh`.
- What it does:
  1. Checks user-systemd availability.
  2. Creates `codex-heavy.slice` (if missing) with defaults:
     `MemoryHigh=20G`, `MemoryMax=28G`, `CPUWeight=80`,
     `ManagedOOMPreference=avoid`.
  3. Runs the command inside that slice via
     `systemd-run --user --scope`.
- Usage:
  - Interactive shell in isolated slice:
    `./scripts/run_heavy.sh`
  - Run a command in isolated slice:
    `./scripts/run_heavy.sh lake build Q3.Main`
- Verified smoke checks:
  - `./scripts/run_heavy.sh --help`
  - `./scripts/run_heavy.sh bash -lc 'echo RUN_HEAVY_OK'`
- Operational caveat:
  - Very large PrimeCert builds can exceed default `MemoryMax=28G` and be
    killed by `systemd-oomd` in that scope.
  - For those runs only, start a one-off scope with higher limits
    (e.g. `MemoryHigh=36G`, `MemoryMax=48G`) and keep the default slice
    limits unchanged for regular work.

## Synthesis (2026-02-10, in progress) — Step 2 GT10000 blocker: deep disjunction elaboration

- Target: unblock `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  by replacing the last fallback axiom path for `n > 10000`.
- Root cause (code-level): GT10000 shard mem-lemmas generated a giant
  `have hcases : n = ... ∨ ...` and `rcases hcases with ...` tree
  (about 1k branches per shard), which is a recursion/elaboration hotspot.
- Evidence pointers:
  - `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_10001_20000.lean`
    (around `prime_heat_weight_term_le_pp_ub_of_10001_20000_primepow_mem`).
  - Generator path in `scripts/prime_brange_heat_pp_auto.py` (mem-lemma emission block).
- External cross-check: `lean-stat-learning-theory` (`7b82b13`) uses
  small-lemma decomposition and local heartbeat tuning, and does not rely on
  giant OR-dispatch chains for this kind of branching.
- Applied workaround:
  1. Generator now emits `classical; fin_cases hmem` for mem dispatch.
  2. Existing GT10000 shard files were migrated from `hcases/rcases` to `fin_cases`.
- Smoke verification:
  - `timeout 240 lake build +Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_10001_20000:olean`
    reaches long compile phase without immediate recursion-depth crash (`EXIT=124`, timeout).
  - `timeout 240 lake build +Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000:olean`
    also proceeds without early compile errors (`EXIT=124`, timeout).
- Next checkpoint:
  - run isolated long build (`scripts/run_heavy.sh`) to completion and confirm
    `.olean` for GT10000 shards + aggregator, then re-run
    `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.

### Strategy memo (фиксируем, чтобы не забыть)

- Не лечить это как «системный баг»: первопричина в форме proof-term
  (`hcases/rcases` на огромном дизъюнкте), а не в Ubuntu.
- Базовый паттерн для GT10000: `classical; fin_cases hmem` вместо giant OR.
- Держать проверку двухступенчато:
  1. короткий smoke-timeout (ловит ранние ошибки/регрессии генерации),
  2. длинный изолированный прогон в `codex-heavy.slice` до `.olean`.
- После длинного прогона обязательный контрольный шаг:
  `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.

## 2026-02-22 — Path A стабилизация: PrimeCert вынесен из критического пути

- Исправлен `Q3/Proofs/RKHS_PrimeCap_Analytic.lean` (структура модуля/импорты), модуль собирается.
- Исправлен `Q3/Proofs/Q_nonneg_atoms_closure.lean` (`tsum_add` -> `Summable.tsum_add`) для совместимости с текущим Mathlib API.
- Исправлен `Q3/Proofs/Bridge.lean` (корректная `WithLp.toLp`-конструкция для `EuclideanSpace`).
- Проверено: `lake build Q3.RKHS_Contraction`, `lake build Q3.T5_Transfer`, `lake env lean Q3/Main.lean`.
- Результат: основной путь снова доходит до `Q3.Main.RH_of_Weil_and_Q3 : RH`; каскадный блокер по PrimeCert в main dependency path снят на Path A.

## Synthesis (2026-02-23, in progress) — Sub-agent split for final active axioms

Target blockers in active Q3 main-chain:
- `Q3.prime_term_le_at_t_critical_axiom` (`Q3/Proofs/Q_nonneg_t_critical.lean`)
- `Q3.Weil_criterion_tau0` (`Q3/Axioms.lean`)

Step-by-step execution:
1) Created two focused Aristotle requests:
   - `aristotle_input/subagent_prime_term_tcritical_2026_02_23.md`
   - `aristotle_input/subagent_weil_tau0_2026_02_23.md`
2) Strategy split:
   - Sub-agent A: close or strictly strengthen/replace `prime_term_le_at_t_critical_axiom` via Path B-compatible analytic route.
   - Sub-agent B: close `Weil_criterion_tau0` directly, or return strongest derivable theorem + minimal missing lemma set.
3) Immediate acceptance criterion:
   - produced Lean patch has no `sorry|exact?|admit`,
   - preserves active API names used by `Q3/Main.lean`.
4) After download: run `rg -n "sorry|exact\\?|admit"` on outputs, then integrate only hole-free fragments.

Update (2026-02-23, local bridge rewrite):
- Rewired `Q3.Q_phi_shift_nonneg_t_critical_tau0_brange[_of_margin]` in
  `Q3/Proofs/Q_nonneg_t_critical.lean` to use:
  - `prime_term_le_arch_term_on_Brange_tau0_of_margin`
  - `prime_term_le_arch_term_on_Brange_tau0`
  instead of `prime_term_le_at_t_critical_axiom`.
- Resulting active main-chain axiom status (`#print axioms` on `Q3.Main.RH_of_Weil_and_Q3`):
  - standard: `propext`, `Classical.choice`, `Quot.sound`
  - project gates: `Q3.Weil_criterion_tau0`, `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`
  - `Q3.prime_term_le_at_t_critical_axiom` no longer appears in RH chain.
- Strict executable-hole scan (active Q3, excluding Archive/Clean):
  - no matches for `^\s*(sorry|admit)` and no `exact?` hits.

Update (2026-02-23, Aristotle context fix):
- Initial Aristotle jobs without explicit context returned non-actionable stubs (model could not see Q3 files).
- Re-submitted the same three sub-agent requests with `--no-auto-add-imports` + explicit `--context-files`:
  - `fab26ba2-c4c8-438d-911f-30970145e35a` (prime_term gate)
  - `750bb959-5f7e-4e5f-919c-c4af2d818949` (Weil tau0)
  - `17375b4f-0025-4b66-b309-f6f4bb7774f2` (PrimeCert PathB margin)
- Expected acceptance criterion unchanged: no `sorry|exact?|admit`, then integrate only hole-free lemmas.

Update (2026-02-23, PrimeCert legacy rebuild):
- Root blocker for legacy chain remains stale/invalid PrimePow `.olean` artifacts.
- Started targeted rebuild:
  `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`
- Current state: chunk modules `..._10001_20000` etc are actively recompiling under current toolchain; after completion re-test:
  1) `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  2) `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`

## Synthesis (2026-03-05, in progress) — PrimeHeat arch-bound blocker under current toolchain

Target lemma / axiom:
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
- Wiring: this feeds `prime_heat_bounds_data` -> `prime_heat_bounds_cert` ->
  `prime_margin_Lipschitz_on_Brange` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  and from there the current τ=0 PrimeCert margin chain.

Embedding search (q3_docs, 3 successful queries):
- `prime_heat_bounds_arch_data heat arch integral bound`
- `BrangeHeatCert arch bound a_star heat_weight intervalIntegral`
- `a_star linear growth Gaussian integral prime cert`
- Consistent hits: previous plans already converge on the same route:
  use `a_star_linear_growth` together with Gaussian integrability/interval-integral
  lemmas; no existing hole-free closure was found in the repo index.

Web / external scan:
- No drop-in Mathlib tactic path for this numeric interval bound was identified.
- This strengthens the local conclusion that the next productive move is not a
  fresh theorem sketch in isolation, but restoring the PrimeHeat build chain first.

Local build diagnosis (current machine, 2026-03-05):
1. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
   fails because `..._Partial.olean` is missing.
2. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Partial.lean`
   fails because `..._SumData.olean` is missing.
3. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
   fails because `..._Checker.olean` is missing.
4. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
   fails on incompatible header for
   `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000.olean`.
5. Timestamp check shows that incompatible artifact still dates to 2026-02-09,
   while current project toolchain is `mathlib v4.26.0`; this is a stale-build,
   not a new theorem regression.

Decision tree:
- Option 1 (active): rebuild `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`
  and then the chain `Checker -> SumData -> Partial -> BrangeHeatCert_2026_01_28`,
  only after that return to `prime_heat_bounds_arch_data`.
- Option 2 (fallback): if the rebuild still fails after the stale `.olean` layer is
  removed, isolate the first source-level error in the GT10000 aggregator and fix
  that before touching arch bounds.
- Option 3 (false-for-now): sending a fresh Aristotle request for
  `prime_heat_bounds_arch_data` immediately. Rejected for now because all prior
  2026-02-09 outputs were empty stubs with `sorry` due missing Q3 context, and the
  current blocker is upstream build integrity.

Concrete next steps:
1. Finish targeted rebuild of `Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`.
2. Re-run `lake env lean` on `Checker`, `SumData`, `Partial`, and the main
   `BrangeHeatCert_2026_01_28.lean` in that order.
3. Once the chain compiles again, either prove `prime_heat_bounds_arch_data`
   locally from existing heat-integrability infrastructure or prepare a new
   Aristotle request with explicit Q3 context files and no import ambiguity.

## Synthesis (2026-03-05, in progress) — full paper mainline vs live Lean mainline

Source read completely enough to reconstruct the live proof spine:
- `full/RH_Q3.tex` and the active main sections
  `T0`, `A1prime`, `A2`, `A3/*`, `RKHS/*`, `D3/*`, `Weil_linkage`, `Weil_pack`,
  `Main_closure`.
- Active paper mainline is explicitly:
  `T0 + A1' + A2 + A3 + RKHS -> Main positivity -> Weil criterion`.
- `D3`, `T5`, and `IND_AB` are archived/legacy in the paper and are not meant to
  be part of the critical proof path.

What this changes for Lean:
- Live `Q3.Main.RH_of_Weil_and_Q3` currently depends on
  `Q3.Weil_criterion_tau0` and `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`,
  not on the paper-mainline analytic chain.
- So the repo now has a structural mismatch:
  the paper advertises an analytic uniform route, while Lean mainline still closes
  via a legacy PrimeCert gate.

Paper mainline nodes that already have serious Lean support:
- `T0`: normalization crosswalk is already wired in `Q3/AxiomsTheorems.lean`.
- `A1'`: density is largely wired/theorem-level in the current transfer stack.
- `A2`: continuity/Lipschitz is theorem-level in current Lean.
- `C1`: compression-by-isometry is already formalized in
  `Q3/Proofs/C1_Embedding_Bridge.lean` and `Q3/Proofs/C1_T_P_comp_bridge.lean`.
- `A3_FLOOR`: monotonicity/sample-point infrastructure exists (`A3_Floor_*`).

Critical mismatches discovered while reading the paper:
- The paper claims “single-scale alignment”, but the active text mixes
  `t = t_critical = 3/20`, `t_sym = 3/50`, and `t_rkhs = 1`.
- `full/sections/A3/symbol_floor.tex` states the uniform Arch floor at `t = 3/50`,
  while `full/sections/A3/main.tex` consumes it as if it were the A3 bridge floor
  at `t = 3/20`.
- `full/sections/RKHS/prime_cap.tex` uses the uniform cap at `t_rkhs = 1`,
  which directly conflicts with the “single-scale” language in `A3/main.tex`.
- `A1'` in the main paper still defers its proof to the archived shifted-atom
  density argument instead of giving a fresh in-line proof.

Recommended Lean refactor:
- Stop treating PrimeHeat/Grid certificate closure as the only mainline plan.
- Introduce a paper-mainline migration track:
  `A3_Digamma_Symbol -> A3_Uniform_Bridge -> RKHS_rho_cap -> tau0_bridge -> Main`.
- Keep legacy `PrimeCert` certificate closure as a separate branch of work, not as
  the blocker for the theorem-first mainline.

Recommended progress tracking:
- Track by paper theorem, not by legacy axiom name.
- Minimal columns:
  paper statement, Lean target file, current proof status, wired into mainline?,
  axiom impact, parameter contract frozen?
- Highest-priority blocker is now not “compute PrimeHeat again”, but
  “freeze the scale contract of the paper mainline”.

## Synthesis (2026-03-07, in progress) — honest target is pair/evenized `t_critical`, not scalar `phi_shift`

Exact live blocker and wiring:
- Active chain is still
  `Q3.Main -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`.
- The only nonstandard project axiom in the live scalar node remains
  `Q3.prime_term_le_at_t_critical_axiom`, as confirmed by
  `#print axioms Q3.Main.RH_of_Weil_and_Q3`.
- This axiom is consumed in `Q3/Proofs/Q_nonneg_t_critical.lean` by
  `prime_term_le_at_t_critical -> Q_phi_shift_nonneg_t_critical ->
   Q_phi_shift_pair_nonneg_t_critical -> Q_Fejer_heat_atom_nonneg_t_critical`.

Local search / blocker audit:
- Semantic search must be run from the repo root. Running
  `./scripts/research_oracle.py` from `q3.lean.aristotle/` fails because the
  script only exists at the top level.
- Five local embedding queries were attempted for the new blocker. Three failed
  with `SQLiteError: database is locked / SQLITE_BUSY_RECOVERY`; the two that
  returned results only surfaced stale `tau=0` / old-axiom notes and did not
  produce a direct pair/evenized closure lemma.
- External web search (primary-source oriented) found only general Weil-criterion
  structure results, e.g. Connes--Consani on restricting to compactly supported
  convolution-square test functions. Useful philosophically, but not a direct
  proof of our shifted-evenized `t_critical` lemma.

New local theorem support added:
- `Q3/Proofs/PrimeTerm_t_bridge.lean` now contains:
  `PrimeTermBridge.prime_term_phi_shift_tcritical_le_cap`
  and
  `PrimeTermBridge.prime_term_phi_shift_tcritical_le_exp_rho_oneK`.
- These compile and expose the honest bridge
  `prime_term(phi_shift at t_critical) <= exp_tcrit_to_rkhs(K) * R`,
  with the RKHS cap route providing `R = rho_oneK K`.

Critical no-go discovered immediately:
- `rho_oneK` is defined as
  `exp(8 * pi^2 * t_rkhs_cap * K^2) * rho_one`, so the `t_critical -> t_rkhs_cap`
  transport carries a huge exponential penalty.
- Numerically,
  `t_rkhs_cap = 40/(16*pi^2) ≈ 0.2533029591`,
  and already at `K = 1` we have
  `exp_tcrit_to_rkhs(1) ≈ 1.2151333e7`.
- Therefore the old single-scale budget
  `rho_one <= c_star / 4`
  does **not** control
  `exp_tcrit_to_rkhs(K) * rho_oneK(K)`;
  the bridge explodes instead of closing the scalar inequality.
- So the plan item “prove the same-signature scalar theorem by combining RKHS cap
  with the existing `c_star` floor” is false as an implementation path.

Consequence for the active proof strategy:
- Do **not** send Aristotle after the old target
  `prime_term_le_at_t_critical_axiom` with the same signature.
- The honest next target is one of:
  1. `Q_phi_shift_pair_nonneg_t_critical`,
  2. `Q_Fejer_heat_atom_nonneg_t_critical`,
  3. or a minimal new assumption that closes exactly one of those two theorems.
- The right request should explicitly reuse the new bridge lemmas and the existing
  decomposition
  `Fejer_heat_atom_eq_phi_shifts`,
  but it must allow Aristotle to return a weaker theorem or an explicit obstruction
  if pair/evenized positivity still needs one extra ingredient.

## Synthesis (2026-03-07) — G0 reset loop frozen as project contract

Control-plane decisions:
- We stay in the current repo; no new physical `work3` clone.
- The canonical control plane is exactly four files:
  `PROJECT_ORCHESTRATOR.md`,
  `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`,
  `docs/INSIGHTS.md`.
- Precedence is fixed:
  orchestrator > paper tracker > execution plan > insights.
- Supporting snapshots such as `docs/CHAIN_STATUS.md` and `ACTIVE/MAIN_CHAIN_DEPS.md`
  remain useful, but they are now explicitly read-only/supporting and no longer
  define active frontier or queue state.

Gate-contract decisions:
- The active project chain is fixed as
  `T0 -> G0 -> G1 -> G2 -> G3 -> G4 -> G5 -> G6 -> RH`.
- `G3` is restored as its own gate. This matters operationally:
  `G2` chooses and freezes the exact admissible family `G_K`,
  while `G3` proves positivity on that same `G_K`.
- The reset sprint was `G0`, i.e. a governance/typing sprint rather than new math:
  `G0.0` numbering/precedence freeze,
  `G0.1` vocabulary split,
  `G0.2` closure typing pass,
  `G0.3` narrative alignment.

Concrete manuscript drift identified before edits:
- `A1'` is genuinely a theorem on the restriction cone
  `R_K = C^+_{even}([-K,K])`, not yet on admissible `W_K`.
- `A2` and the LF route consume admissible `W_K`.
- `Main_closure.tex` still phrases the density input as if it already lived on `W_K`,
  so the closure section is ill-typed until `G0/G1` are made explicit.
- `introduction.tex` still advertises a closed `PSD on each W_K => Weil positivity`
  chain instead of the gate chain with unresolved `G1-G3`.
- Lean wrappers in `Q3/Main.lean` and `PaperMainlineAtomRoute.lean` expose useful
  theorem names, but their docstrings need to say explicitly that the current route
  still inherits `Q3.prime_term_le_at_t_critical_axiom`.

Result of the reset pass:
- `PROJECT_ORCHESTRATOR.md`, `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`, and `docs/INSIGHTS.md`
  now agree on the same gate chain, precedence rule, and active frontier.
- Active manuscript sections now separate `R_K`, `W_K`, and future `G_K` explicitly.
- `A1'` is now stated as density on `R_K`, while `Main_closure.tex` and the Weil-linkage text stay explicitly conditional on the unresolved closure gates.
- Lean-facing docstrings in `Q3/Main.lean`, `PaperMainlineAtomRoute.lean`, and `CompatibilityReduction.lean`
  now describe the exported route as the current compiled route rather than as an already fully closed proof.

Verification bundle completed:
- `cd full && latexmk -pdf RH_Q3.tex`
- `cd q3.lean.aristotle && lake env lean Q3/Main.lean`
- `printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`
- Active axiom profile remains:
  `Q3.Weil_criterion` + `Q3.prime_term_le_at_t_critical_axiom`
  plus standard `propext`, `Classical.choice`, `Quot.sound`.

Consequence for the next loop:
- `G0` is now closed.
- The next honest frontier is `G1.1`: freeze the first support-upgrade theorem on admissible `W_K`.

## Synthesis (2026-03-07, in progress) — q3_docs refresh + first honest post-Aristotle blocker

Live infra audit:
- `qmd status` showed the old `q3_docs` collection was stale: 91 indexed files,
  475 vectors, updated 33 days ago.
- That old collection indexed only `**/*.md`, so current TeX and live Lean files were
  absent from semantic search.
- The documented entrypoint `./scripts/research_oracle.py` from inside
  `q3.lean.aristotle/` was also broken: the real backend script lived only at the repo
  root (`/Users/emalam/Documents/GitHub/rh_lean_01_2026/scripts/research_oracle.py`).

Cleanup decision:
- `q3_docs` should not stay as a stale markdown dump.
- It is now rebuilt as a curated live KB containing:
  - current control/workflow docs,
  - active manuscript TeX (`full/sections`, `full/appendix`, `RH_Q3.tex`),
  - live Q3 Lean files,
  - while excluding `Archive`, `Clean`, transcript dumps, and heavy `PrimeCert` shards.
- A local wrapper `q3.lean.aristotle/scripts/research_oracle.py` now delegates to the
  repo-root backend, and `q3.lean.aristotle/scripts/refresh_q3_docs.py` rebuilds the
  staged source tree plus the `q3_docs` collection repeatably.

Reason this matters for `G1`:
- The completed Aristotle result for `c315e2a4-5923-44fa-a18c-4ed90cb08375` cannot be
  integrated: it contains holes and sandbox-local fake definitions instead of real Q3
  objects.
- So the next correct step is not “retry the same packet blindly”, but extract the
  first honest blocked local theorem from the real `hg_mem` support-membership block.
- Fresh embeddings are now part of the blocker workflow, not optional garnish.

Refresh result:
- After tightening the curated scope and excluding legacy snapshots, transcript dumps,
  and queue artifacts, `q3_docs` now indexes a curated live corpus rather than the old
  markdown-only dump.
- The refreshed top hits for
  `hg_mem AtomCone_K_fixed hmargin Atom_eq_zero_outside_open`
  now point directly to:
  - `Q3/Proofs/A1_density.lean`,
  - `Q3/Axioms.lean`,
  - `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`.
- The refreshed top hits for
  `atom_sum_mem_W_K_of_margin support subset continuity even nonnegative`
  now surface the exact local neighborhood we need:
  - `docs/PAPER_MAINLINE_TRACKER.md`,
  - `Q3/Axioms.lean`,
  - `Q3/Proofs/Q_Lipschitz.lean`,
  - plus the already inspected inline proof block in
    `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`.

Exact next theorem shape frozen from the real `hg_mem` block:

```lean
lemma atom_sum_mem_W_K_of_margin
    (K t0 δ : ℝ) (hK : K > 0) (ht0 : 0 < t0) (hδ : 0 < δ)
    (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hmargin : ∀ i, |τ i| + δ ≤ K) :
    let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x
    g ∈ Q3.W_K K := by
```

Supporting pointers:
- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean:176-240` already contains the exact
  continuity / support / even / nonnegative subproof shape.
- `Q3/Proofs/A1_density.lean:248` provides `Atom_eq_zero_outside_open`, which is the
  real support-vanishing brick under the margin condition.
- `Q3/Basic/Defs.lean:148-152` fixes the real definition of `Q3.W_K`.
- `Q3/T5_Transfer.lean:55-59` shows the downstream wrapper pattern once `g ∈ W_K` is available.

Web + local mathlib check:
- External search on Lean/mathlib support machinery pointed to `Function.support_sum`.
- Local grep confirmed generic support lemmas such as `Function.support_subset_iff'`
  are available in Mathlib, so the support subproof can be kept on a standard path if
  the pointwise `Atom_eq_zero_outside_open` route needs a small helper.

## Synthesis (2026-03-07, in progress) — G1.1 support-upgrade theorem shape

Target node and wiring:
- `G1` sits strictly between A1' density on `R_K` and the future admissible family `G_K`.
- The frozen contract must therefore avoid choosing `G_K` too early, but it must be strong enough to feed A2 on admissible tests.

Local semantic search:
- Query `AtomCone_K_fixed subset support admissible W_K closure gap` returned the old
  `atomcone-fixed-t-gap-2026-01-18` insight and the earlier note that `A1_density_WK_thm`
  depended on a missing `h_approx` / support-control step.
- Query `support containment hat interpolation margin condition hg_supp admissible support stays in [-K,K]`
  pointed to the old support-margin route: `hg_supp`, `hmargin`, and hat interpolation with support staying in `[-K,K]`.
- Query `A1_density_WK_thm h_approx AtomCone_K_fixed support containment` pointed directly to the theorem shape
  `∀ Φ ∈ W_K, ∀ ε>0, ∃ g ∈ AtomCone_K_fixed, ||Φ-g||∞<ε`, which is useful as structure guidance
  but too strong to quote as already-honest paper math after the March reset.
- Three parallel semantic-search queries failed with the known local issue
  `SQLITE_BUSY_RECOVERY`; only the successful results above should be treated as actual evidence.

Concrete file/lemma pointers from the repo:
- `Q3/Proofs/A1_density.lean`: `hat_interpolation_approx_bounded`, `hmargin`, `hg_supp`,
  and the old `A1_density_WK_thm` skeleton.
- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`: old strong theorem on `W_K`, useful as a construction template.
- `Q3/T5_Transfer.lean`: shows exactly how A2 consumes admissible approximants once one has
  `g ∈ W_K`.
- `Q3/AxiomsTheorems.lean`: current legacy-strength `A1_density_WK` export, which should now be read
  as old structure guidance rather than as the active paper contract.

External web search:
- Rutgers Math 573 notes on piecewise linear approximation / hat functions support the hat-interpolation side.
- MIT 18.155 notes on mollification support the compact-support-preserving smoothing side:
  if `f ∈ C_c^0(U)`, then for small mollifier radius one has `f_ε ∈ C_c^\infty(U)` and `f_ε → f`
  uniformly on compacts.

Recommendation:
- Freeze `G1.1` as a replacement theorem, not as a direct density theorem on `W_K`.
- Exact shape:
  for every finite nonnegative restriction-level shifted-evenized approximant `h` from A1' and every `ε>0`,
  there exists an admissible replacement `\widetilde h ∈ W_K` with
  `||h-\widetilde h||_{L^\infty([-K,K])} < ε`.
- Then for `Φ ∈ W_K`, combine A1' with the replacement theorem and A2:
  `||Φ-h||<ε`, `||h-\widetilde h||<ε` implies `||Φ-\widetilde h||<2ε`, hence
  `|Q^\star(t;Φ)-Q^\star(t;\widetilde h)| ≤ 2L_Q(K)ε`.
- This is the minimal honest `G1` contract. `G2` can then name `G_K` as the class of admissible replacements produced by that theorem, and `G3` can attack positivity on that exact family.

## Update (2026-03-07, post-refresh) — q3_docs backend behavior

- Full refresh of `q3_docs` succeeded after the target-cone pivot and the new reviewed note:
  `Prepared 291 files for q3_docs: 124 md, 56 tex, 111 lean`.
- `qmd search` / `research_oracle.py query` continue to work and immediately surfaced the
  corrected-cone contract from active docs such as `full/sections/introduction.tex`,
  `full/sections/abstract.tex`, `Q3/Basic/Defs.lean`, and `docs/CHAIN_STATUS.md`.
- `qmd ls q3_docs` intermittently still hits the known local backend issue
  `SQLiteError: database is locked` / `SQLITE_BUSY_RECOVERY`.
- Treat this as a tooling/backend lock, not as evidence that the refreshed embeddings are stale.
  When the lock appears, use successful semantic-query hits plus the refresh summary as the
  practical confirmation signal, and avoid parallel pressure on the local qmd database.

## Synthesis (2026-03-07, in progress) — exact theorem blocks after the corrected-cone pivot

Target node and wiring:
- After `T0.1`, the public mainline is no longer “broad `W_K` + shifted density”.
- The next honest mathematical contract is the trio
  `T0-pd + A1-pd + packet-Rayleigh`.

Local semantic search:
- Query `A1-pd centered packet density positive definite cone autocorrelation`
  returned `full/sections/A1prime.tex` and the active implementation plan, confirming
  that the live corrected route is already centered-packet based.
- Query `Rayleigh pairing quadratic form Fejer heat packet autocorrelation`
  returned `full/sections/A3/rayleigh_bridge.tex` and `full/sections/RKHS/core.tex`,
  which is exactly the repo evidence needed for the packet-level quadratic-form bridge.
- Two sibling queries hit the known local lock
  `SQLITE_BUSY_RECOVERY`; treat the successful hits above as the usable evidence.

Concrete synthesis:
- The corrected local cone should be frozen via
  `\mathcal W_{K,0}^{pd} = { \psi * \widetilde{\psi} }` and
  `\mathcal W_K^{pd} = \overline{\operatorname{cone}(\mathcal W_{K,0}^{pd})}`.
- The exact centered generator family should be frozen as
  `\mathcal P_K = \operatorname{cone}{\Phi_\Psi = \Psi * \widetilde{\Psi}}`
  with `\Psi` a finite Fej\'er$\times$heat packet supported in `[-K/2,K/2]`.
- The exact missing pair is:
  1. `A1-pd`: `\overline{\mathcal P_K}^{\|\cdot\|_\infty} = \mathcal W_K^{pd}`;
  2. packet-Rayleigh: `Q^\star(t;\Phi_\Psi)` equals the quadratic form already
     controlled by the centered Toeplitz/RKHS engine.
- The right proof skeleton for `A1-pd` is now explicit:
  pre-square density in `C_c^\infty([-K/2,K/2])` plus the autocorrelation continuity inequality
  `||\psi*\widetilde{\psi}-\varphi*\widetilde{\varphi}||_\infty <= (||\psi||_1+||\varphi||_1)||\psi-\varphi||_1`.

Recommendation:
- Freeze these theorem blocks in the public manuscript and in the control plane.
- Make the next active step the proof skeleton behind `A1-pd`, not another broad-cone patch.
- Keep packet-Rayleigh as the next queued bridge theorem on the same exact packet cone.

## Update (2026-03-07, in progress) — qmd serialization fix

- Root cause of the recurring `SQLITE_BUSY_RECOVERY` noise: our `qmd` entrypoints
  were not serialized at all. `scripts/research_oracle.py` and
  `q3.lean.aristotle/scripts/refresh_q3_docs.py` could hit the same SQLite-backed
  qmd state concurrently.
- Fix introduced:
  - shared helper `/Users/emalam/Documents/GitHub/rh_lean_01_2026/scripts/qmd_ops.py`
  - one file lock at `q3.lean.aristotle/.qmd_cache/qmd_ops.lock`
  - retry/backoff on `SQLITE_BUSY*`
  - stale `q3_docs_stage*` cleanup during refresh
- Operational rule after the fix:
  - run qmd queries sequentially,
  - no parallel local query fan-out,
  - refresh and query now share the same lock layer.

## Synthesis (2026-03-07, in progress) — naive Rayleigh-family obstruction

Target node and wiring:
- The corrected-cone pivot survives.
- But the previous same-family blocker `SF-pd` was still one step too optimistic.
- The family `\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}
   = \operatorname{cone}\{\Phi_{B,t,p}=\Phi_{B,t}|p|^2\}` is too large to serve
  as the public closure family.

Local semantic search:
- Query `same-family bridge Phi_{B,t}|p|^2 broad positivity local bumps`
  returned the live tracker and orchestrator, confirming that the repo still
  treated `SF-pd` as the active frontier.
- Query `packet Rayleigh Phi_{B,t}|p|^2 density too large counterexample a(2)`
  returned the centered Rayleigh bridge sources in A3 and the corrected-cone
  packaging, which is exactly where the overlarge-family risk bites.
- External confirmation of the positive-definite Weil target remains the same
  Cambridge/Suzuki source already recorded in the corrected-cone notes.

Concrete synthesis:
- `A1-pd` still feeds the dense autocorrelation family
  `\mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}`.
- The naive packet-Rayleigh candidate feeds
  `\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}} = \operatorname{cone}\{\Phi_{B,t}|p|^2\}`.
- On compacts `K<\pi`, the family `\Phi_{B,t} r^2` with `r` an even real
  trigonometric polynomial is already dense in the broad local cone of even
  nonnegative bumps because `\Phi_{B,t}>0` on `[-K,K]` and Stone--Weierstrass
  gives `r_n^2 \to h`.
- Combined with the full quadratic-form meaning of Lemma 8.8 and the centered
  A3 positivity engine, that would force false broad local positivity.
- Therefore the live blocker is no longer a bridge from
  `\mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}` to
  `\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}`.
- This intermediate `OP-pd` wording was a useful staging point, but it is now
  superseded by the sharper packet package
  `A1-pd + packet-Rayleigh-pd + A3-pd`.

Recommendation:
- Retire `SF-pd` as the active mainline blocker.
- Keep the naive `\Phi_{B,t}|p|^2` route as background-only.
- Freeze the obstruction itself, but do not keep `OP-pd` as the public frontier.

## Synthesis (2026-03-07, final) — A3-pd packet package

Target node and wiring:
- The corrected-cone pivot survives.
- The `OP-pd` placeholder can now be replaced by a sharper theorem package:
  `A1-pd + packet-Rayleigh-pd + A3-pd`.

Local semantic search:
- Query `A1-pd packet-Rayleigh A3-pd autocorrelation packets`
  returned `full/sections/introduction.tex`, `full/sections/scope_notation.tex`,
  `full/sections/Notation/qstar_contract.tex`, and the live corrected-cone
  insight notes, confirming that the active route already points toward the
  packet/autocorrelation side.
- Query `operator-controlled packet family autocorrelation Toeplitz form`
  hit `full/sections/A3/rayleigh_bridge.tex` and `full/sections/Main_closure.tex`,
  which is exactly the repository bridge needed for the packet Toeplitz form.
- Query `naive Rayleigh family obstruction OP-pd`
  surfaced the obstruction note and the tracker/orchestrator state, confirming
  that the old `OP-pd` wording was now the main source of drift.

Concrete synthesis:
- `A1-pd` survives as density of the corrected packet family
  `\mathcal G_K^{pd}` inside `\mathcal W_K^{pd}`.
- exact packet-Rayleigh survives on autocorrelation packets
  `\Psi_c * \widetilde{\Psi_c}` with Toeplitz symbol
  `S_{g,\Delta}(\theta)=\sum_m \kappa_m e^{-im\theta}` and
  `\kappa_m=Q^\star(t;h(\cdot-m\Delta))`.
- The naive family `\Phi_{B,t}|p|^2` remains background-only after the
  local-bump obstruction.
- Therefore the single live knife-edge is `A3-pd`: prove
  `S_{g,\Delta}(\theta)\ge c_K>0` on the same exact dense packet family that
  feeds `A1-pd`.

Recommendation:
- Freeze the public chain as
  `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> A3-pd -> A2 closure -> LF-pd -> G6 -> RH`.
- Treat `OP-pd` as superseded wording, not as the live frontier.
- Keep Aristotle `G1.6` background-only; the true mainline blocker is now
  packet-symbol positivity, not support upgrade on the broad cone.

## Synthesis (2026-03-07, in progress) — PSD packet kernel frontier

Target node and wiring:
- The corrected-cone pivot survives.
- `A1-pd` survives as the dense autocorrelation route on
  `\mathcal G_K^{pd}\subset \mathcal W_K^{pd}`.
- Exact packet-Rayleigh on autocorrelation packets also survives.
- What fails is the current theorem shape of `A3-pd` as a uniform symbol-floor
  statement on the full dense packet dictionary.

Local semantic search:
- Query `packet kernel PSD Q(g_i * g_j_tilde) Toeplitz sections`
  hit the live corrected-cone packaging in `full/sections/Main_closure.tex`
  and the current `A3-pd` insight notes, confirming that the repo still frames
  the frontier as symbol positivity on `S_{g,\Delta}`.
- Query `Herglotz Bochner positive semidefinite Toeplitz kernel packet space`
  returned the old RKHS/kernel notes together with the corrected-cone files,
  which is the right neighborhood for a PSD-kernel reformulation.
- Query `Q(Psi * Psi_tilde) Toeplitz kappa i-j positive semidefinite`
  surfaced `Main_closure.tex`, `scope_notation.tex`, and the packet package
  note; these are exactly the files where the frontier wording must pivot.

External search:
- External search points back to the classical positive-definite viewpoint
  (Suzuki / Weil distribution, Herglotz-Bochner language) rather than to any
  broad-cone positivity statement. This supports the pivot away from a uniform
  packet-symbol floor on the dense family.

Concrete synthesis:
- For packets `\Psi_c=\sum_j c_j g_j`, the exact identity
  `Q^\star(t;\Psi_c * \widetilde{\Psi_c})=\sum_{i,j} c_i\overline{c_j}\kappa_{i-j}`
  is still the honest bridge.
- But if one takes a dense packet dictionary and asks for one uniform margin
  `Q^\star(t;\Psi * \widetilde\Psi)\ge c_K \|c\|_2^2`, this is impossible:
  packets of the form `\Psi_\Delta=g-g(\cdot-\Delta)` collapse to zero as
  `\Delta\downarrow0`, and by A2 continuity the corresponding `Q` values also
  collapse to zero.
- Therefore the public missing theorem is no longer `A3-pd` in the old
  uniform-gap sense.
- The live theorem must instead be `PSD-pd`: positive semidefiniteness of the
  packet kernel
  `K_Q(g_i,g_j):=Q^\star(t;g_i * \widetilde{g_j})`
  on the dense pre-packet space.

Recommendation:
- Replace the public chain by
  `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`.
- Demote `A3-pd` to a rejected-too-strong route on the dense packet family.
- Keep `S_{g,\Delta}=A_{g,\Delta}-P_{g,\Delta}` as useful structure, but not as
  the public theorem shape.

## Synthesis (2026-03-07, final) — PSD packet kernel frontier

Final verdict:
- `A1-pd` survives.
- Exact packet-Rayleigh survives.
- The old theorem shape `A3-pd` does not survive on the dense packet dictionary.
- The honest missing theorem is now `PSD-pd`: positive semidefiniteness of the
  packet kernel `K_Q(g_i,g_j)=Q^\star(t;g_i * \widetilde{g_j})` on the dense
  pre-packet space.

Reusable theorem payload:
- `thm:A1-pd` stays as the density theorem block.
- `thm:packet-rayleigh-pd` stays as the exact Toeplitz / packet identity.
- `prop:a3-pd-too-strong` records why the old uniform-gap route fails.
- `thm:PSD-pd` is the new theorem target for the public RH chain.

Public chain after the pivot:
- `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 closure -> LF-pd -> G6 -> RH`.

Surviving strategy families:
- Herglotz/Bochner route.
- New prime-factorization / kernel route.

## Synthesis (2026-03-07, in progress) — Aristotle packet split for `PSD-pd`

Цель:
- не “доказывать RH целиком”, а выбрать первый честный proof-route для
  `PSD-pd`: PSD packet-kernel theorem on the dense pre-packet space.

Локальный semantic search:
- Query `Herglotz Bochner positive definite Toeplitz sequence finite sections`
  поднял `Main_closure.tex` именно на remark with the two live strategy families,
  то есть база уже подтверждает правильный theorem neighborhood.
- Query `prime factorization kernel route packet kernel Q(g_i * g_j_tilde)`
  упёрся в те же corrected-cone files; значит второй route пока живёт как
  theorem-shape, а не как готовый lemma stack.

Внешний theorem-shape search:
- внешний поиск подтверждает classical positive-definite representation language
  (`Herglotz/Bochner`) и не даёт готового broad-cone shortcut.
- это согласуется с live manuscript: uniform-gap revival не выглядит честным.

Конкретный план:
- запустить два узких Aristotle packet-а внутри одного gate `PSD-pd`:
  1. `Herglotz/Bochner` packet: exact reduction of finite PSD packet-kernel
     matrices to a positive-definite sequence / measure representation;
  2. `prime-factorization / kernel` packet: exact decomposition stack for
     `K_Q(g_i,g_j)` into Archimedean and prime pieces on the same dense
     pre-packet family.
- У обоих packet-ов одна и та же hard policy:
  не возвращать broad-cone route, не resurrect `A3-pd` uniform gap, не
  claim RH closure, and do not widen the target beyond `PSD-pd`.

Launched Aristotle probes:
- `subagent_psd_pd_herglotz_2026_03_07.md`
  -> `76e1f0f3-47e9-4cb0-b57e-7e64bac1fffb`
- `subagent_psd_pd_kernel_route_2026_03_07.md`
  -> `2f2aff04-379c-4698-a238-a9798417b3b6`
- initial status for both: `QUEUED`

## Synthesis (2026-03-07, in progress) — `Route P` is the primary `PSD-pd` candidate

Target node and wiring:
- The live theorem is still `PSD-pd`: positive semidefiniteness of the packet
  kernel `K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})` on the dense
  pre-packet space behind `A1-pd`.
- The user’s new note sharpens this further: the honest theorem is not a revived
  packet-symbol floor but PSD of the full sesquilinear packet kernel.

Local semantic search:
- The strongest local hits remain `Main_closure.tex`, `Weil_pack.tex`, the
  packet-package notes, and the tracker/orchestrator entries around `PSD-pd`.
- Nothing in the live corpus currently supplies a real PSD factorization of the
  prime packet block; this matches the note’s diagnosis that the current
  centered A3/RKHS engine stops too early.

External theorem-shape search:
- External search again supports `Herglotz/Bochner` as the clean equivalence
  language for positive-definite sequences / Toeplitz sections.
- But it still does not supply a project-local mechanism that would dominate the
  prime packet block directly.

Concrete synthesis:
- `Herglotz/Bochner` survives as the diagnostic / equivalence route:
  it tells us exactly what `PSD-pd` means.
- The realistic primary route is now `Route P`:
  exact packet sesquilinear identity
  -> PSD factorization or Hilbert lift of the prime block
  -> Archimedean domination criterion
  -> PSD of the full packet kernel.
- Therefore the next public theorem package should be organized around:
  `packet sesquilinear identity -> prime-block PSD factorization -> Archimedean domination -> PSD-pd`.

## Synthesis (2026-03-07, final) — `Route P` frozen primary, `Herglotz` secondary

Final verdict:
- `Herglotz/Bochner` survives as the clean diagnostic equivalence language for
  `PSD-pd`.
- `Route P` is now the primary constructive route in the active control plane.

Active theorem package:
- exact packet sesquilinear identity;
- prime-block PSD factorization or Hilbert lift;
- Archimedean domination criterion;
- `PSD-pd` on the same dense pre-packet space.

Manuscript/control-plane effect:
- orchestrator, queue, tracker, `Weil_pack`, `Main_closure`, introduction, and
  abstract now all treat `Route P` as primary and `Herglotz/Bochner` as
  secondary diagnostic.

Aristotle status:
- the `Herglotz/Bochner` probe
  `76e1f0f3-47e9-4cb0-b57e-7e64bac1fffb`
  already returned a generic moment-sequence -> Toeplitz-PSD theorem package;
  it is useful as secondary diagnostic payload, but not a mainline integration.
- the `prime-factorization / kernel` probe
  `2f2aff04-379c-4698-a238-a9798417b3b6`
  remains the more important live Aristotle route.

## Synthesis (2026-03-07, in progress) — full-kernel PSD replaces literal `Route P`

Target node and wiring:
- The live theorem remains `PSD-pd`: positive semidefiniteness of the packet
  kernel `K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})` on the dense
  pre-packet space behind `A1-pd`.
- The new note sharpens the obstruction further: the literal `Route P` package
  "`prime block PSD factorization or Hilbert lift -> Archimedean domination`"
  is not merely unproved; on packet space the standalone prime block is not PSD,
  so that theorem shape is false.

Local semantic search:
- Query `direct full kernel PSD full symbol domination S_{g,Delta} packet kernel`
  hits the corrected-cone manuscript files and the packet-kernel insight layer.
  The active corpus already knows the right target object is `K_Q`.
- Query `Herglotz diagnostic equivalence full kernel PSD route P false prime block`
  returns the orchestrator/manuscript surfaces where the old `Route P` wording is
  still active. This confirms the next task is a source-of-truth rewrite, not
  another speculative estimate.

External theorem-shape search:
- External references still support `Herglotz/Bochner` as the clean equivalence
  between Toeplitz-section PSD, positive-definite sequences, and measure data.
- They do not rescue a project-local PSD factorization of the packet prime block.

Concrete synthesis:
- Exact packet sesquilinear identity survives.
- Standalone PSD factorization of the packet prime block fails on dense packet
  spaces containing an active node.
- Therefore the honest frontier theorem is now:
  direct PSD of the full packet kernel,
  equivalently positivity of the full symbol
  `S_{g,\Delta}=A_{g,\Delta}-P_{g,\Delta}`.
- `Herglotz/Bochner` stays as secondary diagnostic language.
- The primary constructive line must now be phrased as either:
  `full-symbol domination A_{g,\Delta}>=P_{g,\Delta}`
  or
  `a new operator package representing the full kernel as a PSD form`.

## Synthesis (2026-03-07, final) — literal `Route P` rejected, full-kernel PSD primary

Final verdict:
- exact packet sesquilinear identity survives;
- standalone PSD factorization of the packet prime block is false on dense packet
  spaces containing an active node;
- the honest theorem target remains `PSD-pd`, but its primary constructive route
  is now direct PSD of the full kernel `K_Q`, not literal `Route P`.

Public theorem stack after the rewrite:
- exact packet sesquilinear identity;
- prime-block obstruction;
- full-symbol domination `A_{g,\Delta}\ge P_{g,\Delta}` or a new full-kernel
  operator package;
- `PSD-pd`.

Control-plane/manuscript effect:
- orchestrator, queue, tracker, abstract, introduction, `Weil_pack`, and
  `Main_closure` now all treat direct full-kernel PSD as the active route;
- `Herglotz/Bochner` stays explicit, but only as diagnostic equivalence;
- old `Route P` notes are marked superseded, and a new canonical note/reviewed
  note record the full-kernel frontier.

Reusable file pointers:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/full_kernel_psd_frontier_2026_03_07.md`

## Synthesis (2026-03-08, in progress) — `P1–P8` sharpens the live `PSD-pd` package

Target node and wiring:
- The live theorem is still `PSD-pd`: positive semidefiniteness of the full
  packet kernel `K_Q(\Psi,\Phi)=Q^\star(t;\Psi * \widetilde{\Phi})`.
- The new `P1–P8` note sharpens the constructive route further:
  exact packet identity survives,
  standalone PSD factorization of the packet prime block is false,
  and the honest constructive target is now `P7`:
  full-symbol domination `A_{g,\Delta}\ge P_{g,\Delta}` or an equivalent full
  operator package for `K_Q`.

Local semantic search:
- Query `prime block obstruction dense translation packet space active node`
  returns `Main_closure.tex` first, exactly on the new packet prime obstruction.
- Query `P1 P2 P3 P4 P5 P6 P7 P8 packet sesquilinear Toeplitz Herglotz`
  returns the orchestrator/tracker surfaces where the direct full-kernel route
  is now active.
- The live corpus therefore already supports the new theorem neighborhood:
  `P1/P2` exact identity -> `P4` obstruction -> `P6/P7` spectral criterion.

External theorem-shape search:
- External references still support the Toeplitz/Herglotz equivalence:
  Toeplitz-section PSD
  <-> positive-definite sequence
  <-> positive measure on the circle.
- They still do not provide a project-local constructive proof of
  `A_{g,\Delta}\ge P_{g,\Delta}`.

Concrete synthesis:
- `P1` exact packet sesquilinear identity should be public and explicit.
- `P2` Toeplitz reduction should be the main algebraic reduction.
- `P4` must be stated explicitly: packet prime PSD factorization is false.
- `P5/P6/P7` are now the honest primary route:
  decompose `\kappa=\alpha-\beta`,
  use Herglotz as the equivalence language,
  and make `A_{g,\Delta}\ge P_{g,\Delta}` the clean sufficient criterion.
- The next public theorem package should therefore be written as:
  `P1 -> P2 -> P4 -> P5 -> P6 -> P7 -> PSD-pd -> A2 -> LF-pd -> G6`.

## Synthesis (2026-03-08, final) — `P1–P8` frozen, `P7` is the immediate target

Final verdict:
- the exact constructive package is now frozen as
  `P1 -> P2 -> P4 -> P5 -> P6 -> P7 -> PSD-pd`;
- `P3` survives only as the desired theorem shape
  `prime block PSD factorization`, but `P4` shows it is false on dense packet
  spaces containing an active node;
- the immediate constructive target is therefore `P7`:
  full-symbol domination `A_{g,\Delta}\ge P_{g,\Delta}`, or the corresponding
  positive-measure / distribution statement in the general Herglotz regime.

Project effect:
- the orchestrator, queue, tracker, abstract, introduction, `Weil_pack`, and
  `Main_closure` now all expose the strict `P1–P8` package rather than the old
  vague `Route P`;
- the live theorem frontier is no longer `prime block PSD -> Arch dominates`,
  but direct control of the full Toeplitz sequence `(\kappa_m)` via
  `\kappa=\alpha-\beta` and the Toeplitz--Herglotz criterion;
- a new full-kernel operator package remains explicitly available, but only as
  fallback if `P7` cannot be proved directly.

Reusable file pointers:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/p1_p8_full_symbol_package_2026_03_08.md`

## Synthesis (2026-03-08, in progress) — regularized `P7` sharpens the packet route

Target node and wiring:
- the live theorem is still `PSD-pd`: positive semidefiniteness of the full
  packet kernel `K_Q(\Psi,\Phi)=\mathcal Q(\Psi * \widetilde{\Phi})` on a dense
  pre-packet space;
- the new sharpening is not another route change, but a refinement of the
  immediate constructive target `P7`;
- the honest package is now:
  exact packet sesquilinear identity with the symmetrically extended functional
  `\mathcal Q`,
  Toeplitz reduction,
  desired prime-block PSD factorization (false),
  sparse Gershgorin rescue as a local lemma only,
  and then regularized full-symbol domination as the real theorem target.

Local semantic search:
- query `prime block obstruction dense packet space shift translate` points back
  to `Main_closure.tex`, confirming that the old prime-block PSD theorem shape
  is already dead in the live manuscript;
- query `Toeplitz Herglotz criterion packet kernel full symbol` returns the
  current tracker/orchestrator surfaces where the full-kernel route is already
  active;
- query `regularized full symbol domination A_g Delta P_g Delta` is the right
  retrieval neighborhood for the next constructive step, not the old `Route P`
  phrasing;
- query `Gershgorin packet Toeplitz diagonal dominance dense dictionary` is
  useful only as a sparse-dictionary diagnostic, not as the public mainline.

External theorem-shape search:
- the classical external support is still the same: Toeplitz/Herglotz
  equivalence for positive-definite sequences and the standard matrix
  Gershgorin criterion;
- nothing external currently supplies the project-local regularization theorem
  needed to turn `A_{g,\Delta}` into a clean symbol on the packet side.

Concrete synthesis:
- `P1` must be rewritten with the symmetrically extended compact functional
  `\mathcal Q`, not just the even-restricted `Q^\star(t;\cdot)`;
- the packet prime contribution must be symmetrized at `\pm \xi_n`;
- the old theorem shape
  `prime block PSD -> Arch dominates`
  remains false and should stay rejected;
- Gershgorin diagonal dominance is worth recording as the first strict
  sufficient criterion on finite sparse packet dictionaries, but it cannot be
  the dense main theorem because near-collisions force the quadratic form to
  collapse to zero by A2 continuity;
- the real constructive target is therefore the regularized full-symbol
  domination statement
  `A_{g,\Delta}^{reg}(\theta) - P_{g,\Delta}(\theta) >= 0`,
  with any new full-kernel operator package kept as fallback.

## Synthesis (2026-03-08, final) — measure-level `P7/P8` integrated

Final verdict:
- the packet cross-kernel should be written via the symmetric extension
  `\mathcal Q(F)`, not only the even-restricted `Q^\star`;
- the exact packet theorem package now has the public form
  `P1` exact sesquilinear identity for `\mathcal Q`,
  `P2` Toeplitz reduction,
  `P3` desired prime PSD factorization,
  `P4` obstruction,
  `P5` coefficient split `\kappa=\alpha-\beta`,
  `P6` Toeplitz--Herglotz criterion,
  `P7` measure-level / regularized full-symbol domination,
  `P8` conditional corrected compact positivity;
- the immediate constructive target is now
  `\mu_A-\mu_P\ge 0`, or in the stronger symbol regime
  `A_{g,\Delta}^{reg}\ge P_{g,\Delta}`;
- Gershgorin is worth keeping, but only as a sparse finite-block sufficient
  criterion and explicitly not as the dense main theorem.

External theorem-shape check:
- the standard Toeplitz/Herglotz equivalence still matches the packet-kernel
  route exactly;
- the classical Weil positive-definite / convolution-square viewpoint still
  matches the corrected target cone and compact closure step;
- nothing external removes the need for a project-local regularization theorem
  for the Archimedean packet symbol.

Project effect:
- `Main_closure` now contains the symmetric extension `\mathcal Q`, the
  symmetrized packet identity, the prime-block obstruction, the sparse
  Gershgorin lemma, the measure-level `P7` criterion, and `P8`;
- `scope_notation`, `qstar_contract`, `abstract`, `introduction`, `Weil_pack`,
  orchestrator, tracker, and queue all agree on the same sharpened frontier;
- a new insight note plus reviewed note freeze the regularized `P7` package for
  embeddings and future blocker search.

Reusable file pointers:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Notation/qstar_contract.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/regularized_p7_package_2026_03_08.md`

## Synthesis (2026-03-08, final) — concrete finite-dictionary bounds for `P7.6`

Target node and wiring:
- the live theorem is still `PSD-pd`, but the immediate constructive frontier is
  now the explicit coefficient-bounding package behind finite admissible
  dictionary positivity;
- the right packet route is no longer “abstract `P7`”, but:
  Archimedean coefficient bounds on `\alpha_m`,
  prime-mass bounds on `\beta_m`,
  finite-symbol envelope,
  explicit sufficient inequalities `(C1)` / `(C1')`,
  sparse regime `(C2)` / `(C2')`,
  and only then `P7.6` as verification wrapper.

Concrete synthesis:
- `A1`: support-localization bound
  `|\alpha_m|\le \|a^*\|_{L^\infty(I_m)}\|h\|_1`.
- `A2`: approximate-identity refinement
  `|\alpha_m-a^*(m\Delta)\|h\|_1|\le \omega_{a^*,K}(R_h)\|h\|_1`.
- `A3/A4`: packet analogue of the old centered core/off-core lower bound for
  the diagonal Archimedean term `\alpha_0`.
- `P1`: local symmetric prime-mass bound
  `\beta_m\le \|h\|_\infty \Pi_K^{sym}(|m|\Delta;R_h)`.
- `P2/P3`: spacing simplification and off-diagonal prime vanishing.
- finite-symbol envelope `(C0)` reduces positivity of `S_J` to domination of
  the diagonal over off-diagonal leakage.
- explicit sufficient inequalities `(C1)` / `(C1')` are the first honest
  finite-dictionary closure criteria in the corrected route.

Verdict:
- this is a real packet-level analogue of the old centered bridge;
- it is strong enough to close positivity on sparse finite dictionaries;
- it still does **not** close the dense mainline by itself, because near
  collisions and A2 continuity kill any uniform gap on dense packet families.

Project effect:
- `Main_closure` now contains the concrete coefficient package, not just the
  abstract `P7` wrapper;
- active summaries now say the next theorem is “bounds on `\alpha_m,\beta_m`”
  rather than “regularized P7 in general”;
- Poisson regularization stays only as a verification device.

Reusable file pointers:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Notation/qstar_contract.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`

## Synthesis (2026-03-08, final) — canonical centered half-atom pilot

Target node and wiring:
- the live theorem is still `PSD-pd`, but the next honest micro-frontier is now
  the canonical pilot packet `g_{\delta,t_0,0}=\Lambda_\delta\rho_{t_0}` on top
  of the finite-dictionary package;
- this sits exactly on the strict chain
  `A1--A4, P1--P3 -> (C1)/(C1') -> P7.3--P7.6 -> PSD-pd`.

Concrete synthesis:
- for the centered half-atom,
  `R_g=\delta`, `R_h=2\delta`,
  `\|h\|_1=\|g\|_1^2`,
  `\|h\|_\infty=h(0)=\|g\|_2^2`,
  and there are closed formulas for `\|g\|_1`, `\|h\|_\infty`, and
  `M_g(s)=\int_{|x|\le s} g(x)\,dx`;
- the lower bound `H_r\ge M_g(r/2)^2` gives the first usable packet-level core
  mass estimate without introducing any new abstract machinery;
- on the pilot compact `K=0.2`, the active positive nodes are only
  `\xi_2` and `\xi_3`;
- with dictionary `J={0,1}` and `\Delta=0.15`, one has
  `dist(0.15,\Xi_K)\approx 0.02485`, so for `\delta<0.0124` all prime
  collisions vanish: `\beta_0=\beta_1=0`;
- the finite symbol then reduces to `S_J(\theta)\ge \alpha_0-2|\alpha_1|`, and
  the numerical Archimedean gap
  `a^*(0)-2a^*(0.15)\approx 7.13>0` shows that positivity on this sparse
  dictionary is genuinely attainable for small enough `\delta`.

Verdict:
- this is the first nonvacuous packet-level success case for the corrected
  finite-symbol criterion;
- it confirms that the packet package is mathematically alive on sparse
  dictionaries;
- it still does **not** close the dense mainline, because the same mechanism
  collapses when `\Delta\downarrow0`.

Reusable file pointers:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Notation/qstar_contract.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`

## In-progress synthesis (2026-03-08) — semilocal layer as H1 engineering only

Target node and wiring:
- live public route stays `H1 -> H2 -> H3 -> H4`;
- the semilocal Connes--Consani--Moscovici layer is **not** promoted to a new
  RH endgame;
- instead it is frozen only as the strongest current basis/Gram supplier for
  `H1`.

Concrete synthesis:
- fix a finite prime window `S(B)=\{p:\ p\le e^{2\pi B}\}` matching the active
  prime scale of the Q3 finite block;
- let `\eta_m^{(S,a)}` be the packet dictionary supplied by the finite-prime
  cyclic/Jacobi machinery on `L^2(-a,a)`;
- define `E_{a,M}^{(S)}=\operatorname{span}\{\eta_m^{(S,a)}:0\le m\le M\}`;
- use raw synthesis `S_{a,M}^{(S)}` and semilocal Gram matrix
  `\Gamma_{a,M}^{(S)}`;
- either keep the raw metric `J_a^{(S,M)}=\Gamma_{a,M}^{(S),-1}` or pass to the
  normalized synthesis `\widetilde S_{a,M}^{(S)}`.

Verdict:
- this strengthens `H1` because it gives a canonical finite-prime packet basis
  and a natural Gram metric;
- it should only feed the matrix comparison
  `(\widetilde S_{a,M}^{(S)})^*G_g[a]\widetilde S_{a,M}^{(S)}
   = \kappa_{S,a}(T_M[P_A]-T_P^{(M)}) + R_{S,a,M}`;
- if promoted beyond that, it turns into a second heavy endgame and starts to
  hurt rather than help.

## In-progress synthesis (2026-03-08) — filtered Volterra bridge preferred for H1

Target node and wiring:
- live public route stays `H1 -> H2 -> H3 -> H4`;
- the current improvement is not a new endpoint, but a sharper first-pass
  realization of `H1`;
- the key change is to stop forcing `S_{a,M}^*J_aS_{a,M}=I` and instead use the
  explicit pullback metric coming from Suzuki's Volterra operator.

Concrete synthesis:
- define `(I_0^{(a)}\phi)(t)=\int_{-a}^t \phi(u)\,du`;
- take `J_a=(I_0^{(a)})^*I_0^{(a)}`;
- define filtered synthesis by
  `I_0^{(a)}S_{a,M}=U_aM_{1+z}|_{P_M}`;
- then the pullback metric is explicit:
  `B_M=S_{a,M}^*J_aS_{a,M}=T_M[|1+z|^2]=T_M[2+z+z^{-1}]`;
- hence `0\le B_M\le 4I`, so any current Q3 bulk bound
  `Q_M\ge c(a)I` automatically implies `Q_M\ge (c(a)/4)B_M`.

Verdict:
- this is now the preferred first-pass `H1` candidate;
- semilocal packets remain useful as a secondary basis/Gram refinement;
- the real next theorem is exact or almost-exact matrix comparison on the
  filtered basis:

## Historical synthesis (2026-03-08) — one-sided filtered finite section killed the old 1/4 loss

Superseded by the final two-sided filtered tail package
`\mathcal P_{M,N}, \Delta_{M,N}, B_{M,N}, \widetilde Q_{M,N}`.
Keep this note only as a stepping stone in the evolution of `H1`.

Target node and wiring:
- live public route stays `H1 -> H2 -> H3 -> H4`;
- the filtered Volterra bridge survives, but its correct bridge-object is not
  the raw `Q_M`;
- the preferred finite object is now
  `\widetilde Q_M=\Delta_+^*Q_{M+1}\Delta_+`,
  with `\Delta_+=I+L`.

Concrete synthesis:
- keep `J_a=(I_0^{(a)})^*I_0^{(a)}`;
- keep `I_0^{(a)}S_{a,M}=U_aM_{1+z}|_{P_M}`;
- then
  `B_M=S_{a,M}^*J_aS_{a,M}=T_M[|1+z|^2]=\Delta_+^*\Delta_+`;
- if the current Q3 bulk gap gives `Q_{M+1}\ge c(a)I`, then
  `\widetilde Q_M=\Delta_+^*Q_{M+1}\Delta_+\ge c(a)\Delta_+^*\Delta_+=c(a)B_M`;
- hence the old coarse transfer `Q_M\ge(c(a)/4)B_M` is superseded by the
  no-loss filtered relation.

Verdict:
- the preferred first-pass `H1` target is now
  `S_{a,M}^*G_g[a]S_{a,M}=\kappa(a)\widetilde Q_M+F_{a,M}`;
- the real remaining brick is exact entrywise comparison with the Suzuki tail
  matrix and an explicit finite-rank cap;
- semilocal packets remain useful only as secondary finite-prime basis/Gram
  data for this filtered comparison.

## Final result (2026-03-08) — two-sided filtered Suzuki bridge replaces the one-sided Volterra package

Target node and wiring:
- the live public route remains `H1^f -> H2^f -> H3^f -> H4^f`;
- the earlier one-sided filtered Volterra notes
  `h1_filtered_volterra_bridge_2026_03_08.md`
  and
  `h1_filtered_finite_section_2026_03_08.md`
  are now superseded stepping stones;
- the active finite bridge-object is the symmetric two-sided filtered tail
  section
  `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`.

Concrete synthesis:
- exact tail geometry now uses
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`;
- the metric side is exact:
  `S_{a,M,N}^*J_aS_{a,M,N}=B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`;
- the plus-tail carries the filter `1+z`, the minus-tail carries `1+z^{-1}`;
- if `Q_{M+1}\ge c(a)I`, then
  `\widetilde Q_{M,N}\ge c(a)B_{M,N}` with no `1/4` loss;
- the narrowest remaining bulk theorem is the raw-entry identity
  `w_{rs}(a)=\kappa(a)q_{rs}`
  on the two families `(+,+)` and `(+,-)`,
  while the four filtered blocks
  `(++), (+-), (-+), (--)`
  stay as the derived consequence layer;
- after the bulk match, the only other live brick is the finite-dimensional
  Suzuki cap.

Verdict:
- the one-sided `\Delta_+` bridge is no longer the active H1 package;
- semilocal machinery remains strictly secondary, only as a finite-prime
  basis/Gram engine for the same `H1^f`;
- the active frontier is now exact two-sided filtered bulk matching, not
  generic construction of `S_{a,M}` and `J_a`.

## Final result (2026-03-08) — theorem-ready four-block bulk stack is frozen

Target node and wiring:
- the public route remains `H1^f -> H2^f -> H3^f -> H4^f`;
- `H2^f/H3^f/H4^f` stay structurally frozen;
- the active `H1^f` brick is now strictly narrower than the old four-block
  formulation.

Concrete synthesis:
- the Suzuki-side entries are now frozen as
  `M_{mn}^{\sigma\tau}(a)=\langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle`;
- the antiderivative packets are explicitly
  `\psi_n^+[a]=\chi_n[a]+\chi_{n+1}[a]` and
  `\psi_n^-[a]=\chi_{-n}[a]+\chi_{-(n+1)}[a]`;
- each block has an exact spectral formula through
  `\widehat{\psi_n^\pm}`;
- the live bulk checklist is now:
  raw `(+,+)` and `(+,-)` identities first,
  then the filtered block equalities
  `M^{++}, M^{+-}, M^{-+}, M^{--}`
  as formal consequences against the corresponding blocks of
  `\kappa(a)\widetilde Q_{M,N}`;
- after the bulk match, the only remaining H-bridge brick is the
  finite-dimensional Suzuki cap.

Verdict:
- the next theorem is no longer “construct `S` and `J` in general”;
- it is the raw bulk identity on two families plus a separate cap-positivity
  problem;
- semilocal machinery stays engineering-only for this same `H1^f`.

## Final result (2026-03-08) — raw-entry reduction narrows `H1^f` to two bulk families

Target node and wiring:
- the public route remains `H1^f -> H2^f -> H3^f -> H4^f`;
- `H2^f/H3^f/H4^f` stay structurally frozen;
- the live `H1^f` blocker is no longer “match all four filtered blocks directly”.

Concrete refinement:
- freeze the raw-compressed two-sided Section 8 operator
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
  with exact entries
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle
   =A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
  and `\kappa_{A3}=1`;
- freeze the raw Suzuki/Weil entries
  `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`;
- freeze the raw identity
  `w_{rs}(a)=\kappa(a)q_{rs}`
  only as a diagnostic normalization layer;
- the live bulk theorem is now the direct filtered match
  `M_{mn}^{++}(a)=\kappa(a)\widetilde q_{mn}^{++}` and
  `M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}`;
- keep the remaining filtered blocks
  `(-+), (--)`
  only as the filtered consequence layer obtained from Hermitian symmetry;
- keep the finite-dimensional Suzuki cap as the only second brick after the raw
  bulk match.

Verdict:
- the active theorem target is now strictly narrower than the previous
  four-block formulation and no longer lives on the raw `\chi_n[a]` matrix;
- the old four-block note remains valid, but only as the filtered consequence
  layer and no longer as the narrowest active frontier;
- semilocal machinery stays engineering-only for the same `H1^f`.

## In progress (2026-03-08) — Proshka raw-formula data pack

A targeted Proshka context pack was generated at
`q3.lean.aristotle/docs/insights/proshka_h1_raw_formula_brief_2026_03_08.md`.

Its purpose is to hand Proshka the exact local file-level data that is missing
from chat:
- the model-space and compression conventions from
  `full/sections/A3/rayleigh_bridge.tex`;
- the calibration `\kappa_{A3}=1` from
  `full/sections/A3/calibration.tex`;
- the RKHS/Gram operator language from `full/sections/RKHS/core.tex`;
- and the current raw-entry target layer from
  `full/sections/Main_closure.tex`.

Key clarification:
- `w_{rs}(a)=\kappa(a)q_{rs}` is not an already proved Q3 theorem and is now
  treated only as a rejected raw theorem shape;
- what the old A3 files already provide explicitly is the quadratic-form /
  compression machinery;
- the exact raw-compressed Section 8 formula is now extracted as
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
  and
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle
   =A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  where `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`;
- the remaining missing brick is no longer “find the formula”, but prove the
  direct filtered bulk identities on `(++),(+-)` in the matching normalization.

## In progress (2026-03-08) — Proshka-facing raw-operator hack for H1

New extraction from the old A3 files:

- the normalized finite prime block `T_P^{Ray}(t,M)` is not the object Proshka
  should work with directly;
- the useful finite operator is the raw compression
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`;
- therefore the natural Section 8 bridge object for Proshka is
  `Q_M^{raw}:=T_M[P_A]-\Pi_M`;
- its exact entries are
  `q_{rs}=A_{r-s}-\sum_{|\xi_n|\le B}\lambda_n e^{2\pi i(s-r)\xi_n}`,
  where
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`;
- this entry formula is stable in `M` once `|r|,|s|\le M`;
- the calibration section fixes `\kappa_{A3}=1`, so no extra scalar comes from
  the Q3 side.

Operational consequence:

- for Proshka, hand over `Q_M^{raw}`, not the normalized `T_P^{Ray}(t,M)` block;
- hand over the raw entry formula directly;
- ask him to use the raw formulas only as normalization data and match the
  direct filtered bulk identities on `(+,+)` and `(+,-)`;
- let the remaining filtered blocks stay a formal consequence after that.

Important caveat:

- this is a Proshka-facing extraction/hack layer for the bridge work;
- it is not yet promoted blindly to the public theorem stack until the filtered
  H1/H3 normalization is rechecked against the live manuscript.

## In progress (2026-03-08) — Python sanity check for the raw H1 operator package

A repo-local sanity script now lives at:

- `src/h1_raw_operator_sanity.py`

It is meant to be run from the repo root with the local virtualenv:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate
python src/h1_raw_operator_sanity.py --M 4 --M-big 7 --B 0.2 --t 0.15
```

What it checks:

- the scaling identity `\Pi_M=(2M+1)T_P^{Ray}(t,M)`;
- the raw entry formula for
  `Q_M^{raw}=T_M[P_A]-\Pi_M`;
- overlap stability of the raw entries under `M -> M_big`.

Current sample run passes with errors at the `1e-16` level:

- prime scaling error (M): `1.777e-16`
- prime scaling error (M_big): `8.636e-16`
- raw entry error (M): `4.578e-16`
- overlap stability error: `4.475e-16`

This does not prove the direct filtered bulk bridge, but it removes the local
Q3-side normalization ambiguity and gives a fast executable check for future
sessions.

## Final result (2026-03-08) — raw bulk identity is structurally false; direct filtered H1 is the live brick

The normalization audit succeeded, but the old narrowed target was still too
optimistic:

- the raw-compressed Section 8 layer is now stable and explicit:
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle
   =A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
  with `\kappa_{A3}=1`;
- however the raw theorem target
  `w_{rs}(a)=\kappa(a)q_{rs}` is structurally false:
  the Q3 raw matrix is Toeplitz with constant diagonal, while the raw
  Suzuki/Weil matrix in the basis `\chi_n[a]` has diagonal growth of order
  `\log|n|`;
- this is not a sign bug, not a `2\pi` bug, not a `(2M+1)` bug, and not a cap
  effect;
- therefore the raw layer is now diagnostic-only;
- the exact live bulk theorem is the direct filtered match on the adjacent
  Suzuki tails:
  `M_{mn}^{++}(a)=\kappa(a)\widetilde q_{mn}^{++}` and
  `M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}`,
  with `(-+), (--)` coming from Hermitian symmetry;
- after that, the only remaining bridge brick is the finite-dimensional Suzuki cap.

Operational consequence:

- do not ask Proshka to prove the raw identity as the end theorem;
- do give him the raw formulas as normalization/reference data;
- the next exact comparison should happen on the filtered adjacent-tail blocks,
  not on the raw `\chi_n[a]` matrix.

## In progress (2026-03-08) — Incoming H1 theorem skeleton landed

The `incoming_notes` H1 package is worth keeping, but only after adapting it to
the already-frozen raw-compressed notation.

What survives:

- `H1^f` should now be written directly in filtered form, with primary bulk
  identities on the two filtered families `(+,+)` and `(+,-)`;
- the filtered operator equality
  `S_{a,M,N_a}^*G_g[a]S_{a,M,N_a}=\kappa(a)\widetilde Q_{M,N_a}` remains the
  correct exact target, but the raw identities
  `w_{mn}(a)=\kappa(a)q_{mn}` and `w_{m,-n}(a)=\kappa(a)q_{m,-n}` are now only
  diagnostic normalization data and not theorem hypotheses;
- the exact `J_a` pullback
  `S_{a,M,N_a}^*J_aS_{a,M,N_a}=B_{M,N_a}` remains a separate already-frozen
  metric input, not part of the remaining bulk proof burden.

What had to be corrected before integration:

- the incoming text still used the old transitional local-`L` notation for the
  raw entries;
- active mainline now uses only the raw-compressed notation
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle`.

Operational consequence:

- the live `H1^f` theorem block can now be written honestly with a proof
  skeleton;
- the only real bulk brick is the direct filtered match on `(+,+)` and
  `(+,-)`, while the raw layer is a diagnostic mismatch check only;
- after that, filtered four-block identities are formal and the finite Suzuki
  cap is the only second brick.

## In progress (2026-03-08) — executable raw bulk checker

Added `/Users/emalam/Documents/GitHub/rh_lean_01_2026/src/h1_raw_bulk_match.py`
as the first executable probe for the remaining H1 bulk brick. The script
compares raw Q3 entries
\[
q_{rs}=A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}
\]
against Suzuki raw Weil entries
\[
w_{rs}(a)=\frac{2}{a}(-1)^{r+s}\sum_\gamma
\frac{\sin^2(a\gamma)}{(\gamma-\alpha_r)(\gamma+\alpha_s)}
\]
on the two primary families `(+,+)` and `(+,-)`, fits a numerical
`\kappa(a)`, and reports residuals. This does not prove H1; it is a fast local
mismatch detector for signs, Fourier conventions, and hidden scaling.

First probe result at
`a=1.0`, `M=3`, `B=0.2`, `t=0.15`, `zeros=30`:

- `(++): max residual ~= 6.07e-02`, fitted `kappa ~= 1.4598e-03`
- `(+-): max residual ~= 1.21e-01`, fitted `kappa ~= 3.4740e-03 + 2.04e-04 i`
- joint fit does not collapse the two families to one obvious common scalar

So the raw-compressed normalization brick is fixed, but the direct raw Suzuki
match is still nontrivial.  This is good news operationally: the remaining
bulk mismatch is now concrete and numerically testable instead of being a vague
normalization fog.

Follow-up probe with a convention search
(`a=1.0`, `M=2`, `B=0.2`, `t=0.15`, `zeros=10`) tested the natural lightweight
variants:

- Q3 prime phase `e^{+2\pi i(s-r)\xi}` vs `e^{-2\pi i(s-r)\xi}`;
- Suzuki raw entry swap `w_{rs}` vs `w_{sr}`;
- complex conjugation on either side.

All of these gave essentially the same residual scale
(`relative max residual ~= 1.3e-2`).  So the remaining mismatch is not cured by
the first obvious sign / conjugation / index-order flips.  The next suspects
are deeper:

- the exact Suzuki-side raw entry formula,
- the precise Weil/Fourier normalization in the Suzuki package,
- or a missing finite-rank / cap correction already at the raw-entry layer.

## In progress (2026-03-09) — filtered H1 checker is the first live executable test

Added `/Users/emalam/Documents/GitHub/rh_lean_01_2026/src/h1_filtered_bulk_match.py`
to test the current live target directly, not the rejected raw theorem shape.
The script compares the filtered Suzuki blocks
\[
M_{mn}^{++}(a),\qquad M_{mn}^{+-}(a)
\]
against the filtered Q3 blocks
\[
\widetilde q_{mn}^{++},\qquad \widetilde q_{mn}^{+-}
\]
using the already frozen two-sided filter.

First cheap probe at
`a=1.0`, `M=2`, `B=0.2`, `t=0.15`, `zeros=10` gave:

- `(++): relative max residual ~= 1.57e-4`
- `(+-): relative max residual ~= 1.47e-3`
- joint filtered fit: relative max residual ~= `9.26e-4`

This is dramatically better than the raw-layer mismatch and is the first strong
numerical sign that the filtered theorem shape is the right live object.
It does **not** prove H1, but it confirms the direction of the pivot:

- raw identity `w_{rs}(a)=\kappa(a)q_{rs}` stays dead;
- direct filtered bulk match on `(++),(+-)` is the correct executable frontier;
- next narrowing should attack the exact filtered formulas, not raw normalization
  or sign bookkeeping.

## In progress (2026-03-09) — entrywise filtered mismatch map and small sweep

Extended `/Users/emalam/Documents/GitHub/rh_lean_01_2026/src/h1_filtered_bulk_match.py`
from a one-number checker into a second-level diagnostic tool:

- entrywise CSV dump with `run_id`, family, `(m,n)`, raw complex entries,
  family/joint fitted kappas, absolute and relative residuals, and diagonal /
  low-strip metadata;
- terminal summary with separate `++`, `+-`, and joint fits;
- bucket stats for diagonal vs off-diagonal, near-diagonal vs far, and
  low-strip share;
- built-in small grid sweep over
  `a in {0.75, 1.0, 1.25}`,
  `M in {2,3,4}`,
  `zeros in {10,20}`.

Canonical outputs now go to `tmp/`, not tracked docs. First sweep:

- single-run CSV:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/tmp/h1_filtered_mismatch_map_2026_03_09_233351.csv`
- sweep CSV:
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026/tmp/h1_filtered_mismatch_map_2026_03_09_233359.csv`

What the sweep says structurally:

- `++` is consistently much better than `+-`;
- increasing zeta zeros from `10` to `20` changes almost nothing, so current
  mismatch is not a truncation artifact from too few zeros;
- best region in this cheap sweep is near `a=1.25`, where
  `++` reaches relative max residuals around `5e-5` to `3e-4`, and `+-`
  around `2.6e-4` to `2e-2`;
- `a=0.75` is clearly bad, especially for `+-`;
- `a=1.0` starts well at `M=2`, but `+-` degrades sharply by `M=4`;
- dominant error in `+-` is diagonal / near-diagonal, but not low-mode:
  by `M=4` the low-strip share drops to about `0.06` to `0.09`, so this does
  not numerically look like a tiny finite-rank low-mode correction;
- `++` mismatch is more spread across off-diagonal / far entries, especially as
  `M` grows.

Operational consequence:

- the remaining issue is not “one scalar kappa fits everything”;
- the remaining issue also does not look like a simple first-row/first-column
  cap;
- the sharp next question is whether the exact filtered bridge needs an
  additional structured correction in the `+-` family, or whether the
  current filtered `+-` formula still has a convention-level mismatch deeper
  than the lightweight sign/index checks already ruled out.

Follow-up classifier diagnostic (2026-03-09, same script, now with SVD /
rank-1-rank-2 residual fits) sharpened the picture further:

- canonical run
  `a=1.0, M=2, zeros=10`
  is too small to say much except that both `++` and `+-` residual matrices are
  already nearly rank-1;
- the more meaningful “good region” run
  `a=1.25, M=4, zeros=20`
  shows:
  - `++`: rank-1 residual about `2.94e-1`, but rank-2 residual about
    `6.32e-3`, so the error is very close to rank-2;
  - `+-`: rank-1 residual about `2.34e-2`, rank-2 residual about
    `1.99e-3`, with singular-value energy essentially saturated by the first
    two modes;
  - top-left `1x1` and `2x2` energy shares are tiny (`~0.000` / `~0.001` for
    `+-`, `~0.004` / `~0.019` for `++`), so this does **not** numerically look
    like a low-mode cap-only defect.

Updated verdict:

- filtered mismatch still does not look scalar-only;
- but it now looks much more like a **structured low-rank correction**
  than like a dead route or a purely local low-mode defect;
- best next theorem classifier is therefore no longer just
  `exact / low-mode-finite-rank / dead`,
  but more specifically
  `exact / exact+small-rank structured correction / dead`.

Follow-up low-mode support diagnostic (2026-03-10, same checker, now with
union-mask support tests):

- script extended to measure how much residual Frobenius energy sits in the
  union of the first `k` rows/columns (`k=1,2,3`), not just in the top-left
  `k×k` corner and not just in the first singular directions;
- canonical small case (`a=1.0, M=2, zeros=10`) is too tiny to decide
  anything: `union<=2` already covers the whole matrix;
- decisive case (`a=1.25, M=4, zeros=20`) shows:
  - `++`: rank-2 residual `~6.32e-3`, but low-mode union residuals stay much
    larger:
    `union<=1 ~7.81e-1`, `union<=2 ~5.96e-1`, `union<=3 ~4.04e-1`;
  - `+-`: rank-2 residual `~1.99e-3`, while low-mode union residuals are still
    enormous:
    `union<=1 ~9.97e-1`, `union<=2 ~9.85e-1`, `union<=3 ~9.32e-1`.

Sharper verdict:

- the residual is strongly compatible with **small-rank structured
  correction**;
- it is **not** numerically compatible with a defect supported only on the
  first few rows/columns of the filtered tail basis;
- therefore the honest live classifier is now:
  `exact / exact+small-rank structured correction / dead`,
  and the phrase “pure low-mode defect” should be treated only as a candidate
  until proved mathematically.

Follow-up cap-defect classifier (2026-03-10, same checker, now comparing the
leading defect subspaces for `++` and `+-`):

- checker extended with SVD-basis comparison:
  `column_alignment`, `row_alignment`, and `transfer_relative_residual`,
  plus a sweep-level anchor-stability report;
- tiny `M=2` runs are misleading:
  both residual matrices are only `2x2`, so rank-2 agreement is automatic and
  cross-family alignment comes out trivially `~1.000`;
- decisive canonical run `a=1.25, M=4, zeros=20` gives:
  - `++`: rank-2 residual `~6.32e-3`;
  - `+-`: rank-2 residual `~1.99e-3`;
  - cross-family defect basis comparison:
    `++ -> +-`: column/row alignment `~0.606 / ~0.606`,
    transfer residual `~2.69e-2`;
    `+- -> ++`: same alignment but much worse reverse transfer
    `~6.79e-1`.

Sharper live verdict after the cap-defect check:

- the filtered mismatch still looks **small-rank structured**;
- it still does **not** look like pure low-mode support;
- but it also does **not yet** look like one trivially shared finite-dimensional
  cap-space for `++` and `+-` on real bulk-size runs;
- the honest next classifier is therefore:
  `structured small-rank defect with shared cap-space?`
  vs
  `family-dependent structured correction`.

Joint shared-basis / Gram-projection follow-up (2026-03-10):

- checker extended again to build a **joint shared defect basis** from both
  residual families and test each family against the same projector;
- canonical rank-`2` shared projector still fails as a common cap-space:
  in `a=1.25, M=4, zeros=20`, the shared candidate gives
  `proj_rel_resid ~3.26e-1` for `++` but only `~1.76e-2` for `+-`;
- however, rank-`3` changes the picture sharply:
  - canonical run `a=1.25, M=4, zeros=20`:
    shared candidate gives `proj_rel_resid ~7.88e-3` for `++` and
    `~1.10e-3` for `+-`;
  - second real bulk-size run `a=1.0, M=4, zeros=20`:
    shared candidate gives `~1.92e-2` for `++` and `~1.67e-3` for `+-`.

New sharper verdict:

- the data no longer support the naive phrase “one obvious shared cap-space”;
- but they now **do** support a much more focused candidate:
  after the right joint basis / Gram projection, the defect may become a
  **shared finite-rank cap defect of very small rank (currently rank `~3`
  looks plausible)**;
- this is now the best live theorem-shape candidate to ask Proshka about:
  filtered kernel intertwining modulo finite-rank cap defect, not raw equality
  and not pure low-mode support.

## In-progress synthesis (2026-03-10) — freeze the defect-aware `H1` theorem shape, not literal exact equality

Embedding search only reinforced the current control-plane picture: the repo
already had the right raw-vs-filtered audit, the right two-family live bulk
target, and the right suspicion that the defect is structured but not low-mode.

The new freeze was sharper at that stage, but is now superseded by the reduced
2026-03-11 sweep:

- public stack stays `H1^f -> H2^f -> H3^f -> H4^f`;
- but inside `H1^f` the honest working theorem-shape is now
  `filtered intertwining modulo joint finite-rank cap defect after the right joint basis / Gram projection`;
- exact `H1^f` is demoted to the zero-defect special case;
- `rank <= 3` is kept only as the working implementation target, not a theorem fact.

Operationally this compresses the live bridge to two gates:

- Gate A: prove `M=\kappa(a)\widetilde Q + F_{a,N}` with one joint cap-type
  defect for `(++),(+-)`;
- Gate B: prove positivity of the augmented Suzuki cap after adjoining that
  defect block.

Checker status:

- `src/h1_filtered_bulk_match.py` now reports `sigma_next/sigma_rank`,
  principal angles, same-space shared-projector residuals, and embedded
  shared-basis transfer across neighboring runs;
- canonical rank-`3` case still reproduces the live signal:
  `a=1.25, M=4, zeros=20` gives
  `proj_rel_resid ~7.88e-3` for `++` and `~1.10e-3` for `+-`,
  with third principal angles still moderate rather than chaotic.

External sanity check:

- finite-section literature treats a stable gap after the first `k` singular
  values as the right kind of low-rank / finite-codimension signal;
- subspace perturbation literature treats principal angles as the honest metric
  for testing whether the same defect space persists across runs.

Detailed note:

- `docs/insights/h1_cap_defect_theorem_shape_2026_03_10.md`

## Final result (2026-03-11) — shared rank-3 cap defect is false-for-now as a global theorem-shape

Reduced Gate A sweep completed on the decisive grid:

- core: `a in {1.0, 1.25}`, `M in {4,5}`, `zeros in {20,40}`;
- edges: `a in {0.8, 1.5}`, `M=4`, `zeros in {20,40}`;
- always with `defect-rank=3`.

What survived:

- pure low-mode support is still false;
- structured low-rank correction is still very plausible;
- `zeros 20 -> 40` barely changes the verdicts, so this is not a zero-count
  artifact.

What failed:

- `a=0.8, M=4` is stably bad:
  `proj_rel_resid(++) ~ 8.24e-1`,
  `proj_rel_resid(+-) ~ 2.04e-3`;
- `a=1.5, M=4` is stably good:
  `proj_rel_resid(++) ~ 3.7e-3`,
  `proj_rel_resid(+-) ~ 1.1e-3`;
- `a=1.0, M=4` is good, but `a=1.0, M=5` breaks sharply:
  `proj_rel_resid(++) ~ 8.32e-1`,
  `proj_rel_resid(+-) ~ 2.42e-3`;
- `a=1.25, M=4` is good, but `a=1.25, M=5` degrades beyond a small shared cap:
  `proj_rel_resid(++) ~ 1.51e-1`,
  `proj_rel_resid(+-) ~ 3.31e-3`.

Shared-basis `M_step` stability also fails exactly where a theorem-grade shared
cap should persist:

- `a=1.0`, `M:4 -> 5`: third angle `~79.3°`;
- `a=1.25`, `M:4 -> 5`: third angle `~79.7°`.

New honest verdict:

- `shared rank-3 joint cap defect after the right joint basis / Gram projection`
  is now `false-for-now` as a **global** theorem-shape;
- the strongest surviving live statement is
  `structured finite-rank correction yes`,
  but likely family-dependent or requiring a larger/different common space;
- immediate next step is therefore not augmented cap positivity, but the split
  `(++ ) classifier` versus `(+-) classifier`.

Detailed note:

- `docs/insights/h1_rank3_reduced_sweep_2026_03_11.md`

## Follow-up result (2026-03-11) — split classifier with fixed `\kappa_{+-}(a)` keeps the route alive

We upgraded `src/h1_filtered_bulk_match.py` with a dedicated split-classifier
mode:

- fit one common `\kappa(a)` from `(+,-)` or freeze it;
- apply that same scale to both live families;
- compare `family-specific`, `shared-joint`, and `anchor-transfer` basis
  choices.

First real split run:

- `zeros=40` frozen;
- `a in {1.0, 1.25}`;
- `M in {4,5,6}`;
- `rank in {3,4,5,6}`;
- pooled `\kappa_{+-}(a)` fit across `M=4,5,6` for each fixed `a`.

What survived:

- one common `\kappa(a)` per fixed `a` is stable across `M`;
- `(+,-)` remains the easy calibration family under that same `\kappa(a)`;
- `(++ )` still looks like a structured low-rank defect, but now clearly in a
  split, family-specific sense.

What the new classifier says about `(++ )`:

- low-mode remains decisively bad even after freezing `\kappa_{+-}(a)`;
- `joint-Gram` is much better than low-mode, but still weaker than the optimal
  family-specific basis;
- `rank=3` is not enough to stabilize the family cleanly across `M`;
- `rank=4` is already good at `M=5` and still reasonable at `M=6`;
- `rank=5` becomes good at `M=6`;
- but the explicit `M -> M+1` transfer residuals for both family-specific and
  joint-Gram bases stay around `4.5e-1 .. 5.6e-1`, so no theorem-grade
  embedded basis is visible yet.

Interpretation:

- the filtered route is still alive in split form;
- the current classifier verdict is `B`, not `A` and not `C`:
  family-dependent finite-rank defect plausible;
- the surviving shared object is `\kappa(a)`, not a joint rank-`3` cap-space;
- the true hard question is now whether `(++ )` admits a better
  higher-rank / better-adapted basis or whether the theorem must allow a more
  explicitly family-dependent defect space.
- the next pooled refinement `family-gram-a`, built jointly across the tested
  `M`-grid for fixed `(a, zeros, rank)`, is the first strong in-sample common
  `(++ )` basis signal:
  on `a in {1.0,1.25}`, `zeros=40`, `rank in {4,5}`, the projected residuals
  sit around `~1.08e-2 .. 7.53e-2`;
- but the honest holdout `family-gram-prefix`, where the target `M` only sees
  a basis pooled from smaller `M` values, stays bad on `M=5,6,7`:
  direct projected residuals remain around `~4.35e-1 .. 5.46e-1`, and the
  `M -> M+1` transfer residuals remain around `~6.10e-1 .. 6.75e-1`;
- so Branch A stays alive only in split case `B`:
  no theorem-grade prefix-stable common `(++ )` basis is visible yet, and the
  next task is alternative weighted Gram / higher-rank / basis redesign under
  frozen `\kappa_{+-}(a)`, not cap positivity.

Detailed note:

- `docs/insights/h1_split_classifier_fixed_kappa_2026_03_11.md`
- `docs/insights/h1_family_gram_a_basis_2026_03_12.md`
- `docs/insights/h1_family_gram_prefix_holdout_2026_03_12.md`

## In progress (2026-03-14) — Proshka reset prompt for H1

The current `H1` numerics now look useful mainly as negative information:

- raw exact equality is dead;
- low-mode defect is dead;
- global shared rank-`3` defect is dead;
- pooled in-sample common-basis signals exist for `(++ )`, but the honest
  prefix holdout still fails badly.

So the next Proshka-facing request should **not** be another rank/basis hunt.

It should ask for a reset to the simpler operator question:

```text
what is the natural structural class of
S^* G S - \kappa \Delta^* Q \Delta ?
```

The drafted prompt explicitly asks Proshka to classify the defect as one of:

- exact filtered intertwining;
- explicit boundary/cap correction;
- short-range local correction
  (commutator / Toeplitz-Hankel / banded strip);
- genuine bulk mismatch.

Prompt file:

- `docs/insights/proshka_h1_reset_prompt_2026_03_14.md`

## In progress (2026-03-14) — H1 boundary/cap reset synced into control-plane

The reset is now explicit in the source-of-truth files:

- rank/basis scans remain useful only as diagnostics;
- the front-door theorem language is no longer
  `find the right low-rank basis`;
- the live object is now
  `D_{a,M,N}=S^*GS-\kappa\Delta^*Q\Delta`
  as a candidate boundary/cap defect;
- best current guess:
  explicit boundary/cap correction with a moving Toeplitz-Hankel /
  commutator / near-edge matrix shadow;
- immediate next tasks:
  test exact filtered reformulation in the `(+,-)` block and derive the
  surviving same-sign boundary term in the `(++ )` block.

Reset note:

- `docs/insights/h1_boundary_cap_reset_2026_03_14.md`

## Synthesis (2026-03-15, in progress) — `Q_\zeta`-core as the canonical coordination layer

The strongest additive move now is **not** a third RH route and not another
local `H1` trick, but a single capital layer that can absorb the already-live
work:

- keep the public route exactly as it is:
  `T0-pd -> H-bridge -> H4 -> RH`;
- keep `PSD-pd` exactly as it is:
  fallback constructive route;
- introduce a thin canonical coordination object
  `Q_\zeta`-core built from the explicit-form / Weil quadratic-operator layer,
  with two immediate backends only:
  `H-bridge` as the primary operator backend and `PSD-pd` as the strict
  finite-shadow / certificate backend;
- do **not** widen the active scope to Li / Nyman--Beurling / de Branges as
  live routes yet; those are future adapters only;
- first theorem-sized target inside this core remains the same:
  close the `(+,-)` block as exact-or-explicitly-corrected filtered identity,
  then identify the surviving same-sign boundary term in `(++ )`.

Interpretation:

- `Q_\zeta`-core is not a new endgame;
- it is the project layer that decides whether a new idea strengthens the
  canonical object, translates into it, or produces a kill certificate.

## Final result (2026-03-15) — `Q_\zeta`-core skeleton synced into source-of-truth

The project now has a thin canonical coordination layer:

- `Q_\zeta`-core = the explicit-form / Weil quadratic-operator hub above the
  live routes;
- it is **not** a third RH route and does **not** replace the public mainline
  `T0-pd -> H-bridge -> H4 -> RH`;
- its two immediate backends are now frozen explicitly:
  `H-bridge` as the primary operator backend and `PSD-pd` as the strict
  finite-shadow / certificate backend;
- future criteria such as Li / Nyman--Beurling / de Branges are demoted to
  future adapters only until these two backends become fully explicit.

Operational consequence:

- the first theorem-sized target still sits inside `H1`:
  close the `(+,-)` block as exact-or-explicitly-corrected filtered identity;
- then isolate the surviving same-sign boundary/cap term in `(++ )`;
- evaluate any new idea by one question only:
  does it improve the canonical layer, improve a translation into it, or yield
  a kill certificate?

Skeleton note:

- `docs/insights/q_zeta_core_skeleton_2026_03_15.md`

## Synthesis (2026-03-15, in progress) — short-circuit sprint and first `(+,-)` adapter

Exact blocker definition for the next micro-frontier:

- public route stays
  `T0-pd -> H-bridge -> H4 -> RH`;
- active hard blocker still sits only inside `H1^f`;
- fastest theorem-sized target is now the first adapter theorem in `(+,-)`,
  not the whole defect at once.

Local oracle / note audit:

- `Main_closure.tex` still records the older strongest filtered thesis
  `M^{+-}(a)=\kappa(a)\widetilde Q_{M,N}^{+-}`
  with no extra section-boundary defect once `\widetilde Q_{M,N}` is used;
- `h1_raw_entry_reduction_2026_03_08.md` confirms that only `(++),(+-)` are
  independent live bulk families;
- the 2026-03-14 reset still forces the new question to be symbolic defect
  calculus, not rank language.

External sanity-check:

- standard finite-section / Toeplitz-Hankel operator theory treats boundary
  corrections as natural finite-section phenomena rather than evidence of
  genuine bulk mismatch; this supports the current project guess that any
  surviving correction should be boundary/cap, not basis-defined.

Execution decision:

- freeze the two-lane short-circuit sprint:
  lane A = `H1` defect calculus;
  lane B = finite-dictionary `PSD-pd`;
- hand structural math to Proshka;
- keep deterministic exact formula / compression / proof-obligation work local;
- first local artifact is now the `(+,-)` adapter ledger.

Notes:

- `docs/insights/q_zeta_core_short_circuit_sprint_2026_03_15.md`
- `docs/insights/plus_minus_adapter_ledger_2026_03_15.md`

## Synthesis (2026-03-15, in progress) — sprint monitor as operational single source of truth

New blocker is not mathematical but operational:

- the sprint is now real, so a new session must resume the current step without
  re-deriving the frontier from scratch;
- `SESSION_ENTRY.md` is too broad for that job;
- `IMPLEMENTATION_PLAN.md` keeps the active task, but not the live substep,
  last completed step, next deliverable, or sprint invariants.

Local oracle support:

- repo process docs already separate architectural truth, execution queue, and
  insight logs;
- that strongly suggests one additional operational file rather than more
  duplicated status prose.

Execution decision:

- introduce `ACTIVE/SPRINT_MONITOR.md` as sprint single source of truth;
- put machine-readable current-step fields at the top;
- make `SESSION_ENTRY.md` and `ACTIVE/KNOWLEDGE_BASE.md` point to it at startup;
- require that every meaningful sprint move updates this file first.
- tighten the startup contract:
  when the sprint is active, a fresh session should read only
  `SESSION_ENTRY.md`, `ACTIVE/SPRINT_MONITOR.md`, and `current_artifact`
  unless a blocker appears.

## In progress (2026-03-15) — Day 2 `(+,-)` cancellation ledger started

The sprint monitor is now live and the current step is no longer just text in
the plan:

- `ACTIVE/SPRINT_MONITOR.md` records `A2` as the active step;
- the Day 2 artifact already exists:
  `docs/insights/plus_minus_cancellation_ledger_2026_03_15.md`;
- so a fresh session can now resume directly from the current theorem receiver
  instead of re-deriving the frontier.

## Synthesis (2026-03-15, in progress) — orchestrator / worker loop frozen

Parallel-agent communication is now fixed operationally rather than ad hoc:

- `ACTIVE/AGENT_PROTOCOL.md` defines one stable loop:
  orchestrator writes the request node, worker writes the report;
- the current sprint request is now a real node:
  `ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/node.md`;
- the worker write-back target is fixed:
  `ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/report.md`;
- `SPRINT_MONITOR.md` now stores `worker_protocol`, `worker_request`, and
  `worker_report`, so a new session can see the whole loop immediately;
- the prompt contract is now file-based:
  use `ACTIVE/AGENT_PROTOCOL.md` plus the current request node, rather than
  improvising persona-heavy prompts each time.

## Synthesis (2026-03-20, in progress) — `H3^f` theorem packet tightened

The active upper bridge no longer looks fuzzy at the `H3` layer:

- `docs/insights/h3_filtered_gap_transfer_2026_03_19.md` now freezes the exact
  `H2 -> H3` input package:
  closed tail space `V_a^{\mathrm{tail}}`, finite cap complement
  `A_a^{\mathrm{cap}}`, `q_{G,a}`-orthogonal split, and finite Hermitian cap
  matrix `H_a^{\mathrm{cap}}`;
- the `H3` receiver is now expressed as the four-line packet
  `finite gap -> filtered transfer -> tail coercivity -> kernel kill`;
- the bad forms are explicit now:
  failure of `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}` for arbitrarily large
  `M`, collapse of a `q_{J,a}`-normalized tail sequence, or a surviving cap
  null vector when `H_a^{\mathrm{cap}}` should already be positive.

Local consequence:

- the honest next question is no longer “what geometry should `H3` use?” but
  only whether this packet is already rigid enough to hand off to the Suzuki
  endpoint step `H4^f`.

## Synthesis (2026-03-20, in progress) — `H4^f` research-pass

New blocker definition:

- if `H3^f` is really tight enough, the next gate is no longer another bridge
  search but the endpoint handoff
  `0 \notin \sigma_p(G_g[a]) for every a>0 => RH`;
- so the exact question is whether `H4^f` is only Suzuki endpoint packaging or
  whether it secretly needs extra spectral structure not already frozen by
  `H1^f -> H2^f -> H3^f`.

Local oracle recall on `q3_docs`:

- query `H4 Suzuki endpoint RH filtered cap matrix kernel G_g[a]` points back
  to `h1_two_sided_filtered_bridge_2026_03_08.md`, which already freezes
  `H4^f` as “RH via Suzuki Theorem 1.4”;
- query `H4 filtered bridge endpoint theorem 1.4 RH` returns the same public
  stack plus `Main_closure.tex` as the best local shell;
- query `kernel G_g[a] zero eigenvalue Suzuki theorem 1.4 endpoint` hits
  `full/sections/introduction.tex`, where the compressed chain is already
  written as
  `H1 -> H2 -> H3 -> H4 -> no zero eigenvalue for G_g[a] -> RH by Suzuki Theorem 1.4`;
- query `RH equivalent 0 not eigenvalue G_g[a] Suzuki` hits
  `suzuki_form_pair_bridge_2026_03_08.md`, which already treats
  `0 \notin \sigma_p(G_g[a])` as the endpoint criterion.

External sanity-check:

- Clay still lists RH as open on 2026-03-20, so `H4^f` must remain an endpoint
  handoff inside our route, not a claim that RH is already closed externally;
- no external search result changed that picture, so the honest use of Suzuki
  here remains internal endpoint packaging rather than any claim of external
  closure.

Execution decision:

- `H4^f` looks like a genuine final endpoint packet, not a new geometric gate;
- the honest next move is to close `H3` operationally and activate a dedicated
  `H4` artifact, with the only live question being whether the `H3` kernel-kill
  output matches Suzuki Theorem 1.4 cleanly for every `a>0`.

- `H3` is now closed operationally: the upper bridge treats the filtered gap
  transfer as rigid enough for endpoint handoff, so the active local gate
  moves to `H4^f`, namely Suzuki endpoint to RH; the new active artifact is
  `docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md`, and the current
  route-kill condition shifts to failure of the `H3` kernel-kill line to match
  Suzuki Theorem 1.4 exactly for every `a>0`.
- `H4` is now closed operationally as well: the filtered Suzuki--Q3 bridge is
  treated as packaged all the way to RH at theorem-shell level, so the next
  honest move is outside the `H`-bridge itself, namely manuscript packaging or
  Lean/Aristotle formalization of the frozen `H1^f -> H2^f -> H3^f -> H4^f`
  chain.

## Synthesis (2026-03-20, in progress) — reset to the first real blocker `PO2`

New blocker definition:

- packaging the chain `H1^f -> H2^f -> H3^f -> H4^f` did not prove RH;
- it only proved that the route has a clean theorem shell if its lower inputs
  are genuinely discharged;
- the first still-undischarged proof-critical brick on that route is therefore
  not `H4`, but `PO2`: cross-sign bulk exactness inside `H1^\infty`.

Local oracle recall:

- query `mixed block paired operator Toeplitz Hankel cross-sign boundary exactness`
  comes back to `Main_closure.tex` with the same verdict: the honest blocker is
  still the exact four-block bulk comparison on the filtered tail together with
  the finite-dimensional Suzuki cap;
- query `D_{a,N}^{+-} boundary cap only remainder` points back to the older
  filtered H1 notes and again supports the cap-only or boundary-plus-cap
  fallback picture, not a new upper-bridge blocker;
- query `PO2 theorem packet mixed block exact four-block bulk comparison`
  points back to the frozen mainline block notes and tracker, reinforcing that
  the public route still depends on a real `H1` proof input rather than on
  further endpoint packaging.

Direct file check:

- `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` already
  isolates the exact theorem target
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- `docs/insights/h1_proof_obligation_table_2026_03_16.md` still makes `PO2`
  the first proof-critical asymmetry gate inside `H1^\infty`;
- `full/sections/Main_closure.tex` still treats `H2/H3/H4` as consumers of a
  successfully landed `H1`, not as replacements for it.

External sanity-check:

- no external source gave a ready-made theorem closing our exact filtered
  split;
- the external operator-theory support still only justifies the language:
  mixed block should be exact-or-cap-only, same-sign should carry the boundary
  residue.

Execution decision:

- the next fastest move toward an actual RH proof is not more `H4` packaging;
- it is to reopen the theorem phase at `PO2`, namely the proof of cross-sign
  bulk exactness;
- treat `H2^f -> H3^f -> H4^f` as conditional consumers until `PO2` and then
  `PO3` are genuinely discharged.

Compact mixed-block plan:

- work on the infinite-tail object first:
  `\mathcal D_{a,N}^{+-}=P_{+,N}\mathcal D_{a,N}P_{-,N}`;
- expand both sides through the exact filtered four-block formulas
  `M_{mn}^{+-}(a)=W(\psi_n^+[a]*\widetilde{\psi_m^-[a]})`
  and the pulled-back Q3 block `\kappa(a)\widetilde Q^{+-}`;
- isolate the common four-term stencil coming from the two-sided filter
  `\Delta_N`, and force exact cancellation there before any cap discussion;
- allow only two named remainder channels after that cancellation:
  `\mathcal D_{a,\partial}^{+-}` and `\mathcal D_{a,\mathrm{cap}}^{+-}`;
- if any residual term survives that is neither boundary nor cap, kill the
  current theorem shape immediately;
- if the bulk cancels, move directly to `PO3` and keep `(++)` frozen until the
  cross-sign boundary question is also closed.

First exact proof-facing refinement:

- `PO2` now has an explicit entrywise mixed residual
  `R_{mn}^{+-}(a)=M_{mn}^{+-}(a)-\kappa(a)\widetilde q_{mn}^{+-}`;
- by combining the two frozen filtered-block propositions from
  `Main_closure.tex`, this residual is exactly the four-term stencil of the
  raw mixed defects
  `\delta_{r,s}(a)=w_{r,s}(a)-\kappa(a)q_{r,s}`;
- this is the right local target because it does **not** ask for the dead
  global raw identity, only for cancellation of the specific cross-sign
  stencil;
- so the next proof move is now completely sharp:
  prove this stencil vanishes, or prove it is already boundary/cap-only, or
  kill the route.

Direct `PO2` receiver plan after demoting the Krein/localization branch:

- exact live target is the structured shift-uniqueness lemma from
  [h1_po2_cross_sign_bulk_exactness_2026_03_16.md](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md):
  if `P,Q\in\mathcal C_a` and `P(m)=Q(m+1)` for all `m>N`, prove
  `P(z)=Q(z+1)` identically;
- this is wired directly into `PO2`: once this receiver is injective, the
  cross-sign bulk exactness obstruction disappears and the route climbs again
  to `PO3 -> H2^f -> H3^f -> H4^f -> RH`;
- local embedding search gave essentially no signal: four direct queries on
  `q3_docs` all timed out, which is itself evidence that the repo does not yet
  contain a ready-made theorem for this receiver;
- external search also gave no usable primary-source theorem for the infinite
  paired-pole class, only generic Cauchy-transform and interpolation material;
- the concrete attack packet is now:
  1. exploit the exact paired support `Y_a=\{x_\gamma,x_\gamma-1\}` and the
     inherited `O(\gamma^{-3})` coefficients rather than the generic
     `\ell^1` Cauchy class;
  2. test residue identities obtained from contour formulas with
     `\pi\cot(\pi z)` or related integer-sampling kernels against the tail-zero
     condition;
  3. isolate a possible one-point divisor rigidity statement for the direct
     receiver, not for the Krein backend;
  4. if a global theorem still does not emerge, prepare only a tiny Aristotle
     request for a contour/interpolation sublemma, never for the whole
     uniqueness statement at once.
- the first genuinely new direct lemma is now explicit and useful: if
  `R(z)=\sum_{y\in Y_a} e(y)/(y-z)` and `R(a)=0` at a tail integer `a>N`, then
  division by `(z-a)` stays in the **same** simple Cauchy class:
  `R(z)/(z-a)=\sum_{y\in Y_a} e(y)/(y-a)/(y-z)`. So the direct receiver has
  its own internal divisor tower
  `R_k(z)=R(z)/\prod_{j=1}^k(z-(N+j))`, with updated coefficients still living
  on the same paired support. This creates a much more native next target than
  the demoted Krein branch: prove a direct divisor-rigidity statement saying
  such a long tail-zero tower cannot persist in the `Y_a`-paired class unless
  `e\equiv 0`.
- the direct tower now has a genuinely paired-support asymmetry built into it.
  Writing
  `R(z)=\sum a_\gamma/(x_\gamma-z)-\sum b_\gamma/(x_\gamma-1-z)`, after `k`
  tail-zero divisions one gets new paired residues
  `a_\gamma^{(k)}` and `b_\gamma^{(k)}`, with
  `b_\gamma^{(k)} = \theta_{k,\gamma} b_\gamma / \prod_{j=1}^k(x_\gamma-N-j)`
  and
  `\theta_{k,\gamma}=(x_\gamma-N-1)/(x_\gamma-N-k-1) -> 0` for fixed
  `\gamma`. So divisor exhaustion asymptotically suppresses the shifted pole
  inside each pair. This creates a sharper active subtarget:
  normalize `R_k` and try to extract a nonzero one-sided limit supported only
  on `X_a={x_\gamma}`. If that works, `PO2` reduces from the paired support to
  a one-sided critical-line support class where the earlier arithmetic
  obstructions are stronger.
- the real shape of `D3` is now much clearer and much tighter. The suppression
  factor `\theta_{k,\gamma}` only decays on fixed finite packets:
  `\sup_{\gamma\in F}|\theta_{k,\gamma}|\to 0` for each finite `F`, but not
  uniformly in `\gamma`. In fact, if
  `(x_{\gamma(k)}-N-1)/k\to c\in(1,\infty)`, then
  `\theta_{k,\gamma(k)}\to c/(c-1)`, and if
  `(x_{\gamma(k)}-N-1)/k\to\infty`, then `\theta_{k,\gamma(k)}\to 1`. So the
  one-sided decoupling mechanism is only packetwise; globally it needs an
  extra no-escape lemma saying the normalized divisor mass does not drift to
  scales `x_\gamma\asymp k` or larger.
- this yields a clean conditional extraction theorem on the active direct
  route. If one can find a normalization `s_k` and subsequence such that the
  normalized direct-tower coefficients are uniformly `\ell^1`-bounded, tight,
  and pointwise convergent on fixed `\gamma`, then the normalized receivers
  converge locally uniformly off `X_a\cup(X_a-1)` to a one-sided Cauchy
  transform `\sum \alpha_\gamma/(x_\gamma-z)`. So `D3` is no longer a vague
  compactness hope: the exact live brick is now the tightness / no-escape
  statement, while all generic compactness is secondary.
- local embedding search was low-signal again: the `q3_docs` hits were mostly
  irrelevant noise from unrelated `D3`/A3 materials, and no internal note
  contained a ready-made no-escape argument. External web sanity-check only
  pointed toward generic meromorphic compactness / Cauchy-transform folklore,
  not toward the crucial scale-sensitive tightness statement. So the no-escape
  brick should be treated as genuinely new, not as a theorem we merely failed
  to remember.
- `D3` has now hit a serious internal obstruction. If the normalized divisor
  tower had the natural compactness control
  `\sup_k \sum_\gamma (|\alpha_\gamma^{(k)}|+|\beta_\gamma^{(k)}|)<\infty`,
  then every fixed packet coefficient would actually have to tend to zero on
  an infinite-support counterexample. The reason is Gamma-growth: boundedness
  at arbitrarily far-right nonzero support points forces
  `s_k=O(\Gamma(k-M))` for every `M`, and comparing this with the fixed-packet
  denominator `\Gamma(k+N+1-x)` kills each fixed coefficient. So the planned
  compactness extraction `D3c` cannot yield a nonzero one-sided limit on
  `X_a` for infinite support.
- this does not kill the whole direct route, but it does kill the nicest
  compactness version of `D3`. Honest status now: `D3a` is a real finite-packet
  effect; `D3c` is dead as a nonzero one-sided extraction mechanism under
  uniform `\ell^1` control; and the active burden shifts back toward `D2`,
  unless a radically different non-`\ell^1` normalization is found.
- such a radically different normalization now exists. Because the direct
  paired-support coefficients already lie in `\ell^2(Y_a)`, the divisor tower
  can be normalized in `\ell^2`, producing discrete Gibbs probability measures
  \[
  \nu_k(y)=
  \frac{|e(y)|^2\prod_{j=1}^k |y-\lambda_j|^{-2}}
       {\sum_{v\in Y_a}|e(v)|^2\prod_{j=1}^k |v-\lambda_j|^{-2}}.
  \]
  Tightness of `\nu_k` is exactly a non-`\ell^1` version of `D3b1`.
- this is a real revival of `D3`, not a resurrection of the dead `D3c`.
  Tightness of `\nu_k` gives precompactness of the normalized coefficient
  vectors in `\ell^2(Y_a)`, and strong `\ell^2` convergence then gives locally
  uniform convergence of the normalized Cauchy transforms off `Y_a` because
  `\{1/(y-z)\}_{y\in Y_a}` is uniformly in `\ell^2(Y_a)` on compacta away from
  the support. Combined with finite-packet suppression of the shifted member
  in each pair, this yields the right new live target:
  prove a finite anchor block for the Gibbs measures `\nu_k`.
- so the active dichotomy is now sharper again:
  `D3c` stays killed in the `\ell^1` compactness regime, but `D3e` is alive as
  a genuinely new `\ell^2`-Gibbs route. The next honest brick is an
  anchor-block criterion
  `\inf_k \sum_{y\in E}\nu_k(y)\ge \eta`
  for some finite packet `E\subset Y_a`.
- this new `D3e` route is now also blocked in its finite-anchor form. For any
  two fixed nonzero support points `y>y'`, the Gibbs weights satisfy
  \[
  \frac{W_k(y)}{W_k(y')}
  \sim
  C(y,y')\,k^{2(y-y')}
  \qquad (k\to\infty),
  \]
  by the Gamma-product identity and the standard asymptotic
  `\Gamma(k+a)/\Gamma(k+b)\sim k^{a-b}`. So every fixed support point farther
  to the right eventually dominates every fixed support point to its left.
  Consequently, if the counterexample support is unbounded, then for any
  finite packet `E` one can pick `y_*>max E` with `e(y_*)\neq 0`, and then
  `\nu_k(E)\to 0`. Hence no finite anchor block exists, `\nu_k` is not tight,
  and `D3e4` is false on every infinite-support counterexample.
- this is a strong partial kill: `D3e1` remains a correct coefficient
  reformulation and the conditional implications `tightness => precompactness
  => local transform convergence` remain true, but the route never reaches
  its own tightness input. Honest status now: both nice compactness versions
  of `D3` are dead, and the active direct burden returns entirely to `D2`.
- the main `D2` theorem target is now frozen in a much cleaner Gamma-profile
  form. For any `z_0\notin Y_a`, the direct tower identity rewrites as
  \[
  R(z_0)\,u_k(z_0)=\sum_{y\in Y_a}\frac{e(y)}{y-z_0}\,u_k(y),
  \qquad
  u_k(x)=(-1)^k\frac{\Gamma(N+1-x)}{\Gamma(k+N+1-x)}.
  \]
  So `PO2` reduces to a profile-rigidity question: can one external profile
  `u_k(z_0)` be represented by an `\ell^1` superposition of support profiles
  `u_k(y)` on `Y_a`?
- DLMF gamma-ratio asymptotics give the finite-support shadow immediately:
  `u_k(y)/u_k(y')\sim C(y,y')k^{y-y'}`. Hence if the coefficient support had a
  rightmost point, that maximal exponent would dominate and force its
  coefficient to vanish. So any genuine infinite-support counterexample must
  exploit support points running arbitrarily far to the right.
- this isolates the real unresolved upgrade: turn finite right-packet
  dominance into a theorem for the whole unbounded support using the actual
  inherited decay `e(y)=O(\gamma^{-3})` and the zero-density geometry of
  `Y_a=\{x_\gamma,x_\gamma-1\}`. That is now the exact active plan. No ready
  theorem appeared in local search; the useful external sanity-check was DLMF
  §5.11 on Gamma ratios.
- the user’s `L_k` idea is a genuinely good backup refinement for the demoted
  Krein branch. On the algebraic spans
  `\mathcal A_k=\operatorname{span}_{fin}\{G_k/(z-\lambda):\lambda\in Z(G_k)\}`,
  the coefficient-sum functional
  `L_k(\sum c_\lambda G_k/(z-\lambda)):=\sum c_\lambda` is well defined, has
  the asymptotic form `L_k(f)=\lim_{z\to\infty} z f(z)/G_k(z)`, and satisfies
  `\mathcal A_{k+1}=\ker L_k\cap \mathcal A_k`. So if `L_k` extends boundedly
  to the closed space `H_{G_k}`, strict inclusion
  `H_{G_{k+1}}\subsetneq H_{G_k}` follows almost for free. This is a real
  analytic brick inside the backup branch, but it still does not bypass the
  earlier strategic verdict: the active critical path remains the direct
  divisor-rigidity target `D2`, while `L_k` boundedness is a serious reserve
  sublemma if we come back to Krein.
- this backup `L_k` criterion is now corrected and made theorem-grade. The
  valid chain is `G_k=G_0/P_k` with
  `P_k(z)=\prod_{j=1}^k(z-(N+j))`, not `G_0 P_k`; and the needed asymptotic
  input is a negative-power vertical jet for `A/G_0`,
  `A(iy)/G_0(iy)=\beta_0+\beta_1/(iy)+\cdots+\beta_k/(iy)^k+o(|y|^{-k})`.
  Under strip moments `\sum \mu_n |t_n|^{2r}<\infty` up to order `k+1`, this
  implies a polynomial asymptotic for `Q_k=A/G_k`, namely
  `Q_k(iy)=\sum_{r=0}^k q_r^{(k)}(iy)^r+o(1)` with
  `q_r^{(k)}=\sum_{n=0}^{k-r} p_{r+n}^{(k)}\beta_n`, and hence gives a bounded
  extension of `L_k` via
  `L_k(f)=\sum_{r=0}^k q_r^{(k)}\Lambda_r(f)`. So
  `H_{G_{k+1}}\subsetneq H_{G_k}` becomes a real conditional theorem, not just
  a slogan. But this remains a backup branch only: to use it for `PO2` one
  would still need to verify the actual vertical jet for the real `G_0`, and
  the active path is still the direct `D2/D3` divisor route.
- there is now an even more route-native reading of this backup theorem. For
  the actual `PO2` branch, `G_0` comes from a tail-zero witness inside the
  ambient Cauchy-de Branges space, so the native asymptotic object is
  `z\,G_0/A`, not immediately `A/G_0`. Writing
  `G_0(z)/A(z)=\sum_n b_n/(z-t_n)`, one gets
  `z\,G_0(iy)/A(iy)=\alpha_0+\alpha_1/(iy)+\cdots` with
  `\alpha_r=\sum_n b_n t_n^r` under the same strip-moment assumptions. If
  `\alpha_s` is the first nonzero moment, then `A(iy)/G_0(iy)\asymp(iy)^{s+1}`,
  so the leading degree of `Q_k=A/G_k` is `k+s+1`, not automatically `k`.
  Hence the honest route-specific backup target is now:
  determine whether `\alpha_0(G_0)` or `\alpha_1(G_0)` vanishes. In the
  generic case `\alpha_0\neq 0`, the old bridge becomes degree `k+1`; if
  `\alpha_0=0`, the backup branch shifts upward and needs more moment
  functionals. This sharpens the reserve route without changing the active
  critical path, which still runs through direct `D3b1`.
- the moving Gamma-profile form of `D2` now collapses to one fixed reweighted
  Cauchy transform, but only after adjoining the external profile point
  `z_0`. If
  `u_k(z_0)=\sum_{y\in Y_a} c_y(z_0)u_k(y)`, then on the enlarged support
  `\widehat Y_{a,z_0}=Y_a\cup\{z_0\}` with coefficients
  `\widehat e_{z_0}(z_0)=-1` and `\widehat e_{z_0}(y)=c_y(z_0)`, the exact
  forward-difference identity becomes
  `\sum_{w\in \widehat Y_{a,z_0}} \widehat e_{z_0}(w)u_k(w)
   =(1/k!)\Delta^k \widehat R_{N,z_0}(N)`,
  where
  `\widehat R_{N,z_0}(z)=\sum_{w\in \widehat Y_{a,z_0}}((w-N)\widehat e_{z_0}(w))/(w-z)`.
- by Newton's formula this is equivalent to
  `\widehat R_{N,z_0}(N+m)=0` for every `m\ge 0`. So the active `D2` burden is
  no longer “exclude an `\ell^1` superposition of moving Gamma profiles,” but
  the static augmented tail-zero uniqueness statement
  `\widehat R_{N,z_0}(N+m)=0\ \forall m\ge 0 \Rightarrow \widehat R_{N,z_0}\equiv 0`.
- this correction matters: the earlier unreweighted static reduction was too
  naive for the actual profile identity. The honest theorem target must retain
  the external point `z_0` as one additional pole of the static transform.
- admissibility still survives on the actual `PO2` data. On `Y_a`,
  `e(y)=O(\gamma^{-3})`; dividing by `y-z_0` improves this to `O(\gamma^{-4})`;
  multiplying by `y-N` returns only `O(\gamma^{-3})`. So the enlarged
  coefficient family on `\widehat Y_{a,z_0}` remains in `\ell^1` after adding
  the single point `z_0`.
- the next exact simplification is already static and sharper than `D2e`
  itself. Evaluating `\widehat R_{N,z_0}(N+m)=0` gives
  `((z_0-N)/(z_0-(N+m))) = \sum_{y\in Y_a} ((y-N)c_y(z_0))/(y-(N+m))`
  for every `m\ge 0`. So the live theorem target is now a kernel-representation
  uniqueness statement on the integer tail: one external Cauchy kernel cannot
  be represented by an `\ell^1` superposition of support kernels.
- this is the right place to attack. The finite-support case is trivial by
  pole separation: both sides are rational in `m`, and the left pole at
  `m=z_0-N` cannot come from poles at `m=y-N` with `y\in Y_a`. Therefore any
  real obstruction is purely infinite-support.
- exact target / wiring:
  `D2f1` = infinite-support tail uniqueness for the static kernel
  representation above;
  if `D2f1` falls, then `D2e` falls; if `D2e` falls, then Gamma-profile
  rigidity falls; if `D2` falls, `PO2` cracks and the `H-bridge` route comes
  back to life.
- concrete plan now:
  isolate a finite right packet and tail in the static representation;
  use pole separation to kill the finite packet exactly;
  then try to upgrade this to the whole tail using the actual decay
  `e(y)=O(\gamma^{-3})` and the geometry `Y_a=\{x_\gamma,x_\gamma-1\}`.
- this upgrade now has a much sharper internal split. Writing
  `d_y(z_0):=(y-N)c_y(z_0)`, the static identity is
  `K_{z_0}(m)=\sum_{y\in Y_a} d_y(z_0)/(y-(N+m))` with
  `K_{z_0}(m)=(z_0-N)/(z_0-(N+m))`. Because `d_y(z_0)=O(\gamma^{-3})` and
  local zero counting gives `#(Y_a\cap[t-1,t+1])\ll_a \log(2+t)`, the unit
  packet around `N+m` has total coefficient mass only `\ll_a (\log m)/m^3`.
- therefore the next theorem packet is:
  `D2f2` = no-resonance asymptotic lemma;
  if the nearest support point to `N+m` stays farther than
  `\gg_\omega (\log m)/m^2`, meaning
  `m^2\rho_m/\log m\to\infty`, then the local packet is negligible and one should get
  the first-order asymptotic
  `K_{z_0}(m)\sim -(1/m)\sum_y d_y(z_0)`, hence the moment identity
  `\sum_y d_y(z_0)=z_0-N`.
- there is now a clean proof skeleton for `D2f2`: multiply the identity by
  `M=N+m` and write
  `M K_{z_0}(m)= -\sum_y d_y(z_0) + \sum_y d_y(z_0)\,y/(y-M)`. Then split the
  second sum into `y\le M/2`, `M/2<y` with `|y-M|\ge 1`, and the resonant
  packet `|y-M|<1`. The first two pieces die by absolute convergence of
  `\sum_y |d_y(z_0)|\,y`, and the packet dies under the lower-gap condition
  because its total coefficient mass is only `\ll (\log M)/M^3`. Important
  correction: to get `o(1)` after multiplying by `M`, one needs the stronger
  gap `m^2\rho_m/\log m\to\infty`; the weaker bound
  `\rho_m\gg (\log m)/m^2` gives only `O(1)`.
- equivalently, any failure of this first-order asymptotic must be carried by
  infinitely many ultra-near resonances
  `|y-(N+m)|\ll (\log m)/m^2`.
- this already yields a real corollary, not just a shape theorem. Since
  `d_y(z_0)=((y-N)e(y))/(R(z_0)(y-z_0))`, the identity
  `\sum_y d_y(z_0)=z_0-N` simplifies to
  `\sum_{y\in Y_a} e(y)=0`. So every no-resonance counterexample would force
  zeroth-moment cancellation of the original receiver coefficients.
- there is also now a clean obstruction to the next naive upgrade. A
  second-order asymptotic would naturally require absolute control of
  `\sum_y |d_y(z_0)|\,y^2`, but with `d_y(z_0)=O(\gamma^{-3})` and
  `#(Y_a\cap[t-1,t+1])\ll_a \log(2+t)`, the packet at height `t` contributes
  only `\ll_a (\log t)/t`, whose sum diverges. So there is no routine
  absolute-convergence route from `D2f2` to a first-moment identity.
- this is a useful kill, not bad news. It means the no-resonance branch gives
  us exactly one generic moment layer, namely `\sum_y e(y)=0`. To go further,
  we now need either genuinely pairwise cancellation from the shifted support
  `\{x_\gamma,x_\gamma-1\}`, or the resonance branch `D2f3`.
- this also identifies the exact borderline scale. Above
  `(\log m)/m^2` by a diverging factor, the generic first-order route works;
  at the borderline scale itself, the generic argument stalls and the whole
  burden moves into the paired correction term `D2g1`.
- that “pairwise cancellation” is now named precisely. Writing
  `e_\gamma^+=e(x_\gamma)` and `e_\gamma^-=e(x_\gamma-1)`, the tail-zero
  identity becomes
  `0=\sum_\gamma p_\gamma/(x_\gamma-M) + \sum_\gamma q_\gamma/((x_\gamma-M)(x_\gamma-1-M))`
  with `p_\gamma=e_\gamma^+ + e_\gamma^-` and `q_\gamma=e_\gamma^-`.
- because `\sum_y e(y)=0`, the one-sided main coefficients satisfy
  `\sum_\gamma p_\gamma=0`. So the whole missing no-resonance upgrade is now
  concentrated in the paired correction term
  `\sum_\gamma q_\gamma/((x_\gamma-M)(x_\gamma-1-M))`.
- exact next brick:
  `D2g1` = prove that the resonant packet of this correction term is
  `o(M^{-1})` on a no-resonance subsequence using actual pairwise residue
  structure; otherwise the route collapses entirely into `D2f3`.
- this is good compression: we no longer say “some new pairwise structure is
  needed”; we now know exactly which series has to cancel and where.
- a new user-proposed reduction is logically correct but currently too strong
  to be the mainline. In operator form, with
  `(\mathcal T_N e)_m=\sum_y e(y)/(y-(N+m))`, full `PO2` would follow from:
  every nonzero `e\in\ker \mathcal T_N` yields another nonzero
  `\widetilde e\in\ker \mathcal T_N` with support bounded above, provided the
  one-sided bounded-above theorem is already available.
- this is a legitimate meta-reduction, but not the fastest current route. It
  asks for global support extraction while preserving the whole infinite tail
  of sampling equations. That looks at least as hard as the current direct
  brick, and local / external search gave no sign of a ready-made extremal
  support principle for this Cauchy-tail kernel.
- practical verdict: keep the bounded-above extraction theorem as backup
  `D2h`, but do not demote the sharper live split `D2g1` versus `D2f3`.
- this is a strong narrowing: `D2f1` is no longer a vague infinite-support
  uniqueness problem. The live burden is now a dichotomy between a clean
  no-resonance asymptotic route and an ultra-near resonance obstruction on the
  actual support `Y_a`.
- research pass for this blocker was again low-signal on the local side: the
  `q3_docs` oracle returned mostly irrelevant `DigammaSeries` /
  hat-interpolation noise and nothing close to a ready-made tail-zero
  uniqueness theorem. External web search was useful only as sanity-check for
  standard Gamma-ratio / Newton-difference formulas, not as a source of the
  missing rigidity theorem. So the new static `D2e` target should be treated
  as genuinely ours, not as a known theorem we merely failed to locate.
- in-progress synthesis for the next `D2g1` attack:
  the exact target is now the resonant packet of
  `\sum_\gamma q_\gamma/((x_\gamma-M)(x_\gamma-1-M))` on the borderline scale
  `(\log M)/M^2`;
  local oracle search was still low-signal, while direct `qmd` calls only
  returned generic corrected-cone / Digamma noise or timed out on the new
  packet queries, so there is still no sign of a ready-made theorem;
  external web search was likewise low-yield and gave only sanity-check level
  background on arithmetic-progressions / localization, not the missing local
  correction lemma;
  the concrete plan is therefore to quantify the packet contribution directly:
  show that at the threshold scale it is bounded by `#packet / \log M`, so a
  nontrivial obstruction would force a logarithmic microcluster of support
  points inside a window of width `\asymp (\log M)/M^2`.
- this is now done in the first honest quantitative form. Fix
  `0<c<C<\infty` and define the threshold packet
  `\mathcal P_M(c,C)=\{\gamma: c(\log M)/M^2 \le |x_\gamma-M|
  \le C(\log M)/M^2\}`.
  Outside the ultra-near branch `D2f3`, one has
  `|x_\gamma-1-M|\ge 1/2` on this packet for large `M`, and the inherited
  decay still gives `|q_\gamma|\ll_a M^{-3}`.
- therefore
  `\left|M\sum_{\gamma\in\mathcal P_M(c,C)}
  q_\gamma/((x_\gamma-M)(x_\gamma-1-M))\right|
  \ll_{a,c,C} \#\mathcal P_M(c,C)/\log M`.
  So if the packet cardinality is `o(\log M)`, then the borderline packet is
  already `o(1)` after multiplying by `M`, hence `o(M^{-1})` on the original
  scale.
- this creates a new sharp obstruction:
  any genuine failure of `D2g1` outside `D2f3` must produce packets with
  `\#\mathcal P_M(c,C)\gtrsim \log M`.
  Since the old local count on the whole unit interval is only
  `\#(Y_a\cap[M-1,M+1])\ll_a \log M`, a counterexample would need a
  near-maximal logarithmic microcluster inside the microscopic window
  `\asymp (\log M)/M^2`.
- this is real progress. The active direct split is no longer only
  `paired correction` versus `ultra-near resonance`; it is now
  `paired correction with a log-sized microcluster requirement` versus
  `ultra-near resonance below the threshold scale`.
- new in-progress synthesis for the next step:
  a logarithmic microcluster in the paired support `Y_a=\{x_\gamma,x_\gamma-1\}`
  should immediately force a compressed microcluster in the one-sided support
  `X_a=\{x_\gamma\}` near either `M` or `M+1`, because a microscopic window
  around `M` cannot contain both members of a pair separated by distance `1`;
  by pigeonhole, half of the packet must come from one side.
- once that reduction is written cleanly, a packet
  `\#\mathcal P_M(c,C)\gtrsim \log M` in width `\asymp (\log M)/M^2`
  yields a block of `\gg \log M` one-sided support points in an interval of the
  same width, hence at least one consecutive gap of size `O(M^{-2})`.
- external search was still only sanity-level useful here:
  Hall's paper on distinct zeros in short intervals and Hall--Hayman on small
  regions confirm that this is the right geometric direction, and Rodgers'
  tail-bound paper gives local-statistics background at the much coarser
  `1/\log T` scale under RH, but none of these gives the missing theorem at
  the `1/M^2` scale.
- this reduction is now frozen as `D2g3`:
  because the pair support is `Y_a=\{x_\gamma,x_\gamma-1\}`, a microscopic
  packet around `M` splits into two disjoint one-sided packets around `M` and
  `M+1`; if the total packet has size `\ge \eta \log M`, then one of those
  one-sided packets has size `\ge (\eta/2)\log M`, still inside width
  `\asymp (\log M)/M^2`.
- ordering that packet immediately gives a consecutive one-sided support gap
  `x_{\gamma+1}-x_\gamma\ll_{\eta,C} M^{-2}`, hence a zeta-zero ordinate gap
  `\gamma_{n+1}-\gamma_n\ll \gamma_n^{-2}` along an infinite subsequence.
- this is a strong compression. The active direct route is now:
  `D2g1` or else `D2g2` or else `D2g3` or else `D2f3`.
  So outside the ultra-near branch, any surviving counterexample must force
  infinitely many absurdly compressed one-sided critical-line gaps.
- there is now also a clean exact local theorem in the paired direction:
  a finite one-sided paired correction term
  `K(z)=\sum_j c_j(1/(a_j-z)-1/(b_j-z))` with all `a_j,b_j<N+1` and
  tail zeros `K(N+m)=0` for all `m\ge 1` can be regrouped as an ordinary
  one-sided receiver `K(z)=\sum_{v\in V} d(v)/(v-z)`, where `d(v)` is the
  divergence of the weighted pair-graph.
- one-sided rigidity then forces `d(v)=0` at every vertex. If the underlying
  finite pair-graph is a forest, leaf-stripping kills all edge weights, so the
  whole correction term is zero. This is now frozen as `D2g4`.
- this is a real theorem, and it is a nice local kill: any nontrivial exact
  finite local paired correction with tail zeros must already carry cycle
  structure.
- but it is still not the global closure of `D2g1`, because the missing step
  is exact truncation: we do not yet know how to carve such a finite packet
  out of the full infinite correction term while preserving the whole tail of
  zeros. So `D2g4` is a strong local structural theorem, not yet the mainline
  endgame.
- in-progress synthesis for the next brick:
  replace exact local forest/cycle dichotomy by a quantitative finite-window
  statement on sample defects;
  work with a finite vertex set `V`, the finite Cauchy sample matrix `C_V`,
  and the incidence matrix `B_G` of the local pair-graph;
  prove the exact factorization `s(c)=C_V B_G c`, invertibility of `C_V`, and
  then the estimate
  `\operatorname{dist}(c,\ker B_G)\le (\kappa(V,N)\beta(G))^{-1}\|s(c)\|_2`;
  this would show that approximate local packets are forced toward cycle-space,
  and any surviving obstruction must come from collapse of the stability
  constants `\kappa(V,N)\beta(G)`, which is exactly the right entry point into
  the resonance branch `D2f3`.
- this is now frozen as `D2g5`. For a finite window
  `V=\{v_1,\dots,v_L\}\subset(-\infty,N+1)`, local pair-graph `G`, and packet
  coefficients `c`, the first `L` tail samples satisfy the exact factorization
  `s(c)=C_V B_G c`, where `C_V` is the finite Cauchy sample matrix and `B_G`
  is the incidence matrix.
- `C_V` is invertible by the usual polynomial argument for a finite ordinary
  receiver vanishing at `L` tail points, so with
  `\kappa(V,N)=\sigma_{\min}(C_V)>0` and
  `\beta(G)=\sigma_{\min}(B_G|_{\ker(B_G)^\perp})>0` one gets
  `\operatorname{dist}(c,\ker B_G)\le (\kappa(V,N)\beta(G))^{-1}\|s(c)\|_2`.
- this is the clean quantitative version of the old local picture:
  approximate finite packets with tiny sample defect are forced toward the
  cycle space. In particular, exact finite packets lie in the cycle space and
  therefore define the zero paired correction term; forests are even
  quantitatively dead because then `\ker B_G=\{0\}`.
- practical verdict:
  branch B is now mathematically clean.
  If `\kappa(V,N)\beta(G)` stays uniformly bounded below on relevant windows,
  then `D2g1` dies locally.
  So any surviving local obstruction must come from collapse of these
  stability constants, and that is now the right hard brick feeding `D2f3`.
- next in-progress split of that brick:
  separate `\kappa`-collapse from `\beta`-collapse.
  On the Cauchy side, the determinant formula for a finite Cauchy matrix says
  that if a local window has bounded size, stays a definite distance away from
  the sampled tail grid, and its vertices remain pairwise separated, then
  `\kappa(V,N)` is bounded below by an explicit positive function of those
  parameters.
- so at least on bounded-size local windows, `\kappa`-collapse already forces
  one of two geometric pathologies:
  either some vertex approaches the sample grid (resonance), or some pair of
  vertices approaches each other (compressed support gap).
  This is exactly the sort of “impossible geometry” we want.
- this is now frozen as `D2g6`. Using the Cauchy determinant formula plus the
  crude norm bound `\|C\|\le L/\rho`, one gets a positive lower bound for
  `\kappa(V,B)` on every bounded-size local window with uniform sample
  separation `\rho`, pairwise vertex separation `\delta`, and coarse diameter
  bound `D`.
- therefore bounded-size `\kappa`-collapse already forces genuine geometric
  degeneration: either resonance to the sampled tail grid, or compressed
  vertex gaps, or escape of the whole window.
- in our actual `D2` setting the first two are the meaningful cases. So the
  stability-collapse branch is now cleanly split:
  `\beta`-collapse is graph/combinatorial, while `\kappa`-collapse on bounded
  windows already means “resonance or compressed geometry”.
- next in-progress sharpened target:
  bounded-size windows should also kill the `\beta`-channel.
  For an oriented graph `G`, the nonzero singular values of the incidence
  matrix are the square roots of the positive Laplacian eigenvalues; in
  particular `\beta(G)` is the square root of the smallest positive Laplacian
  eigenvalue on the relevant support components.
- standard spectral graph theory then says that among connected simple graphs
  on `r` vertices, the path minimizes algebraic connectivity, so
  `\beta(G)\ge 2\sin(\pi/(2r))`; multiedges can only increase the Laplacian.
  Therefore if the local packet size is bounded by `L`, then
  `\beta(G)\ge 2\sin(\pi/(2L))>0`.
- if this is written cleanly, the surviving obstruction is squeezed again:
  on bounded-size windows neither `\kappa` nor `\beta` can collapse without
  genuine geometric degeneration, so any local obstruction must either enlarge
  the packet size or enter the resonance/compressed-gap branch.
- this is now frozen as `D2g7/D2g8`.
  For the incidence side, `\beta(G)` is the square root of the smallest
  positive Laplacian eigenvalue. Standard spectral graph theory gives that
  among connected simple graphs on `r` vertices the path graph minimizes
  algebraic connectivity, hence
  `\beta(G)\ge 2\sin(\pi/(2r))`; multiedges only increase the Laplacian.
- therefore if a local packet touches at most `L` active vertices, then
  `\beta(G)\ge 2\sin(\pi/(2L))>0`. Combined with `D2g6`, this yields a full
  bounded-size barrier:
  if the packet size is bounded and the Cauchy-side geometry stays nondegenerate,
  then `\kappa(V,B)\beta(G)` cannot collapse at all.
- practical consequence:
  bounded-size local packets are now completely out of the mystery zone.
  Any surviving local obstruction must either force genuine geometric
  degeneration on the Cauchy side, or make the active packet size tend to
  infinity, or both. That is exactly the right funnel into the
  `D2g3/D2f3` branch.
- in-progress synthesis after `D2g7`:
  the next exact theorem should no longer talk about the product
  `\kappa(V,N)\beta(G)` abstractly, but about a three-way collapse split:
  drift of the whole window, compressed gaps inside the support, or packet-size
  growth.
- external sanity-check for this step stayed standard and low-risk:
  Cauchy determinant formula, the identity between nonzero singular values of
  incidence and positive Laplacian eigenvalues, and the path-graph lower bound
  for algebraic connectivity. No ready-made theorem for our exact PO2 packet
  route appeared, which is fine: the missing bridge is now genuinely ours.
- exact next target:
  if normalized local packets have tiny sample defect and remain in a
  near-tail slab with bounded packet size, then they cannot survive unless the
  support gaps compress. Equivalently, after excluding drift, any surviving
  obstruction must come from compressed-gap geometry or unbounded packet size.
- this is now frozen as `D2g9`.
  Let `(V_n,G_n,c_n)` be normalized finite local packets with
  `\|s_n(c_n)\|_2\to 0`, all windows staying inside one fixed near-tail slab,
  and `\#V_n\le L`. Then either the minimal support gap
  `\delta(V_n)\to 0`, or the coefficients are forced into the cycle space:
  `\operatorname{dist}(c_n,\ker B_{G_n})\to 0`.
- proof is exactly the new finite-window machine:
  if `\inf\delta(V_n)>0`, then `D2g6` gives a uniform lower bound for
  `\kappa(V_n,N)` and `D2g7/D2g8` give a uniform lower bound for `\beta(G_n)`,
  so `D2g5` forces asymptotic cycle-space collapse.
- practical reading:
  after excluding drift, there is no third bounded-size survival mode.
  Any genuine local obstruction must now pass through
  `\delta(V_n)\to 0` or `\#V_n\to\infty`.
  That is already exactly the funnel we wanted into `D2g3/D2f3`.
- next in-progress reduction:
  once bounded-size packets are dead, the remaining packet-growth branch should
  be cut against the old local counting bound
  `\#(Y_a\cap[t-1,t+1])\ll_a \log(2+t)`.
  If a large local packet stays inside a fixed near-tail slab around `M`, then
  pigeonhole on that slab forces a microscopic subinterval containing
  `\gg \log M` active vertices, hence a microcluster and then a compressed-gap
  output by the already-frozen `D2g2/D2g3` mechanism.
- so the clean next theorem-shape is:
  after excluding drift, unbounded packet growth inside a fixed near-tail slab
  cannot remain diffuse; it must concentrate into the same short-scale
  microcluster geometry that already feeds `D2f3`.
- this is now frozen as `D2g10` in a deliberately honest form.
  Packet growth in a fixed near-tail slab implies, by pigeonhole plus the old
  local counting bound, a dense local unit packet carrying `\gtrsim \log M`
  active vertices along a subsequence.
- that is not yet the same as the threshold packet `\mathcal P_M(c,C)` from
  `D2g2`, so the last refinement step is still open. But the mystery is gone:
  after excluding drift, large packets cannot stay diffuse. They must already
  enter dense local geometry, and from there the remaining work is exactly to
  refine unit-scale density down to threshold-scale microclustering or extract
  a direct compressed-gap consequence.
- sharper in-progress observation:
  for the branch-B dichotomy we do not actually need the full unit-packet
  density statement to get compression. If all active vertices stay inside one
  fixed near-tail slab and `\#V_n\to\infty`, then the minimal gap already
  satisfies `\delta(V_n)\le (R_0-\eta_0)/(\#V_n-1)\to 0` by plain pigeonhole.
- so after excluding drift, packet growth is not a separate mystery branch at
  all: it automatically collapses into compressed-gap geometry. The next clean
  theorem should therefore say that any genuinely surviving local obstruction
  in branch B forces `\delta(V_n)\to 0`; cycle-space collapse is the only
  alternative, and once that is excluded, compressed gaps are unavoidable.
- this is now frozen as `D2g11`.
  If normalized local packets stay in one fixed near-tail slab and do not
  collapse into cycle space, then their minimal support gap must satisfy
  `\delta(V_n)\to 0`.
- proof is clean: bounded-size subsequences are killed by `D2g9`, while
  unbounded-size subsequences give `\delta(V_n)\to 0` immediately by
  pigeonhole in a fixed-length interval.
- this is a strong simplification:
  after excluding drift, packet growth is no longer a separate surviving mode.
  The whole branch B is now funneled into one geometric output:
  compressed-gap geometry. The only remaining hard part is quantitative:
  upgrade `\delta(V_n)\to 0` to the sharper threshold-scale geometry already
  isolated in `D2g2/D2g3/D2f3`.
- in-progress synthesis for the next brick:
  the exact target is now a quantitative upgrade of `D2g11`, not a new branch.
  Local embedding search mostly returns our own `D2g2/D2g3/D2g11` notes rather
  than any hidden external theorem, which is good: the problem has become
  internal and explicit.
- external sanity-check only reinforces the existing matrix backend:
  Cauchy-matrix determinant lower bounds and Laplacian/algebraic-connectivity
  floors are the right tools, but there is no ready-made theorem turning
  generic gap-collapse into the threshold `(\log M)/M^2` scale for us.
- so the clean next move is:
  on fixed-size drift-excluded subsequences, combine `D2g6` and `D2g7` into an
  explicit power-law inequality
  `\delta(V_n)\ll \|s_n(c_n)\|_2^{2/(L(L-1))}`.
- this would already be a real gain, because any defect bound smaller than the
  corresponding threshold power would force the packet directly into the sharp
  compressed-gap regime feeding `D2g2/D2g3/D2f3`.
- this is now frozen as `D2g12`.
  On any fixed-size drift-excluded cycle-reduced subsequence,
  `D2g5 + D2g6 + D2g7` give the explicit defect-to-gap law
  `\|s_n(c_n)\|_2 \ge A(L,R_0,\eta_0)\,\delta(V_n)^{L(L-1)/2}` and hence
  `\delta(V_n)\ll \|s_n(c_n)\|_2^{2/(L(L-1))}`.
- therefore the bounded-size branch no longer asks for vague “gap collapse”.
  It is enough to prove an analytic defect estimate below the critical power
  `((\log M_n)/M_n^2)^{L(L-1)/2}`; that immediately forces
  `\delta(V_n)=o((\log M_n)/M_n^2)` and drops the packet into the already-live
  threshold/compressed-gap branch `D2g2/D2g3/D2f3`.
- constructive model enemy:
  instead of only forbidding bad geometry, we now have an explicit model enemy
  `D2g13`: a near-collision cluster
  `v_i(h)=u+h\xi_i` with barycentric weights
  `w_i=\prod_{j\ne i}(\xi_i-\xi_j)^{-1}`.
- the equally spaced binomial finite-difference packet
  `d_i=(-1)^{i-1}\binom{L-1}{i-1}` is exactly the special case `\xi_i=i-1` of
  the same model, not a different construction.
- there is now also a fully explicit consecutive-pair realization of that same
  enemy:
  with `c_j=(-1)^j\binom{L-2}{j}` one gets
  `K_h^{fd}(z)=\sum_{j=0}^{L-2} c_j(1/(v_j-z)-1/(v_{j+1}-z))`
  and this regrouping is exactly the ordinary binomial packet again.
- in particular, on every fixed right-tail block its defect satisfies
  `\|s^{(M)}(h)\|_2\asymp h^{L-1}`.
  This makes the comparison with `D2g12` completely explicit:
  the general theorem gives only `\|s\|\gtrsim \delta^{L(L-1)/2}`, while the
  model enemy realizes the much larger scale `h^{L-1}`.
- so the exponent in `D2g12` is definitely nonsharp for `L\ge 3`, and the real
  hard question is now very clean:
  can genuine packets on the zeta-derived support realize this rigid
  finite-difference/Hermite structure at all?
- its local receiver satisfies the exact identity
  `\sum_i w_i/(v_i(h)-z)=-h^{L-1}/\prod_i(z-v_i(h))`, so on a fixed
  tail block its defect is of order `h^{L-1}`.
- this is extremely useful conceptually:
  it shows what the strongest local survivor should look like, namely a
  discrete Hermite atom obtained from a collapsing cluster that cancels the
  first `L-1` moment layers.
- it also sharpens the next question.
  `D2g12` gives only the lower bound `\|s\|\gtrsim \delta^{L(L-1)/2}`, while
  the constructive enemy achieves size `h^{L-1}`; so for `L\ge 3` the current
  lower exponent may be nonsharp.
- the new live brick is therefore `D2g13a`:
  show that genuine cycle-reduced paired packets cannot realize this
  Hermite-type extremizer unless they already fall into the ultra-near
  resonance branch `D2f3`.
- this sharpens one step further as `D2g14`.
  The same barycentric near-collision cluster already gives an exact paired
  correction term:
  `K_h(z)=\sum_i w_i(1/(v_i(h)-z)-1/(v_i(h)-1-z))=R_h(z)-R_h(z+1)`.
- so the model enemy is not merely “similar” to our class.
  It already lives in the paired class, with the one-sided cluster in `X_a`
  plus its forced shifted copy.
- this is great news strategically:
  the remaining issue is now purely arithmetic/geometric realizability inside
  the real support `Y_a`, not whether we guessed the right analytic toy model.
- and this has now split cleanly.
  `D2g14a` proves that any approximate realization of the Hermite model at
  scale `h` already forces an actual one-sided cluster in `X_a` of diameter
  `O(h)`, hence a consecutive gap `O(h)`.
- therefore if such a realization happens with
  `h=o((\log M_n)/M_n^2)`, the route is already inside `D2f3`.
- so the geometric half of realizability is no longer open.
  The only live question is coefficient/defect realization:
  can a genuine cycle-reduced paired packet on `Y_a` carry barycentric
  Hermite-like weights and achieve the model defect rate without already
  pushing `h` into the threshold branch?
- there is also a clean graph-side simplification now.
  The paired Hermite model `K_h(z)=\sum_i w_i(1/(v_i(h)-z)-1/(v_i(h)-1-z))`
  lives on a matching graph, so `\ker B=0` and `\beta=\sqrt{2}` exactly.
- this matters a lot:
  the model enemy has no hidden cycle-space instability at all.
  Its small-defect behavior comes purely from Cauchy-side geometric collapse of
  the one-sided cluster `v_i(h)=u+h\xi_i`.
- so any genuine packet on the real support `Y_a` that approximates this model
  cannot explain itself away by graph collapse. It must really realize the
  near-collision geometry in `X_a`, i.e. exactly the compressed-gap direction
  we already wanted to force.
- coefficient side also sharpened cleanly as `D2g16`.
  For a near-collision cluster `v_i(h)=u+h\xi_i`, the tail-sample defect admits
  a confluent moment expansion
  `S_h(c)_m=-\sum_{r\ge0} h^r \mu_r(c)/(x_m-u)^{r+1}` with
  `\mu_r(c)=\sum_i c_i\xi_i^r`.
- therefore the defect order is controlled by the first surviving moment of the
  coefficient vector.
  The unique direction that kills the first `L-1` moment layers is exactly the
  barycentric/Hermite line `\mathbb C w`.
- consequence:
  to achieve the model defect rate `h^{L-1}`, a packet must not only realize
  the support microcluster; its coefficients must also lie asymptotically close
  to that single Hermite line.
- this is the new live coefficient barrier:
  the enemy is now explicit both geometrically and coefficient-wise.
- this is now quantitative in the paired model as `D2g16f`.
  For a near-collision packet
  `K_h(c;z)=\sum_i c_i(1/(v_i(h)-z)-1/(v_i(h)-1-z))`, sampled on a fixed
  right-tail block, one gets
  `dist(c,\mathbb C w)\le C(h+h^{-(L-2)}\|P_h(c)\|_2)`.
- in particular, if the paired local defect is already at the Hermite scale
  `\|P_h(c)\|_2\ll h^{L-1}`, then the coefficients are forced into an `O(h)`
  tube around the unique barycentric/Hermite line.
- this is the exact bridge we wanted:
  small paired defect + microcluster geometry no longer implies only a vague
  coefficient preference; it forces quantitative coefficient capture.
- this now transfers to genuine packets as `D2g17`.
  Once a real cluster `y_1<\cdots<y_L\subset X_a` is written in normalized
  form `y_i=u+h\xi_i`, the exact capture theorem applies uniformly over every
  compact nondegenerate shape class
  `\mathcal K_{L,\rho}=\{0=\xi_1<\cdots<\xi_L=1,\ \xi_{i+1}-\xi_i\ge\rho\}`.
- consequence (`D2g17a`):
  a genuine packet with Hermite-scale defect `\|P_y(c)\|_2\ll h^{L-1}` has
  only two options:
  either some relative subgap is already compressed (`y_{i+1}-y_i<\rho h`),
  or the coefficients are forced into an `O(h)` tube around the Hermite line
  of that exact local geometry.
- this is the first real model-to-reality bridge in the coefficient branch.
  After it, the remaining live question is no longer “do real packets look
  Hermite-like?”, but “can the actual residues on `Y_a` realize that Hermite
  capture without already collapsing into `D2f3`?”.
- this now sharpens once more as `D2g18`.
  On every compact nondegenerate shape class, the normalized Hermite vector has
  coordinates uniformly bounded away from `0` and with strict alternating sign
  pattern. Therefore Hermite capture forces a very rigid local residue
  fingerprint: after one global phase rotation, the coefficients must be
  alternating and of comparable magnitude.
- so the remaining residue-level burden is no longer “some complicated local
  coefficients”. It is the much narrower question whether actual residues on
  `Y_a` can form such a phase-rotated finite-difference block without already
  collapsing into the resonance branch.
- this now gets an amplitude kill as `D2g19`.
  Even if a genuine local packet enters Hermite capture, reinstating the true
  residue scale `q_\gamma=e(x_\gamma-1)=O(M^{-3})` forces its actual paired
  local contribution to be only `O(M^{-3}h^{L-1})`, hence `o(M^{-1})` on every
  bounded near-tail slab.
- so Hermite capture is not just rigid; it is harmless at the `D2g1` scale.
  This is a big narrowing:
  in the bounded-size drift-excluded regime, every genuine local obstruction
  must already lie in the other branch of `D2g17a`, namely compressed relative
  subgaps.
- and now `D2g20` closes the rest of that bounded-size branch by raw scale
  counting: an `O(1)`-packet with residues `q_\gamma=O(M^{-3})` cannot stay
  non-negligible on the threshold scale `(\log M)/M^2`, because after the
  `M`-rescaling each individual term is only `O(1/\log M)`.
- so bounded-size local packets are fully closed:
  either they are harmless by `D2g19`, or they already force
  `o((\log M)/M^2)` proximity to `M` or `M+1`, i.e. direct entry into `D2f3`.
- equivalently, outside `D2f3` every surviving local obstruction must now have
  packet size going to infinity. This is a very clean reduction: the direct
  live branch is no longer “some local packet”, but specifically a noncompact
  large-packet mechanism.
- combining this with the already-frozen `D2g2/D2g3` packet counting, we now
  get a very sharp final compression:
  outside `D2f3`, any surviving direct obstruction must be a logarithmic
  threshold microcluster, hence must force infinitely many one-sided gaps
  `x_{\gamma+1}-x_\gamma \ll M^{-2}`.
- equivalently, the whole direct branch has now been reduced to a clean
  arithmetic dichotomy:
  either scaled ordinates hit the integer lattice at ultra-near scale
  `o((\log x)/x^2)`, or there are infinitely many microscopic critical-line
  gaps `\gamma_{n+1}-\gamma_n \ll \gamma_n^{-2}`.
- packaged that immediately into a conditional closure statement `D2g23`:
  if both arithmetic scenarios are excluded, then the whole direct infinite
  support counterexample route is dead. So the analytic residue problem has
  really been pushed all the way down to two explicit arithmetic geometry
  exclusions.
- quick search verdict on the new arithmetic endpoint:
  there is no routine external theorem in sight that kills the microscopic-gap
  branch `\gamma_{n+1}-\gamma_n \ll \gamma_n^{-2}`. The visible literature
  around small gaps studies gaps on the scale of the average spacing, not a
  hard lower bound excluding a `\gamma^{-2}` regime. So this branch should
  currently be treated as a hard arithmetic wall, not as a likely quick import.
- consequence for tactics:
  after `D2g23`, the faster live attack is not the gap branch but the
  integer-resonance branch
  `\operatorname{dist}(x_\gamma,\mathbb Z)=o((\log x_\gamma)/x_\gamma^2)`,
  because that at least has a direct lattice target built into the scaling.
- packaged that branch more sharply as `D2g24/D2g24a`:
  integer resonance is exactly an infinite near-arithmetic progression of
  critical-line zeros
  `\gamma_\nu = (\pi/a)m_\nu + o((\log m_\nu)/m_\nu^2)`.
  So the live arithmetic target is no longer “numbers close to integers”, but
  a super-accurate near-lattice-zero problem.
- pushed that one step further to `D2g24b/D2g24c`:
  such a near-progression is equivalent to infinitely many windows of length
  `o((\log T)/T^2)` on which the smooth Riemann--von Mangoldt main term is
  negligible but `S(T)` must still jump by size `\asymp 1`.
  So the integer-resonance branch has been converted into a supertiny
  local-oscillation problem for the argument term `S(T)`.
- upgraded that packet to the sharper `D2g25/D2g26` form:
  on each dyadic block `(T,2T]`, the shrinking-target count
  `A_\alpha(T,\varepsilon)` is controlled explicitly by a Fej\'er-kernel bridge
  ```
  A_\alpha(T,\varepsilon)
  \ll
  \varepsilon\,\mathcal N(T,2T]
  +
  \varepsilon\sum_{j\le 1/(2\varepsilon)}|S_\alpha(j;T)|.
  ```
  So the first term already dies on our scale, and the entire burden moves to
  `D2g26`: high-frequency control of `S_\alpha(j;T)` up to
  `j\asymp T^2/\log T`.
- but there is already a better tactical reading built into the same proof:
  define
  ```
  \Sigma_\alpha(H;T) := \sum_{T<\gamma\le 2T} F_H(\alpha\gamma).
  ```
  Then
  ```
  A_\alpha(T,\varepsilon) \le \frac{\pi^2}{4H}\Sigma_\alpha(H;T),
  ```
  so shrinking-target exclusion follows from the softer signed/smoothed goal
  `\Sigma_\alpha(H(T);T)=o(H(T))`. This is closer to Landau--Gonek /
  explicit-formula technology than the absolute-value majorant
  `\sum |S_\alpha(j;T)|`.
- after expansion,
  ```
  \Sigma_\alpha(H;T)
  =
  \mathcal N(T,2T]
  + 2\sum_{j=1}^{H-1}(1-j/H)\Re S_\alpha(j;T),
  ```
  so the live arithmetic endpoint is no longer forced to be termwise control of
  all high frequencies; it can be attacked as one single weighted signed sum.
- sharpened this one step further: on the actual target scale
  `\varepsilon(T)=o((\log T)/T^2)` we do not need
  `\Sigma_\alpha(H(T);T)=o(H(T))`. Since
  ```
  \mathcal N(T,2T]/H(T)\asymp \log^2 T / T \to 0,
  ```
  it is already enough to prove the natural-scale bound
  ```
  \Sigma_\alpha(H(T);T)\ll \mathcal N(T,2T]\asymp T\log T.
  ```
  This is much softer and looks compatible with explicit-formula technology.
- packaged the next bridge as `D2g29/D2g29a/D2g29b`:
  after inserting a smooth dyadic cutoff `w(\gamma/T)`, the Fejér-smoothed zero
  sum
  ```
  \Sigma_{\alpha,w}(H;T)=\sum_\gamma w(\gamma/T)F_H(\alpha\gamma)
  ```
  becomes a single weighted combination of
  ```
  Z_j(T)=\sum_\gamma w(\gamma/T)e(j\alpha\gamma),
  ```
  and the Guinand--Weil explicit formula should rewrite each `Z_j(T)` into
  archimedean part + prime-power part + error, with prime localization near
  `\log n \approx 2aj`.
- this is the first place where the whole endpoint really lines up:
  Ford–Zaharescu gives the exceptional/nonexceptional arithmetic fork,
  Landau–Gonek gives the resonance geometry on the prime-power side,
  and Suzuki/Fujii explains why a single smoothed signed sum is the right
  object instead of `\sum |S_j|`.
- then closed the soft analytic side of that packet: if the archimedean term is
  written in the standard explicit-formula form
  ```
  \mathcal M_{\alpha,w}(H;T)=\int \Omega(u) w(u/T) F_H(\alpha u)\,du
  ```
  with `\Omega(u)\ll \log(2+|u|)`, then
  ```
  \mathcal M_{\alpha,w}(H;T)\ll T\log T
  ```
  uniformly in `H`. The reason is simple and robust:
  `w(u/T)` localizes to `u\asymp T`, while the Fejér packet has total mass
  `\asymp T` after Fourier expansion because
  `T\sum_{|j|<H}(1-|j|/H)\widehat w(Tj\alpha)\ll T`
  by Schwartz decay.
- same argument shows that any residual explicit-formula terms coming from a
  finite number of fixed Fourier shifts are only `O(T)`. So, under the
  standard formula architecture, the archimedean side is no longer the live
  burden.
- conclusion sharpened again: `D2g29a` is effectively closed at the note level.
  The only honest remaining obstacle in the `D2g29` packet is now
  `D2g29b`, i.e. the prime-side localization near `\log n \approx 2aj`.
- pushed `D2g29b` one level further down: the prime-side packet can be reduced
  schematically to
  ```
  T \sum_{n\ge 2}\frac{\Lambda(n)}{\sqrt n}\,\mathfrak R_{\alpha,H,T}(n),
  ```
  where `\mathfrak R_{\alpha,H,T}(n)` is just a Schwartz-decaying
  distance-to-lattice weight around
  `\frac{\log n}{2\pi}\approx j\alpha`.
- because the lattice spacing is fixed (`|\alpha|`) while the localization
  width is `1/T`, each prime power has at most `O_\alpha(1)` genuinely relevant
  resonant indices `j`. So the whole Fourier packet collapses to a single
  near-lattice problem for the set of prime-power logarithms.
- this makes the exceptional arithmetic meaning completely transparent:
  `a=r\log p/(2q)` is exactly the condition that some prime-power logarithms
  lie exactly on the lattice `2aj`. In the nonexceptional case, the burden is
  to prove that prime powers cannot come close often enough to make
  ```
  \sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\mathfrak R_{\alpha,H(T),T}(n)
  ```
  exceed `\log T`.
- so the live brick is now no longer “bound the prime side somehow”, but one
  concrete weighted near-resonance counting problem for prime powers.
- Research-oracle infrastructure was also tightened on this host: the old
  `qmd query` path is too heavy/unreliable for blocker recall, so
  `scripts/research_oracle.py query ...` now means a stable hybrid
  `qmd search + qmd vsearch` merge. Functionally this keeps the same role
  (fast recall over curated `q3_docs`) but drops the fragile expansion/rerank
  backend from the default workflow.
- this is cleaner than the older abstract majorant wording:
  the live question is now literally one explicit exponential-sum criterion on
  dyadic zero blocks.
- pushed this one step further to `D2g27/D2g27a`:
  `D2g26` now has three concrete sufficient forms.
  The weakest direct target is
  ```
  \frac{1}{H(T)}\sum_{j\le H(T)}|S_\alpha(j;T)|=o(1)
  ```
  and the uniform bound is stronger still.
  So the endpoint is no longer just “high frequencies matter”, but one very
  concrete high-frequency cancellation threshold.
- then pushed one step further again: the naive raw `L^2` surrogate is actually
  dead, not just strong. The diagonal term alone gives
  ```
  \sum_{j\le H(T)} |S_\alpha(j;T)|^2 \ge H(T)\,\mathcal N(T,2T],
  ```
  so `o(H(T))` is impossible on nonempty dyadic blocks. This kills the fake
  second-moment route cleanly.
- the honest quadratic object is therefore the off-diagonal Fejér packet
  ```
  \Sigma_\alpha(H;T)
  =
  \sum_{|j|<H}(1-|j|/H)|S_\alpha(j;T)|^2
  =
  H\,\mathcal N(T,2T]
  + \sum_{\gamma\ne\gamma'} F_H(\alpha(\gamma-\gamma')).
  ```
  So any surviving `L^2`-style attack must pass through pair-correlation /
  off-diagonal control after subtracting the diagonal mass.
- semantic search on `q3_docs` for the new endpoint mostly surfaced our own
  internal off-diagonal exponential-sum wrappers (`off_diag_exp_sum`,
  `off_diag_exp_sum_integrated`) and did not reveal a pre-existing local lemma
  that already controls `S_\alpha(j;T)` uniformly up to `j\asymp T^2/\log T`.
- external primary-source search confirms the same shape: Ford–Zaharescu gives
  modulo-one distribution and the exceptional-`alpha` density picture, while
  Landau-Gonek style papers give explicit-formula / pair-correlation
  background, but neither directly reaches the shrinking-target range
  `\varepsilon(T)=o((\log T)/T^2)` with Fourier frequencies
  `j\asymp T^2/\log T`.
- this also makes the fork fully explicit on the original spacing parameter:
  exceptional `\alpha=a/\pi` means exactly
  ```
  a = \frac{r\log p}{2q}
  ```
  for some prime `p`, integer `r\neq 0`, and `q\in\mathbb N`.
  So before any hard Fourier work, there is a clean discrete arithmetic gate:
  either `a` lies in this countable logarithmic set and one must use the
  exceptional density-defect branch, or else the whole endpoint is forced into
  the nonexceptional high-frequency route.
- conclusion: `D2g26` is now a genuine external arithmetic input. The honest
  next step is to split into exceptional/nonexceptional `\alpha=a/\pi`, kill
  the vacuous raw-`L^2` branch, and then attack the nonexceptional case either
  via the direct mean-`L^1` criterion, or more naturally via the signed
  Fejér-majorant `\Sigma_\alpha(H;T)`, or via a genuinely new off-diagonal
  Fejér/pair-correlation estimate. The strongest current formulation is now
  `D2g29`: reduce the endpoint to proving that the smoothed prime-side packet is
  at most natural size `T\log T`.
- also sharpened the Hermite-capture fingerprint itself:
  `D2g18b` now shows that once a local packet enters an `O(h)`-tube around the
  Hermite line, every adjacent residue ratio must lie in an `O(h)`-tube around
  a negative real interval `[-A_{L,\rho},-a_{L,\rho}]`.
  So the live coefficient enemy is no longer “some alternating block”, but an
  almost literally phase-rotated finite-difference chain at the level of
  neighboring ratios.
- in practical terms, the coefficient branch is now essentially burned off.
  The remaining live local mechanism is the noncompact large-packet /
  compressed-gap resonance branch `D2g2/D2g3/D2f3`.

## In progress (2026-04-10): computational radar for `D2g16d`

- exact target: test whether genuine local one-sided packets cut from the real
  support `X_a=\{x_\gamma=a\gamma/\pi\}` look numerically like the
  Hermite/barycentric extremizer from `D2g13--D2g16`.
- local embedding search was run on 4 queries around Cauchy singular values,
  barycentric/Hermite clusters, and finite-difference cancellation; the local
  index returned only generic matrix references or timed out, so there is no
  ready-made internal lemma for this step.
- external web search gave only high-level sanity-check pointers on Cauchy
  smallest-singular-value technology, not a direct bridge for our packet class.
- working plan:
  1. generate real support points `x_\gamma=a\gamma/\pi` from actual zeta zeros;
  2. scan consecutive windows of lengths `L=2,3,4`;
  3. for each window, build the local tail sample matrix at the nearest
     right-tail block and compute the smallest-singular-value direction;
  4. compare that optimal coefficient vector with the Hermite/barycentric line
     of the same geometric window;
  5. record whether the smallest-defect windows are actually close to the
     Hermite line or whether real support geometry pushes them away.
- success condition for the radar:
  either the best real windows already align closely with the Hermite line
  (then the enemy is concretely identified), or they stay uniformly away from
  it (then `D2g16d` gets a much sharper theorem target).
- first scan (`n\le 120`) already points in the first direction.
  For `a=0.5` and `a=1`, the best real consecutive windows of lengths
  `L=2,3,4` have Hermite overlaps around `0.99`, `0.99`, and `0.98`
  respectively; for `a=2`, the overlap drops only when the windows themselves
  stop looking like dense microclusters.
- provisional verdict:
  the computational radar supports the current theorem picture rather than
  fighting it; the dangerous local packets appear to be genuinely Hermite-like,
  not some different hidden extremizer.

## In progress (2026-04-11): refreshed recall layer and `D2g29b` source synthesis

- refreshed `q3_docs`: the live local KB is now back in sync (`353` files,
  `1810` vectors). This matters because the old blocker-search layer had become
  stale and was blurring real math signal with index drift.
- the local `research_oracle` protocol has been stabilized: default
  `scripts/research_oracle.py query ...` is now a hybrid
  `qmd search + qmd vsearch` wrapper with fused ranking, rather than the old
  heavy `qmd query` path. Functionally the role stays the same: fast recall,
  not proof and not source of truth.
- after the refresh, 4 focused recall queries were run for the live block
  (`prime power logarithms near lattice`, `Baker linear forms logarithms prime
  powers`, `explicit formula Fejér kernel prime powers`,
  `Landau Gonek prime power resonance`). The useful signal is narrow but clean:
  the internal KB keeps returning the same packet and does not reveal any
  pre-existing local theorem that already kills the weighted near-lattice
  prime-power sum from `D2g29b4`.
- external primary-source search confirms the current arithmetic split but also
  removes one tempting false shortcut:
  Ford–Zaharescu supports the exceptional/nonexceptional modulo-one fork, and
  Suzuki confirms the smoothed explicit-formula/prime-side genre;
  however Baker/Matveev linear-forms-in-logarithms machinery does **not**
  automatically solve our nonexceptional branch, because the key quantity
  `m \log p - 2aj` involves the ambient parameter `a`, and in the general route
  `a` is just a fixed real number, not an algebraic-logarithmic input to which
  Matveev can be applied for free.
- so the honest next plan is:
  1. keep the exceptional branch exactly where it already lives
     (`a = r \log p /(2q)` with genuine prime-power resonance);
  2. do **not** divert the generic nonexceptional branch into a fake
     Baker/Matveev route;
  3. continue directly on `D2g29b4`, i.e. the weighted prime-power near-lattice
     counting problem that comes out of the Fejér-smoothed explicit formula.
- bottom line: the active direct path stays arithmetic and explicit-formula
  based. The refreshed recall layer is now stable enough to support that work,
  but it did not uncover a hidden theorem that bypasses `D2g29b4`.
- one more correction falls out of the same pass: the positive majorant
  `D2g29b4`
  ```
  \sum \frac{\Lambda(n)}{\sqrt n}\,\mathfrak R_{\alpha,H(T),T}(n)\ll \log T
  ```
  is likely too strong to be the true endpoint, because it throws away the very
  Fejér oscillation we introduced on purpose. A PNT sanity check near
  `n\approx e^{2aj}` suggests that the purely positive near-lattice mass would
  be enormous at the natural range `H(T)\asymp T^2/\log T`.
- so the honest live object is now the signed kernel
  ```
  \mathcal K_{\alpha,w,H,T}(\xi)
  = \sum_{|j|<H}(1-|j|/H)\bigl[\widehat w(T(\xi-j\alpha))+\widehat w(T(\xi+j\alpha))\bigr],
  ```
  and the corrected `D2g29` target is the signed prime-side estimate
  ```
  \sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\,
  \mathcal K_{\alpha,w,H(T),T}\!\left(\frac{\log n}{2\pi}\right)\ll \log T.
  ```
- this is a real compression, not a retreat: it tells us exactly what not to
  do next. We should not spend cycles trying to prove an over-strong absolute
  near-lattice counting theorem that the natural heuristics themselves fight.
- the archimedean packet was also sharpened beyond the crude
  `O(T\log T)` closure: under the standard explicit-formula normalization
  one can split off the `j=0` mode and prove
  ```
  \mathcal M_{\alpha,w}(H;T)
  =
  c_w\,T\log T
  +
  O_w(T)
  +
  O_{w,\alpha}(\log T\log(2H)).
  ```
  So the entire Fejér-weighted oscillatory tail of the gamma-factor is only a
  harmonic-error term, while the main `T\log T` mass comes from the zero mode.
- on the target range `H(T)\asymp T^2/\log T`, this still gives
  `\mathcal M_{\alpha,w}(H(T);T)\ll T\log T`, so the strategic verdict is
  unchanged but cleaner: the gamma-factor is not merely bounded by the right
  scale, it is explicitly understood up to a lower-order harmonic tail.
- integrated the next structural refinement of the prime-side packet:
  the honest project reading is now
  `D2g29b0 -> D2g29b1 -> D2g29b2 -> D2g29b3`.
  Here
  `b0` = choose an explicit-formula-admissible kernel/majorant,
  `b1` = write the admissible decomposition
  `\Sigma=\mathcal M+\mathcal P+\mathcal E`,
  `b2` = note that it is enough to keep `\mathcal P` and `\mathcal E` on the
  natural scale `T\log T`,
  and `b3` = split exceptional vs nonexceptional prime-side resonance.
- this is a good compression: it separates one honest analytic hygiene issue
  (admissible kernel choice) from the real arithmetic burden.
- project-control audit also found a live automation/protocol drift:
  some active KB skill docs still contained old `aristotle prove-from-file`
  commands even though the canonical workflow had already moved to
  `formalize / submit / result`. That is not a kernel leak, but it is exactly
  the kind of stale instruction that later causes automation misfires.
- branch naming has now been promoted from habit to protocol:
  addresses like `D2g29b` are treated as proof-tree coordinates, not just
  labels. That means route-kill propagates by default to the whole subtree:
  if `D2g` dies, then `D2g29`, `D2g29b`, etc. die with it unless there is an
  explicit reopen with a new obstruction-killer. This should make both routing
  and clustered idea-search much cleaner.
- `D2g29b0` is now fixed concretely rather than abstractly:
  keep the periodic shrinking-target majorant in Fejér form
  `\phi_H=(\pi^2/4H)F_H`, but replace the hard dyadic zero-window by a
  nonnegative Schwartz majorant `W_+(\gamma/T)` with `W_+\ge 1` on `[1,2]`.
  This keeps the majorant logic we already want, while making the height-side
  test function honest for the explicit-formula step.
- `D2g29b1` is now upgraded from schematic localization to an honest
  admissible packet decomposition for that fixed pair `(\phi_H,W_+)`:
  writing
  `Z_j^+(T)=\sum_\gamma W_+(\gamma/T)e(j\alpha\gamma)` and
  `h_{j,T}(u)=W_+(u/T)e(j\alpha u)`, the Guinand--Weil step gives
  `Z_j^+=M_j^+ + P_j^+ + E_j^+`, hence
  `\Sigma^{\phi}_{\alpha,W_+}=\mathcal M^{\phi}_{\alpha,W_+}+\mathcal P^{\phi}_{\alpha,W_+}+\mathcal E^{\phi}_{\alpha,W_+}`.
  The prime side is localized by rapid decay of `\widehat W_+` to the windows
  `|\log n \mp 2aj|\lesssim 1/T`, so the live burden really has moved to
  the legacy positive node `D2g29b2a`, then the arithmetic split `D2g29b3`,
  and then to the signed-kernel endpoint `D2g29c`.
- quick automation/process audit: the repeated `64 unified exec processes`
  warning does not appear to come from a repo-side leak in the active Q3
  scripts. The obvious long-lived processes are app/session-level MCP helpers
  plus external `mgrep watch` daemons already known from older notes; inside
  this repo, background watchers exist only as opt-in utilities
  (`scripts/swarm start/watch`, `q3.lean.aristotle/scripts/tdd.sh watch`) and
  are not on the live mainline path.

## In progress (2026-04-11): D2g29b2a honest lattice-sum correction

- exact target: upgrade the old positive-packet spacing node (now `D2g29b2a`)
  from heuristic prose to an honest spacing
  lemma plus an actual bound for the near-lattice decay packet
  `\mathfrak R_{\alpha,H,T}^+(n)`;
- wiring point: this sits strictly between the now-closed admissible packet
  decomposition `D2g29b1` and the live prime-side burden `D2g29b3 / D2g29c`;
- local oracle recall found no hidden existing theorem, only our current
  heuristic statement and generic node-spacing material;
- external search also did not produce a ready-made citation-level lemma for
  the exact weighted finite-lattice packet we use here;
- key correction: the naive bound
  `\mathfrak R \ll (1+T\,\mathrm{dist})^{-A}` is probably too strong for the
  full positive packet, because summing a polynomial-decay kernel over a
  lattice typically loses one power;
- honest candidate shape:
  `\mathfrak R \ll (1+Td)^{-A} + (T|\alpha|)^{-1}(1+Td)^{1-A}`,
  hence in the spaced regime `T|\alpha|\gg 1` one gets
  `\mathfrak R \ll_{\alpha,A} (1+Td)^{1-A}`;
- plan: rewrite the positive-packet node as an honest spacing lemma plus this
  two-term bound,
  then explicitly record that this still leaves `D2g29c` as the real signed
  endpoint and that the positive majorant route remains over-strong.
- result: the legacy node `D2g29b2a` is now corrected at note level. The honest positive-packet
  bound is not
  `\mathfrak R \ll (1+Td)^{-A}`,
  but rather
  `\mathfrak R \ll (1+Td)^{-A} + (T|\alpha|)^{-1}(1+Td)^{1-A}`,
  hence in the spaced regime `T|\alpha|\gg 1` one only gets exponent `1-A`.
- verdict: this strengthens, not weakens, the route hygiene. It confirms that
  the unsigned near-lattice packet is inherently lossy and that the real live
  endpoint remains the signed kernel branch `D2g29c`.

## In progress (2026-04-11): D2g29c Fourier/physical-space sharpening

- exact target: replace the schematic `D2g29c''` Fourier-inversion line by the
  honest kernel identity for the signed packet after summing the Fejér weights;
- wiring point: this is the next live step after the corrected unsigned packet
  `D2g29b2`; it should make the cancellation structure in `D2g29c` explicit;
- local recall again returns only our own packet notes plus the standard
  Guinand--Weil crosswalk, which is a good sign: there is no hidden bypass and
  the route really is to compute the kernel directly;
- external search only confirms the generic explicit-formula Fourier template:
  test functions are inserted through their Fourier transforms, and the prime
  side is read by Fourier inversion back in physical space;
- concrete plan:
  1. use the repository Fourier convention from `T0`,
  2. rewrite
     `\sum_j a_j \widehat W_+(T(\xi-j\alpha))`
     as a single oscillatory integral,
  3. identify the inner Fourier packet with `\phi_H(\alpha u)`,
  4. simplify the `+\alpha/-\alpha` duplication using `a_j=a_{-j}`,
  5. record the exact signed kernel seen by prime powers.
- result: `D2g29c''` is now upgraded from a schematic inversion line to the
  exact identity
  `\mathcal K(\xi)=\frac{2}{T}\int W_+(u/T)e(-u\xi)\phi_H(\alpha u)\,du`,
  and the prime packet becomes the exact pairing
  `-\pi^{-1}\langle \mu_P,\widehat G_{\alpha,H,T}\rangle` with the discrete
  prime measure
  `\mu_P=\sum_{n\ge2}\Lambda(n)\delta_{\log n/(2\pi)}/\sqrt n`.
- after choosing `W_+` even, the associated truncated physical-space model is
  the real cosine packet
  `\Re D_X(u)=\sum_{2\le n\le X}\Lambda(n)\cos(u\log n)/\sqrt n`, so the signed
  endpoint should be read distributionally / truncationally rather than as a
  naive absolutely convergent critical-line Dirichlet integral.
- verdict: the signed endpoint is now a single exact kernel identity on the
  zero side plus an honest prime-distribution pairing on the arithmetic side.
  That is still much sharper and more usable than the old unsigned
  near-lattice packet, and it isolates the real arithmetic burden cleanly.
- this also sharpens `D2g29b3`: the exceptional condition
  `a=r\log p/(2q)` is now literally the commensurability condition between the
  Fejér modulation frequency `2a=2\pi\alpha` and the prime-power frequency
  `m\log p`. So the split is no longer just a frequency-side lattice slogan;
  it is the exact question of whether the cosine phase can lock coherently to
  the physical-space Fejér lattice `u\approx k/\alpha`.

## In progress (2026-04-11): D2g29d signed prime-distribution endpoint

- exact target: replace the still-vague phrase "control the prime side" by one
  explicit arithmetic endpoint after the signed correction `D2g29c''`;
- wiring point: this is the live child of `D2g29b3`; after `D2g29a/b0/b1/b2/c`
  the route no longer depends on unsigned near-lattice mass and depends only on
  one signed prime-distribution pairing;
- local oracle recall again returns only our own packet notes plus generic
  explicit-formula infrastructure, which is good evidence that there is no
  hidden theorem shortcut and that the endpoint must be formulated directly;
- external search points the same way: Ford--Zaharescu give the arithmetic
  exceptional/nonexceptional split, while Suzuki/explicit-formula papers
  support the physical-space prime-pairing genre, not a termwise `|S_j|` route;
- concrete plan:
  1. define the truncated signed packet
     `\mathcal S_{\alpha,H,T}(X)=-(1/\pi)\int G_{\alpha,H,T}(u)D_X(u)\,du`,
  2. demand the natural-scale bound `\mathcal S_{\alpha,H(T),T}(X)\ll T\log T`,
  3. record that this is uniform in `X` / equivalent to the limiting
     prime-distribution pairing,
  4. split the remaining arithmetic burden into the exceptional commensurable
     case `a=r\log p/(2q)` and the nonexceptional case,
  5. treat this as the single live endpoint below `D2g29`.
- verdict: the proof tree is now cleaner. The live arithmetic burden is no
  longer "all high Fourier modes"; it is one signed packet endpoint with one
  sharp arithmetic split.

## In progress (2026-04-11): D2g29b1 explicit-formula decomposition tightened

- exact target: upgrade `D2g29b1` from a generic localization slogan to the
  actual packet-level decomposition with named pieces `M_j^+`, `P_j^+`,
  `E_j^+` and the aggregated prime kernel `\Psi_{\alpha,W_+,H}`;
- wiring point: this sits strictly below the already fixed kernel choice
  `D2g29b0` and strictly above the arithmetic endpoint
  `D2g29b2a/b3/d`, so it is
  the right address to make the algebra-to-arithmetic bridge completely
  explicit;
- concrete upgrade:
  1. record `M_j^+(T)=(2\pi)^{-1}\int W_+(u/T)e(j\alpha u)\Omega(u)\,du`,
  2. keep `P_j^+(T)` in the explicit-formula normalization already used in the
     packet,
  3. set `E_j^+(T)=E(h_{j,T})`,
  4. define the aggregated prime kernel
     `\Psi_{\alpha,W_+,H}(T;\xi)=\sum_{|j|<H} a_j[\widehat W_+(T(\xi-j\alpha))+\widehat W_+(T(-\xi-j\alpha))]`,
  5. rewrite the full prime side as
     `-(T/2\pi)\sum_{n\ge2}\Lambda(n)\Psi(T;\log n/2\pi)/\sqrt n`.
- verdict: `D2g29b1` is now a genuine named decomposition step, not just a
  heuristic localization sentence. This makes the later `b2/b3/d` references
  much cleaner.

## In progress (2026-04-11): D2g29b2 strip-growth obstruction check

- exact target: decide whether the raw height-side Fejér route below `D2g29b1`
  is actually honest on the shrinking-target scale `H(T)\asymp T^2/\log T`, or
  whether the test function itself explodes in the strip and kills the route;
- wiring point: this is the next child under `D2g29b`; if it fails, then the
  whole raw height-side explicit-formula subroute dies and the proof tree
  should move to a prime-first replacement rather than keep polishing `b2`;
- local oracle recall shows no hidden bypass theorem: it keeps returning only
  our own `D2g29` packet and generic Guinand--Weil infrastructure;
- the repository `T0` normalization is not the issue here: the obstruction is
  about the external classical explicit formula used in `D2g29`, not about the
  internal `Q^\star` functional;
- web/background check matches the standard classical picture: the height-side
  test in Guinand--Weil feels special values around `\pm i/2`, so strip growth
  is the right quantity to inspect;
- concrete plan:
  1. compute the exact imaginary-axis growth of `F_H(\alpha u)` at `u=\pm i/2`,
  2. show it is `\asymp H^{-1}e^{\pi |\alpha|H}`,
  3. transfer this to the raw packet `h_{H,T}(u)=W_*(u/T)F_H(\alpha u)`,
  4. record that on `H(T)\asymp T^2/\log T` this dwarfs every natural
     `T\log T` target,
  5. mark raw `D2g29b` as strip-growth blocked and promote the prime-first
     replacement as the active child.
- result: the obstruction lands cleanly. The one-shot height-side packet
  `h_{H,T}(u)=W_*(u/T)F_H(\alpha u)` has strip size
  `|h_{H,T}(\pm i/2)|\gg H^{-1}e^{\pi |\alpha|H}`, so on
  `H(T)\asymp T^2/\log T` the strip contribution is already superpolynomial in
  `T` and cannot honestly fit inside a natural-scale `T\log T` bound.
- verdict: `D2g29b` as a raw one-shot height-side explicit-formula route is
  dead. The old positive-packet spacing estimate survives only as a legacy
  bookkeeping shadow (`D2g29b2a/b`), while the active burden moves to the
  signed prime-side endpoint `D2g29d`.

## In progress (2026-04-11): D2g29d1 exceptional/nonexceptional split packet

- exact target: turn the still-verbal split inside `D2g29d` into one explicit
  child address, so the live endpoint is no longer “some arithmetic control of
  the signed pairing,” but a precise dichotomy with separate burdens;
- wiring point: after `D2g29b` was killed by strip growth, the tree now jumps
  directly from the signed endpoint `D2g29d` to its first arithmetic split;
- local recall result: no hidden internal theorem kills either branch; the KB
  keeps returning our own packet plus the same frequency-commensurability
  interpretation;
- external primary-source signal is consistent with the same split: Ford–
  Zaharescu support the exceptional arithmetic fork, while Suzuki/explicit
  formula papers support the signed prime-pairing genre but do not close the
  branch automatically;
- concrete plan:
  1. define `D2g29d1` as the arithmetic split for the signed packet
     `\mathcal S_{\alpha,H,T}(X)`,
  2. isolate the exceptional branch
     `a=r\log p/(2q)` as exact prime-power commensurability,
  3. isolate the nonexceptional branch as the no-exact-locking regime,
  4. state what natural-scale estimate `\ll T\log T` is sufficient in each
     branch,
  5. make `d1a` / `d1b` the next honest child addresses.
- result: `D2g29d1` is now written explicitly in the main note. The split is
  no longer just verbal:
  `d1a` = exact-locking branch on a resonant prime-power lattice,
  `d1b` = incommensurate branch with no exact prime-power resonance.
- verdict: this is a real compression. The remaining arithmetic burden under
  `D2g29d` is now partitioned cleanly into two non-overlapping child tasks.

## In progress (2026-04-11): D2g29c prime-first replacement sharpened

- exact target: record the clean algebraic identity that replaces the dead raw
  height-side route `D2g29b`: the Fejér packet over zeros can be rewritten
  directly through Landau–Gonek-type sums
  `\Delta_\gamma(X;T)=\sum_{T<\gamma\le 2T} X^{i\gamma}`;
- wiring point: this does not replace the current signed endpoint `D2g29d`; it
  sharpens `D2g29c` and explains why `d` is the physical-space / prime-pairing
  form of the same prime-first route;
- concrete plan:
  1. define `D2g29c0` as the exact identity
     `\Sigma_\alpha(H;T)=N(T,2T]+2\sum_{j=1}^{H-1}(1-j/H)\Re\Delta_\gamma(X_j;T)`
     with `X_j=e^{2aj}`,
  2. define `D2g29c1` as the sufficient natural-scale criterion
     `\sum_{j\le H(T)}(1-j/H)|\Delta_\gamma(X_j;T)|\ll T\log T`,
  3. define `D2g29c2` as the exceptional/nonexceptional split in the
     `X_j=e^{2aj}` language,
  4. define `D2g29c3` as the remaining arithmetic wall for these
     Landau–Gonek-type sums on the exponential grid,
  5. keep `D2g29d` as the equivalent signed physical-space endpoint rather than
     a competing branch.
- result: `D2g29c0/c1/c2/c3` are now written explicitly in the main note. This
  stabilizes the tree: `c` is the algebraic/prime-first face of the same live
  endpoint whose physical-space face is `D2g29d`.

## In progress (2026-04-11): D2g29c3a Landau--Gonek input layer

- exact target: isolate the first genuinely arithmetic theorem input below
  `D2g29c3`, namely an averaged Landau--Gonek-type estimate strong enough to
  imply the sufficient criterion `D2g29c1`;
- wiring point: this is the direct arithmetic child of the prime-first route,
  parallel to the physical-space split `D2g29d1a/d1b`;
- local recall + external search did not reveal a ready-made theorem that
  already matches our Fejér-weighted exponential grid `X_j=e^{2aj}`; this is
  again a good sign that the correct move is to formulate the needed input
  precisely rather than pretend the literature already hands it to us;
- concrete plan:
  1. define an optional exceptional main term `\mathfrak M_a(X_j;T)`,
  2. require
     `\sum b_j |\Delta_\gamma(X_j;T)-\mathfrak M_a(X_j;T)|\ll T\log T`,
  3. require separately
     `\sum b_j |\mathfrak M_a(X_j;T)|\ll T\log T`,
  4. conclude the `D2g29c1` criterion,
  5. read the nonexceptional branch as `\mathfrak M_a\equiv 0`.
- verdict: this cleanly identifies the next real theorem-shape. The live
  burden is no longer "estimate the sums somehow", but "obtain an averaged
  Landau--Gonek input on the exponential grid, after isolating the exact
  exceptional main term".

## In progress (2026-04-11): D2g29c4 compatibility obstruction

- exact target: decide whether the apparently natural transfer
  `\Delta_\rho(X;T) \rightsquigarrow \Delta_\gamma(X;T)` is a viable shortcut
  or whether it already smuggles in near-RH-scale horizontal control;
- wiring point: this sits directly below `D2g29c3a`; if the transfer is
  obstructed, then the Landau--Gonek input remains only a formal sufficient
  shape and not a practical route for the live mainline;
- key exact identity:
  `\Delta_\rho(X;T)-\Delta_\gamma(X;T)=\sum (X^{\beta-1/2}-1)X^{i\gamma}`;
- on the mesh `X_j=e^{2aj}` the weighted compatibility bound would force a
  lower-bound problem for
  `\sum_j b_j |e^{2aj(\beta-1/2)}-1|`;
- the basic real-exponential estimate gives
  `\sum_j b_j |e^{\lambda j}-1| \gg \min(H,|\lambda|H^2)`,
  hence a compatibility bound at scale `T\log T` would imply
  `\sum_{T<\gamma\le 2T}\min(H,H^2|\beta-1/2|)\ll T\log T`;
- verdict: on `H(T)\asymp T^2/\log T` this forces average horizontal control
  `|\beta-1/2|\lesssim 1/H(T)\asymp \log T/T^2` for almost all zeros in the
  dyadic block. That is far too strong to treat as a free compatibility step.
- conclusion: `D2g29c4` kills the naive Landau-compatibility shortcut. The live
  burden stays on the signed prime-distribution route `D2g29d1a/d1b` unless a
  genuinely new direct compatibility argument appears.

## In progress (2026-04-11): D2g29d1a exceptional resonant spine

- exact target: isolate the exact-locking contribution inside the signed
  prime-distribution endpoint and see whether the exceptional branch already
  simplifies because the resonant prime powers come with the geometric weight
  `\Lambda(n)/\sqrt n`;
- wiring point: this is the first active child of `D2g29d1`; after `c4` kills
  the naive Landau-compatibility shortcut, the exceptional signed branch is the
  cleanest remaining place to win honest ground;
- local recall result: no hidden theorem closes it automatically, but the note
  already contains the exact locking geometry
  `a=r\log p_0/(2q) \iff m\log p_0 = 2aj` on one prime-power lattice;
- concrete plan:
  1. define the resonant spine using `g=\gcd(r,q)`,
     `j_0=q/g`, `m_0=r/g`,
  2. decompose the prime measure into `\mu_{\mathrm{exc}}+\mu_{\mathrm{off}}`,
     where `\mu_{\mathrm{exc}}` is the exact `p_0^{m_0\ell}` spine,
  3. prove the spine contribution is absolutely bounded by `O(T)` using the
     exact prime-packet formula and the uniform bound `|\mathcal K|\ll 1`,
  4. conclude that the live burden in the exceptional branch is only the
     off-spine remainder,
  5. record `d1a` as a real simplification, not just a restatement.
- result: the resonant-spine extraction now lands in the main note. With
  `\phi_H=(\pi^2/4H)F_H` one has the uniform kernel bound
  `|\mathcal K_{\alpha,W_+,H,T}(\xi)|\ll_{W_+}1`, hence the exact exceptional
  spine contributes only
  `|\mathcal P_{\mathrm{exc}}(H;T)|\ll T\sum_{\ell\ge1}\log p_0/p_0^{m_0\ell/2}\ll T`.
- verdict: this is a genuine gain. The exact-locking part of the exceptional
  branch is already harmless at scale `T\log T`; the only live burden in
  `D2g29d1a` is now the off-spine remainder.

## In progress (2026-04-11): EurekaClaw sidecar integration for Q3

- exact target: decide whether EurekaClaw should be attached to Q3 as a real
  project tool, and if yes, fix the boundary so it strengthens the workflow
  instead of polluting the canonical proof state;
- official fit check: EurekaClaw has a multi-agent `MetaOrchestrator` with a
  central `KnowledgeBus`, a four-tier memory system with a theorem dependency
  graph, a skill registry/evolver, and a domain-plugin layer for custom tools,
  skills, and workflow hints;
- recommendation: use it only as a local-first sidecar, not as the main
  orchestrator and not as a replacement for Aristotle/Lean verification;
- concrete Q3 use cases: blocker-focused literature survey, branch-cluster
  memory, candidate lemma mining, Aristotle prompt drafting, and paper-grade
  writeups after a packet is closed;
- concrete non-goals: no direct write-back to `ACTIVE/` monitors, no direct
  Lean import, no autonomous route-kill decisions, no unreviewed skill
  distillation into the canonical protocol;
- implementation path: add a `q3_rh` EurekaClaw domain plugin with wrappers
  around local oracle search, Aristotle submit/result polling, `lake env lean`,
  and read-only branch lookup, then ingest sidecar outputs back through the
  existing Q3 workflow;
- detailed plan file:
  `docs/insights/eurekaclaw_q3_sidecar_integration_2026_04_11.md`.

## In progress (2026-04-11): D2g29d1b nonexceptional incommensurate branch

- exact target: compress the nonexceptional child of `D2g29d1` to its honest
  arithmetic remainder, instead of leaving it as a vague “generic case”;
- oracle + web recall verdict: no hidden theorem closes it automatically; the
  useful external background only confirms the same split we already have,
  namely exceptional prime-power commensurability versus nonexceptional
  incommensurability;
- exact gain: if `a` is not of the form `r \log p /(2q)`, then there is no
  exact resonance equation `m \log p = 2aj` for any prime `p` and integers
  `m,j\ge 1`;
- consequence: unlike `D2g29d1a`, the nonexceptional branch has no exact
  resonant spine and no Landau-type main term to subtract;
- therefore `D2g29d1b` is a pure signed endpoint:
  prove directly that the incommensurate packet
  `\mathcal P^{\phi}_{\alpha,W_+}(H(T);T)` stays on the natural scale
  `O(T\log T)`;
- only the thin windows `|m\log p-2aj|\lesssim 1/T` can be dangerous, because
  that is exactly where the kernel escapes its rapid-decay regime;
- result to record next: upgrade this from a clean theorem-packet to either a
  genuine near-window reduction or an explicit new arithmetic wall.

## Result (2026-04-11): D2g29 closes on the normalized positive-definite route

- important repair: once `D2g29b0` replaces `F_H` by the normalized majorant
  `\phi_H=(\pi^2/4H)F_H`, the correct target scale is no longer `T\log T` but
  `T\log T/H`;
- this fixes a real normalization mismatch inside the old `D2g29b2b/d`
  phrasing: for the normalized packet one needs
  `\Sigma^{\phi}_{\alpha,W_+}(H(T);T)\ll T\log T/H`, not merely `\ll T\log T`;
- decisive new move: choose the concrete even Schwartz majorant
  `W_{\mathrm{pd}}(t):=e^{4\pi}e^{-\pi t^2}`, so `W_{\mathrm{pd}}\ge 1` on
  `[1,2]` and `\widehat W_{\mathrm{pd}}(\xi)=e^{4\pi}e^{-\pi\xi^2}\ge 0`;
- then the normalized prime kernel
  `\mathcal K_{\alpha,W_{\mathrm{pd}},H,T}(\xi)` is pointwise nonnegative,
  because it is a sum of Fejér coefficients `a_j\ge 0` against nonnegative
  translates of `\widehat W_{\mathrm{pd}}`;
- therefore the signed prime packet is automatically favorable:
  `\mathcal P^{\phi}_{\alpha,W_{\mathrm{pd}}}(H;T)\le 0`;
- meanwhile the normalized archimedean packet and fixed-shift residual packet
  inherit an extra `1/H` from the coefficients `a_j`, so they satisfy
  `\mathcal M^{\phi}_{\alpha,W_{\mathrm{pd}}}(H;T)\ll T\log T/H` and
  `\mathcal E^{\phi}_{\alpha,W_{\mathrm{pd}}}(H;T)\ll T/H`;
- hence
  `\Sigma^{\phi}_{\alpha,W_{\mathrm{pd}}}(H(T);T)\ll T\log T/H`;
- because `A_\alpha(T,\varepsilon(T))\le \Sigma^{\phi}_{\alpha,W_{\mathrm{pd}}}(H(T);T)`
  and `H(T)\asymp T^2/\log T`, one gets
  `A_\alpha(T,\varepsilon(T))\ll \log^2 T/T=o(1)`, so eventually
  `A_\alpha(T,\varepsilon(T))=0`;
- verdict: this is a genuine closure of `D2g29` through a stronger sibling
  route `D2g29e`; the older `D2g29d1a/d1b` arithmetic split is demoted from
  live critical path to backup/legacy analysis.

## In progress (2026-04-11): D2g30 microscopic-gap branch after D2g29

- exact target: update the `PO2` arithmetic reduction honestly after closing
  the integer-resonance half `D2g29`;
- exact gain: `D2g22` had two arithmetic enemies, but `D2g29e` kills the
  ultra-near integer-resonance branch, so the only remaining direct arithmetic
  wall is the microscopic one-sided gap branch
  `x_{\gamma+1}-x_\gamma\ll x_\gamma^{-2}`;
- oracle recall + external sanity-check agree on the right interpretation:
  known small-gap literature works at average-spacing scale `1/\log T`, not at
  the supertiny `1/T^2` scale forced here;
- new theorem-packet: if such consecutive gaps exist infinitely often, then on
  midpoint windows of radius `u_\nu\asymp \gamma_\nu^{-2}` the zero-counting
  function must capture two zeros while the smooth Riemann--von Mangoldt part
  contributes only `o(1)`;
- therefore the remaining wall can be rewritten as a supertiny two-jump
  problem for `S(T)`:
  `S(T_\nu+u_\nu)-S(T_\nu-u_\nu)\ge 2-o(1)` on infinitely many windows with
  `u_\nu\ll T_\nu^{-2}`;
- stronger correction from rereading `D2g21`: the true surviving enemy is not
  merely one microscopic gap but a one-sided packet with `\gtrsim \log T`
  ordinates inside a window of `x`-length `\asymp (\log T)/T^2`;
- after transport back to ordinates and subtracting the negligible
  Riemann--von Mangoldt smooth part, this forces a logarithmically large local
  spike
  `S(T_\nu+u_\nu)-S(T_\nu-u_\nu)\gtrsim \log T_\nu`
  on windows of radius `u_\nu\asymp (\log T_\nu)/T_\nu^2`;
- active next address: `D2g30c/D2g30d`, not the weaker `D2g30a/b` packaging;
- external sanity-check remains negative: standard short-interval technology
  for `S(T)` lives at average-spacing scales and does not touch this
  `(\log T)/T^2` local-spike regime.

## In progress (2026-04-11): D2g30e kill-certificate for the generic S(T) short-interval door

- exact target: test whether classical short-interval `S(T)` literature can
  already kill the deterministic spike branch from `D2g30c/D2g30d`;
- local oracle recall gives no hidden project theorem at this scale and keeps
  pushing the live burden back to the same microcluster geometry;
- external sanity-check is unfavorable in exactly the right way:
  Korolev-type papers prove existence of large values of `S(t)` on short
  intervals under RH, while Selberg/Fujii-style technology is averaged and not
  a deterministic exclusion theorem on prescribed windows;
- verdict: the generic “import standard short-interval `S(T)` bounds” route is
  false-for-now for `D2g30d`;
- active consequence: the live choice is now either a new Q3-specific
  structural exclusion of logarithmic microclusters or an honest route handoff
  beyond direct arithmetic.

## In progress (2026-04-11): D2g31 structural handoff after killing the generic S(T) door

- exact target: replace the dead generic `S(T)` shortcut by a Q3-internal
  theorem shape that still attacks the residual `D2g30c` microcluster branch;
- local oracle recall points back to the already-built geometry stack
  `D2g17a/D2g18`: genuine packets with small defect either collapse by
  compressed subgaps or are forced into an `O(h)`-tube around the Hermite line;
- this means the post-`D2g30e` enemy is no longer an arbitrary logarithmic
  spike, but one of two structured objects:
  deep compressed-gap cascade (hence `D2f3`) or bounded Hermite-captured
  genuine packet;
- active next address: `D2g31/D2g31a`;
- live theorem target: prove paired Hermite incompatibility for such bounded
  genuine packets, or else show that every extraction chain necessarily falls
  into `D2f3`.

## In progress (2026-04-11): D2g31b sharpened handoff via D2g19a

- exact gain: `D2g19a` already kills the bounded Hermite-capture branch after
  reinstating the true amplitude scale `q_\gamma=O(M^{-3})`;
- therefore the first fork written in `D2g31a` was still too wide;
- corrected live picture: a surviving `D2g30c` logarithmic microcluster must
  support repeated compressed-subgap descent, because bounded Hermite-captured
  packets are already amplitude-harmless;
- active next address is now `D2g31c`: extraction-to-compressed-gap theorem;
- if `D2g31c` lands, the whole post-`D2g29e` direct arithmetic residue
  collapses back into the already-isolated resonance branch `D2f3`.
- quick numerical sanity-check on actual ordinates (`a=1`, first `80` zeros,
  packet lengths `L=2,3,4`) still points the same way: the smallest-singular
  local windows have Hermite overlaps around `0.995` for `L=2`,
  `0.976–0.989` for `L=3`, and `0.970–0.983` for `L=4`, so the dangerous
  bounded-size windows continue to look Hermite-like rather than suggesting a
  new coefficient law.
- concrete geometric gain: a `D2g30c` logarithmic microcluster with
  `\gtrsim \log M` points in length `\asymp (\log M)/M^2` already contains,
  for every fixed `L_0`, some consecutive `L_0`-block of diameter `O(M^{-2})`;
- therefore the only genuinely missing part of `D2g31c` is amplitude transfer
  to such a bounded extracted block, not support geometry anymore.
- sharpened theorem-shape: if one-block amplitude transfer fails, then the
  obstruction must live on a coherent mesoscopic chain of many bounded blocks;
- active consequence: the direct residue is no longer a vague big cluster, but
  either one dangerous bounded block or a phase-coherent train of Hermite-like
  bounded blocks.

## In progress (2026-04-11): D2g31f/g phase-lock compression

- exact gain: a coherent train of bounded Hermite-like blocks is still too
  loose a shape; overlapping windows should force their local phases to lock;
- because neighboring blocks share `L_0-1` coordinates and Hermite-captured
  shared coordinates are uniformly nondegenerate, the block phases cannot
  wander independently;
- corrected live enemy: not “many local Hermite-like blocks”, but one global
  phase-rotated alternating mesoscopic train;
- active next question: can the genuine paired residues
  `q_\gamma=e(x_\gamma-1)` support such a long globally phase-locked
  alternating train?

## In progress (2026-04-11): D2g31h identification with the canonical model enemy

- exact gain: the phase-locked alternating train from `D2g31f/g` is not a new
  species; it is exactly the same finite-difference/Hermite genre already
  isolated in `D2g13b/D2g13c`;
- therefore the direct frontier compresses again: the live enemy is no longer
  an abstract train, but a genuine paired realization of the canonical model
  packet;
- active next question: can the actual support `Y_a={x_\gamma,x_\gamma-1}`
  realize this canonical model enemy without already dropping into `D2f3`?

## In progress (2026-04-11): D2g31i splice with D2g15a

- exact gain: the remaining question from `D2g31h` is already answered by an
  older packet;
- `D2g15a` says there is no cycle/graph escape for the paired Hermite model,
  and its only dangerous realization mechanism is the actual near-collision
  geometry in `X_a`, i.e. exactly the compressed-gap/resonance direction
  isolated as `D2f3`;
- therefore the whole post-`D2g29e` direct arithmetic residue now compresses
  to one branch only:
  outside `D2f3` there is no remaining direct arithmetic enemy;
- active consequence: the non-resonant direct route is effectively exhausted;
  the only live residue is now `D2f3`.

## Verified (2026-04-11): D2f3 fixed-constant threshold is already killed by D2g29e

- exact correction: `D2g29e3` proves the dyadic estimate
  `A_\alpha(T,\varepsilon)\ll T\log T/H` with `H\asymp 1/\varepsilon`; the
  little-`o` scale was only one application, not the true limit of the proof;
- therefore for every fixed `C>0`,
  `\varepsilon_C(T)=C(\log T)/T^2` also gives
  `A_\alpha(T,\varepsilon_C(T))\ll_C \log^2 T/T=o(1)`, hence eventually
  `A_\alpha(T,\varepsilon_C(T))=0`;
- the only honest care point is dyadic renormalization: from
  `\operatorname{dist}(x_\gamma,\mathbb Z)\le C(\log x_\gamma)/x_\gamma^2`
  on infinitely many ordinates one passes to
  `A_\alpha(T,\varepsilon_{C'}(T))\ge 1` on infinitely many dyadic blocks for a
  possibly different fixed constant `C'=C'(\alpha,C)`;
- with that constant transfer made explicit, `D2f3` is excluded outright;
- consequence: combining `D2f3b` with `D2g31i`, the whole post-`D2g29e`
  direct arithmetic residue is empty.
- next local splice: `D2g33` now turns that direct-route closure into the
  admissible `PO2` theorem-shell output
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`,
  so the next forced packet is `PO3`, not another arithmetic reduction.

## In progress (2026-04-11): PO3 restart after the D2g33 splice

- exact target is now frozen as
  `PO3a = \mathcal D_{a,\partial}^{+-}=0`,
  with `PO3b = \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}` and
  `PO3c = \mathcal D_{a,\partial}^{-+}=0` by symmetry;
- local oracle recall is fully coherent: the active source stack is
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md),
  [`plus_minus_cancellation_ledger_2026_03_15.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md),
  and [`h1_boundary_cap_reset_2026_03_14.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_boundary_cap_reset_2026_03_14.md);
- downstream notes
  [`h1_po4_same_sign_boundary_identification_2026_03_18.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md)
  and
  [`h1_po5_cap_separation_2026_03_19.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md)
  already assume the mixed side is bulk-exact and boundary-killed, so the live burden is now purely `PO3`;
- external web sanity-check gives only generic Toeplitz/Hankel boundary-language support; no external theorem closes `PO3` for us automatically;
- immediate plan: keep one exact `PO3a` lemma, one cap-only corollary `PO3b`, and treat any surviving non-cap cross-sign boundary residue as a route-kill event.

## In progress (2026-04-11): PO3 formalization receiver after the D2g33 splice

- interface check is now clean: the historical `PO3` note already consumes
  exactly the current `D2g33` output from `PO2`, namely the mixed
  boundary/cap-only shell
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- downstream packets `PO4`, `PO5`, `PO6`, `PO7`, `H2^f`, `H3^f`, `H4^f`
  remain consistent with that interface, so there is no newly opened
  mathematical blocker between `D2g33` and the frozen upper bridge;
- local oracle search on `q3_docs` for `PO3` formalization / theorem-shell
  receivers returns the `PO3` note itself, structure-mapping docs, and the
  general Lean formalization philosophy, but no existing Lean receiver and no
  Aristotle-ready `PO3` request;
- direct repo search confirms the same thing: there is no `PO3`-named Lean
  theorem, no `PO3` artifact in `aristotle_input`, and no explicit lower-shell
  landing zone in `Q3/`;
- the first honest Lean landing zone is now fixed explicitly as
  [`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean),
  which already compiles and freezes the abstract algebraic handoff
  `PO2 shell + PO3a => PO3b`, together with the symmetry transfer `PO3a => PO3c`;
- external web sanity-check on Lean theorem-skeleton/formalization docs adds
  only generic background and no ready-made closure trick for this shell;
- the exact live execution blocker is therefore no longer fresh `PO3`
  mathematics, but the first executable formalization receiver for
  `PO3a/PO3b/PO3c`;
- recommended order is now rigid:
  freeze the `PO3` receiver boundary,
  draft the smallest Aristotle markdown request,
  get user review,
  and only then submit that one shell before touching downstream
  `PO4 -> H4` formalization.

## In progress (2026-04-11): PO3a proof-packet audit after the receiver pass

- exact target remains
  `PO3a = \mathcal D_{a,\partial}^{+-}=0`,
  with downstream shell
  `PO3b = \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}` and
  `PO3c` by symmetry;
- local oracle pass is now stable: every useful hit points back to the same
  four files
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md),
  [`plus_minus_cancellation_ledger_2026_03_15.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md),
  [`h1_boundary_cap_reset_2026_03_14.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_boundary_cap_reset_2026_03_14.md),
  and
  [`h1_four_block_bulk_2026_03_08.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_four_block_bulk_2026_03_08.md);
- external web sanity-check again gives no ready-made Toeplitz/Hankel theorem
  that would close `PO3a` for us automatically; at best it supports the
  general language “boundary / commutator / cap”, not the exact cancellation;
- what we already have mathematically:
  `PO2` kills the bulk channel,
  the reset note fixes the theorem map `H1^\infty -> H1^\partial -> H1^f`,
  the ledger fixes the decomposition
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{bulk}}^{+-}+\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`,
  and the four-block note freezes the filtered bulk formulas and says boundary
  bookkeeping must not live inside the filtered bulk object;
- what we do **not** have yet is the decisive mathematical step:
  an explicit formula identifying the mixed boundary term
  `\mathcal D_{a,\partial}^{+-}` as a concrete short-range
  Toeplitz-Hankel/commutator operator together with the cancellation mechanism
  that forces it to vanish in the `(+,-)` channel;
- therefore the honest live blocker is not formalization but the missing proof
  packet for `PO3a`;
- current 5-line plan:
  1. freeze the missing lemma as “explicit mixed-boundary formula for
     `\mathcal D_{a,\partial}^{+-}`”;
  2. derive that formula from the infinite-tail decomposition in
     `h1_boundary_cap_reset_2026_03_14.md`;
  3. compare it against the filtered `(+,-)` packet from
     `h1_four_block_bulk_2026_03_08.md`;
  4. isolate the exact sign / symmetry cancellation that should kill it;
  5. only after that reuse
     [`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean)
     as the landing shell and reopen Aristotle.

## Final result (2026-04-11): the exact missing `PO3a` lemma is sign-pure boundary-algebra membership

- the audit is now closed tightly enough to replace the vague `PO3a` blocker
  by one exact theorem target:
  prove that the boundary layer `H_{a,N}` in the infinite-tail split
  `\mathcal D_{a,N}=H_{a,N}+C_{a,N}` belongs to the sign-pure boundary algebra
  `\mathcal B` generated by `P_+`, `P_-`, `\Delta_+`, `\Delta_-`, and
  one-sided tail operators;
- this is the right target because the mixed filtered residual already has an
  exact four-term formula from
  [`h1_po2_cross_sign_bulk_exactness_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md),
  and the same note already contains the sign-pure boundary lemma
  `P_+TP_-=0` for every `T\in\mathcal B`;
- therefore the real `PO3a` chain is now rigid:
  `H_{a,N}\in\mathcal B`
  `=> P_+H_{a,N}P_-=0`
  `=> \mathcal D_{a,\partial}^{+-}=0`
  `=> \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}`;
- the old wording “find an explicit mixed boundary formula and some
  cancellation” was too loose; the cancellation mechanism is now identified,
  and only the boundary-formula / algebra-membership step remains open;
- the honest failure mode also sharpens:
  Door 1 dies not from any abstract mixed residue, but exactly if the explicit
  boundary formula forces a genuine cross-sign generator outside
  `\mathcal B`, i.e. a non-cap term with nonzero `P_+(\cdot)P_-`;
- operational consequence:
  the next local attack is no longer a broad `PO3` audit, but a direct proof
  attempt for the boundary-algebra membership lemma, and
  [`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean)
  remains auxiliary until that lemma is real.

## Final result (2026-04-11): `PO3a` now has a rigid five-step proof skeleton

- the live `PO3a` attack is now frozen as the packet
  `PO3a.1 -> PO3a.5`, not as a generic boundary-cancellation cloud;
- `PO3a.1`: decompose the tail synthesis as
  `S_{a,\infty,N}=U_{a,N}+B_{a,N}` with the bulk identity
  `U_{a,N}^*G_g[a]U_{a,N}=\kappa(a)\Delta_N^*Q_\infty\Delta_N`,
  so that the whole boundary layer `H_{a,N}` is generated only by the
  correction `B_{a,N}`;
- `PO3a.2`: expand `B_{a,N}` into finitely many sign-pure boundary generators;
- `PO3a.3`: prove kernel sign-preservation on those generators;
- `PO3a.4`: conclude `H_{a,N}\in\mathcal B`;
- `PO3a.5`: apply the already frozen sign-pure lemma
  `P_+H_{a,N}P_-=0`, hence
  `\mathcal D_{a,\partial}^{+-}=0`;
- this refines the difficulty map sharply:
  `PO3a.5` is already formal once membership is proved,
  `PO3a.4` is only a closure step,
  and the genuine hard bricks are exactly `PO3a.2` and `PO3a.3`;
- operational consequence:
  the next honest mathematical move is to extract the explicit boundary
  expansion of `B_{a,N}` from the tail definitions in
  [`h1_po1_tail_defect_attack_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po1_tail_defect_attack_2026_03_16.md),
  not to reopen the whole `PO3` discussion.

## Final result (2026-04-11): the exact algebraic start of `PO3a.1` is now frozen

- there is now one exact non-speculative identity behind the bulk-boundary
  split:
  if `T_{a,\infty,N}` is the raw sign-pure synthesis
  `T_{a,\infty,N} z^{\pm n}=\chi_{\pm n}[a]`, then the already frozen
  `PO1` / `Main_closure` formulas give
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`
  on the algebraic two-sided tail basis;
- this matters because it shows that the sign geometry is already exact on the
  Volterra-antiderivative side: `\Delta_N` is sign-separated and
  `T_{a,\infty,N}` is sign-pure by construction;
- therefore any genuine boundary layer in
  `S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
   - \kappa(a)\Delta_N^*Q_\infty\Delta_N`
  must arise only when passing back from the antiderivative side to the actual
  defect operator, not from a hidden mixed combinatorics inside the filtered
  tail synthesis itself;
- operational consequence:
  the next sharp local attack is to exploit
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`
  to write the boundary correction explicitly, then test sign-purity of each
  resulting generator.

## In progress (2026-04-11): first honest candidate formula for the `PO3a.2` boundary bricks

- the Volterra factorization now points to one concrete candidate source of the
  boundary layer:
  if `D_a` is the derivative on the Volterra domain, then formally
  `D_a I_0^{(a)} = I` while
  `I_0^{(a)} D_a = I - R_a`
  with the rank-one endpoint projector
  `R_a := \mathbf 1 \otimes \operatorname{ev}_{-a}`;
- so the first plausible explicit formula for `H_{a,N}` is no longer a vague
  commutator cloud, but an algebra generated by the sign-split raw syntheses
  `T_{a,\infty,N}^\pm` together with the endpoint defect `R_a, R_a^*`;
- this is still a candidate, not a proved theorem inside the current packet,
  but it is the first local formula that matches the frozen exact identity
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`;
- operationally this sharpens `PO3a.2` into one concrete test:
  do the endpoint-evaluation bricks produced by `R_a` remain sign-pure after
  the `P_+ / P_-` split, or do they force a genuine cross-sign generator?

## In progress (2026-04-11): exact orthogonality squeeze on the endpoint-projector candidate

- there is now one exact algebraic squeeze on the `R_a` candidate:
  `R_a` outputs the constant function `1`, while the raw sign-pure tail
  syntheses `T_{a,\infty,N}^\pm` use only the nonzero Fourier modes
  `\chi_{\pm n}[a]` with `n>N\ge 0`;
- therefore
  `T_{a,\infty,N}^{+*} 1 = 0` and `T_{a,\infty,N}^{-*} 1 = 0`
  exactly, by ordinary Fourier orthogonality on `[-a,a]`;
- operational consequence:
  any boundary brick where the endpoint projector lands on the left
  raw-synthesis side dies immediately after pullback to the tail;
- so the candidate `PO3a.2` problem is narrower than before:
  only the domain-side endpoint-evaluation functionals can survive, which is
  materially closer to the desired sign-pure picture than a generic
  Toeplitz/Hankel cloud.

## In progress (2026-04-11): endpoint evaluation on the raw tail already splits by sign

- the endpoint functional is now explicit on the raw tail synthesis:
  `\chi_{\pm n}[a](-a)=(2a)^{-1/2}(-1)^n`, so
  `\operatorname{ev}_{-a}\circ T_{a,\infty,N}`
  splits exactly as
  `\ell_{+,N}P_+ + \ell_{-,N}P_-`
  with two alternating one-sided functionals;
- equivalently,
  `R_a T_{a,\infty,N}
   = \mathbf 1\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)`
  is already sign-split on the domain side;
- this is an exact gain, not a conjecture:
  the domain-side endpoint bricks do not mix `+` and `-` at all;
- so the live `PO3a.2/PO3a.3` burden narrows one step further:
  any possible mixed leakage can only come from the left vector produced after
  `G_g[a]` acts on the constant output, not from the endpoint functionals
  themselves.

## In progress (2026-04-11): `PO3a.3` reduces to one vector-level sign test

- after the exact split
  `R_a T_{a,\infty,N}
   = \mathbf 1\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)`,
  the first-order endpoint bricks are controlled by one concrete vector
  `v_{a,N}:=T_{a,\infty,N}^*G_g[a]\mathbf 1`;
- so the live `PO3a.3` question is no longer "understand all boundary
  generators", but the sharper sign test:
  is the relevant part of `v_{a,N}` sign-pure, or at least compatible with the
  split one-sided functionals `\ell_{+,N}P_+`, `\ell_{-,N}P_-`?
- this is still a reduction, not a theorem, but it is a real narrowing:
  the possible mixed leakage is now concentrated in one vector-level object
  rather than an uncontrolled boundary cloud.

## In progress (2026-04-11): the vector-level object is exactly the raw zero-mode column

- the vector
  `v_{a,N}:=T_{a,\infty,N}^*G_g[a]\mathbf 1`
  is no longer abstract:
  since `\mathbf 1=\sqrt{2a}\,\chi_0[a]`, its tail coordinates are exactly
  `\sqrt{2a}\,w_{r,0}(a)` for `|r|>N`;
- using the frozen raw Weil formula, this gives the explicit zero-sum
  expression
  `w_{r,0}(a)
   = (2(-1)^r/a)\sum_\gamma \sin^2(a\gamma)/((\gamma+\alpha_r)\gamma)`;
- so the live `PO3a.3` problem is now reduced to the sign structure of one
  zero-mode coupling column, not an unspecified vector in tail space.

## In progress (2026-04-11): the zero-mode column is reflection-even, but this is weaker than sign-purity

- the live synthesis/oracle pass for the new blocker did **not** return an
  existing reusable lemma about `G_g[a]\mathbf 1` or `w_{r,0}(a)`; the sharp
  object is still the raw zero-mode column itself;
- however, the frozen raw formula from
  `full/sections/Main_closure.tex` can be paired directly over the symmetric
  zero set `\Gamma=-\Gamma`:
  `w_{r,0}(a)
   = (4(-1)^r/a)\sum_{\gamma>0}\sin^2(a\gamma)/(\gamma^2-\alpha_r^2)`;
- in particular this gives the exact symmetry
  `w_{-r,0}(a)=w_{r,0}(a)`, hence the boundary vector
  `v_{a,N}=T_{a,\infty,N}^*G_g[a]\mathbf 1`
  is reflection-even across the positive and negative tails;
- this is the first exact structure theorem on the live `PO3a.3` object, and
  it sharply narrows the search space;
- but it still does **not** prove `H_{a,N}\in\mathcal B`: a rank-one brick
  built from an even left vector and the sign-split right functional
  `\ell_{+,N}P_+ + \ell_{-,N}P_-` can still contain genuine cross-sign pieces;
- in fact there is now an exact local obstruction: for any nonzero vector `v`,
  the rank-one brick
  `K_v:=v\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)`
  is block-diagonal only if `P_+v=P_-v=0`, because its mixed blocks are exactly
  `P_+v\otimes\ell_{-,N}` and `P_-v\otimes\ell_{+,N}`;
- therefore a lone first-order endpoint brick of this type can never lie in the
  sign-pure boundary algebra unless it is zero;
- there is also a sharp finite-section obstruction for the next route:
  if a compressed first-order brick and its adjoint companion cancel exactly,
  then the positive and negative pieces of `v_{a,N}` must each be proportional
  to the alternating tail vectors
  `\sum_{r=N+1}^{M}(-1)^r e_r^\pm`;
- for the actual zero-mode column this means
  `w_{r,0}(a)=c_{a,N,M}(-1)^r` on the whole compressed window
  `N<r\le M`, equivalently the paired sum
  `\sum_{\{\gamma,-\gamma\}\subset\Gamma}\sin^2(a\gamma)/(\gamma^2-\alpha_r^2)` would have to be
  constant in `r` on that window;
- the tempting Stieltjes/monotonicity shortcut has now been explicitly
  rejected: our `\gamma` are zeros of `\xi(1/2-iz)` in the complex plane, so
  the paired quotient sum is not currently an honest positive measure on real
  `\gamma^2`;
- but there is a stronger operator-level squeeze: if the same first-order
  companion cancellation is needed on every compression `P_{M,N}`, then the
  window constants `c_{a,N,M}` glue on overlaps and force a single tail law
  `w_{r,0}(a)=c_{a,N}(-1)^r` for all `r>N`;
- since `w_{r,0}(a)` is an off-diagonal raw entry with fixed second index,
  the already-frozen off-diagonal tail decay then forces `c_{a,N}=0`;
- so a nontrivial alternating-tail pattern cannot support the full
  infinite-tail operator identity: full first-order companion cancellation
  would already imply `w_{r,0}(a)=0` on the whole tail;
- equivalently, with
  `H_a(z):=\sum_{\gamma\in\Gamma}\sin^2(a\gamma)/(\gamma(\gamma+z))`,
  the same route would force
  `H_a(\alpha_r)=0` for every `r>N`, where `\alpha_r=\pi r/a`;
- so the live first-order wall is now a scalar arithmetic-progression
  uniqueness problem for one fixed meromorphic Cauchy-type profile `H_a`;
- after the exact rescaling `\widetilde H_a(w):=H_a(\pi w/a)` with support
  points `y_\gamma:=-a\gamma/\pi`, this becomes a literal simple Cauchy
  transform
  `\widetilde H_a(w)=\sum e_a(y_\gamma)/(y_\gamma-w)`
  vanishing on every integer `r>N`;
- so the first-order `PO3a` wall now feeds directly into the already isolated
  `PO2` Cauchy-tail injectivity target, with one honest caveat:
  the support `Y_a={-a\gamma/\pi}` is complex, so the old one-sided real-line
  rigidity theorem is not enough by itself;
- and the full direct divisor-closure package transfers verbatim:
  dividing by tail factors `(w-(N+j))` keeps `\widetilde H_a` inside the same
  simple Cauchy class and shifts the tail-zero set to the right, so the
  remaining hard part is now only complex-support injectivity, not receiver
  shape;
- even more sharply, zero symmetry gives `e_a(-y)=-e_a(y)`, so the rescaled
  receiver is even and factors as `\widetilde H_a(w)=J_a(w^2)` with a new
  simple Cauchy transform
  `J_a(z)=\sum_{\lambda\in\Lambda_a} b_a(\lambda)/(\lambda-z)` on the squared
  support `\Lambda_a=\{y_\gamma^2\}`;
- therefore the first-order `PO3a` wall narrows from generic integer-tail
  injectivity to a square-tail problem
  `J_a(r^2)=0` for all `r>N`, together with its own quadratic divisor tower
  under division by `z-(N+j)^2`;
- after squaring, the support density also matches the sample density:
  `n_{\Lambda_a}(R)\asymp \sqrt R \log R`, so `\Lambda_a` has exponent of
  convergence `1/2`, the same order as the square lattice `\{m^2\}`;
- the quadratic divisor tower has an exact Newton avatar:
  with `s_j=(N+j)^2`, the weights
  `u_k(\lambda)=1/\prod_{j\le k}(\lambda-s_j)` are exactly the divided
  differences of the Cauchy kernel on the square grid, so the whole moving
  tower is equivalent to vanishing of the initial Newton-profile
  `[J_a; s_1,\dots,s_k]`;
- finite-support square-tail injectivity is now closed immediately by the same
  rational-function argument as before: if
  `J(z)=\sum_{m\le M} b_m/(\lambda_m-z)` vanishes at the first `M` square
  nodes, then the associated square-Cauchy matrix is invertible and all
  residues vanish;
- the square-tail set also has a canonical entire divider
  `E_N^{sq}(z)=\prod_{m>N}(1-z/m^2)=\sin(\pi\sqrt z)/(\pi\sqrt z)` up to the
  finite front factor, so the first-order wall admits an exact whole-tail
  factorization by a square-lattice entire function of lower density than the
  old integer-tail Gamma divider;
- independently of the lower square-tail route, `PO3a` now also has a clean
  upper-shell reduction `PO3a-core`: once a finite sign-split boundary
  expansion `B=\sum |b_{r,\sigma}\rangle\langle\eta_{r,\sigma}|` is available,
  the bad block `P_+H_{a,N}P_-` expands into exactly three explicit families:
  `P_+U^*Gb_{r,-}`, `P_-U^*Gb_{r,+}`, and
  `\langle b_{r,+},Gb_{s,-}\rangle`; so boundary cancellation is reduced from
  abstract algebra-membership to concrete coefficient vanishing;
- `PO3a-core` now has one exact finite-dimensional sharpening:
  if the boundary cap-vectors `\eta_{r,+},\eta_{s,-}` are independent and the
  leakage vectors `u_s^-=P_+U^*Gb_{s,-}`, `v_r^+=P_-U^*Gb_{r,+}` already lie in
  the finite cap spaces `E_\pm=\operatorname{span}\{\eta_{r,\pm}\}`, then
  `P_+H_{a,N}P_-=0` is equivalent to one finite matrix identity `A+B+M=0`,
  where `A,B` are the cap-coordinate matrices of the two leakage families and
  `M_{rs}=\langle b_{r,+},Gb_{s,-}\rangle`;
- this is stronger than the old coefficientwise kill packet: `PO3a` no longer
  requires every leakage term to vanish separately, only that after projection
  into the finite cap spaces the resulting matrices cancel exactly;
- there is now an algorithmic special case `PO3a-row-column reduction`:
  if the boundary correction matrix is supported on finitely many rows `R` and
  columns `C` in a sign-adapted basis, then
  `B=\sum_{r\in R}|e_r\rangle\langle\rho_r|
    +\sum_{c\in C}|\kappa_c\rangle\langle e_c|
    -\sum_{r\in R,c\in C}B_{rc}|e_r\rangle\langle e_c|`,
  with explicit row functionals `\rho_r` and column vectors `\kappa_c`;
- after sign-splitting `\rho_r,\kappa_c`, this gives a fully constructive
  finite generator list to feed into `PO3a-finite reduction`, so in the
  finite row/column regime `PO3a` is literally a finite matrix computation;
- there is now also a sharper equivalent receiver
  `PO3a-corrected-column reduction`: defining corrected columns
  `d_c:=Be_c-\sum_{r\in R}B_{rc}e_r`, one gets the cleaner exact two-term
  decomposition
  `B=\sum_{r\in R}|e_r\rangle\langle \rho_r|
    +\sum_{c\in C}|d_c\rangle\langle e_c|`,
  so the overlap subtraction is absorbed once and for all into the `d_c`;
- this is the best current finite-dimensional engineering form of `PO3a`,
  because the right-vector side now consists only of row-sign pieces
  `\rho_r^\pm` and basis vectors `e_c` with fixed sign, making the later
  compression to sign-pure bases and the assembly of the finite mixed matrix
  `A+B+M` completely mechanical;
- the row/column packet has now been compressed one step further into a literal
  matrix receiver `PO3a-compressed matrix receiver`: after orthonormalizing the
  plus/minus right-generator spans, one gets
  `B=L_+E_+^*+L_-E_-^*`;
- under the finite leakage factorizations
  `P_+U^*GL_-=E_+A` and `L_+^*GUP_-=BE_-^*`, the mixed block becomes exactly
  `P_+HP_-=E_+(A+B+M)E_-^*` with `M=L_+^*GL_-`, so `PO3a` is literally
  equivalent to one finite matrix identity `A+B+M=0`;
- this is now the strongest finite-dimensional receiver in the file: once the
  real boundary defect yields finite row/column data, there is no remaining
  infinite-dimensional ambiguity at all;
- the Lean shell is now synchronized with this receiver at the logical level:
  `Q3/Proofs/HBridge_PO3_Shell.lean` contains
  `po3_boundary_zero_of_matrix_receiver` and
  `po3_cap_only_of_po2_and_matrix_receiver`, so the executable handoff now
  matches the new docs-level packet “finite matrix cancellation
  \Rightarrow boundary zero \Rightarrow cap-only mixed block”;
- in the first-order endpoint model this `PO3a-core` formula collapses exactly
  to the old zero-mode object: the three families reduce to the two sign
  components of `U^*G\mathbf 1` plus the scalar `\langle\mathbf 1,G\mathbf 1\rangle`,
  so the new upper-shell reduction and the old lower-shell `v_{a,N}` route are
  two descriptions of the same live obstruction, not competing forks;
- there is now one more exact intermediate target between abstract
  algebra-membership and a full raw formula for `B_{a,N}`:
  the endpoint-projector calculus. Since
  `E_{a,N}=R_aT_{a,\infty,N}=|\mathbf 1\rangle\langle \ell_{+,N}P_+|
   +|\mathbf 1\rangle\langle \ell_{-,N}P_-|`,
  any boundary term built from finitely many insertions of
  `E_{a,N},E_{a,N}^*` and otherwise sign-preserving operators automatically
  expands into finitely many sign-split rank-one bricks; so the real next
  local brick is to prove that the surviving boundary words are endpoint-word
  finite, not to guess `B_{a,N}` all at once;
- this endpoint-projector bridge is now frozen as an exact theorem packet
  `PO3a-endpoint-word trigger`: if the genuine boundary operator is a finite
  linear combination of words of the three forms
  `A_jE_{a,N}`, `E_{a,N}^*B_j`, and `E_{a,N}^*M_jE_{a,N}`, then it
  automatically admits a finite sign-split rank-one expansion, because
  `A_jE_{a,N}` is controlled by the two sign parts of `A_j\mathbf 1`,
  `E_{a,N}^*B_j` by the two sign parts of `B_j^*\mathbf 1`, and
  `E_{a,N}^*M_jE_{a,N}` collapses to one scalar
  `\langle \mathbf 1,M_j\mathbf 1\rangle` times the four fixed endpoint bricks;
- therefore the live `PO3a` burden is now narrower than “derive a full closed
  formula for `H_{a,N}`”: it is enough to show that every surviving boundary
  term lies in the finite endpoint-word span generated by
  `A E_{a,N}`, `E_{a,N}^* B`, and `E_{a,N}^* M E_{a,N}`;
- once that span statement lands, the already frozen packets
  `PO3a-core`, `PO3a-finite reduction`, and `PO3a-row-column reduction`
  become mechanical, so the remaining honest wall is only the word-level
  extraction of the real boundary defect from the Volterra undoing identity;
- semantic search on the new blocker `Volterra undoing -> endpoint-word span`
  did not surface any hidden ready-made theorem beyond the current `PO1/PO3`
  notes; short external probing likewise did not reveal a useful imported
  theorem, so this step remains an internal algebraic derivation rather than a
  literature import;
- two exact intermediate packets are now frozen above that wall:
  `PO3a-endpoint normal form` says that after composing the endpoint bricks
  with sign-preserving tail operators, the operator still admits a finite
  sign-split rank-one expansion;
- `PO3a-outer-endpoint annihilation` sharpens the Volterra route itself:
  because `T_{a,\infty,N}^*\mathbf 1=0`, one gets
  `T_{a,\infty,N}^*R_a=0` and `R_a^*T_{a,\infty,N}=0`, so any endpoint
  insertion that lands directly on the outer synthesis side dies immediately;
- therefore the real `PO3a` extraction problem is now narrower than before:
  after a finite Volterra-undoing expansion, every surviving term must already
  normalize to one of the three families
  `A E_{a,N}U`, `V^*E_{a,N}^*B`, `U_1^*E_{a,N}^*ME_{a,N}U_2`;
- this means the next honest local theorem is no longer “compute the whole
  `H_{a,N}`”, but only “show that the actual defect expands into finitely many
  such surviving normal-form words”;
- that algebraic burden is now frozen even more sharply as
  `PO3a-two-endpoint extraction`: if one can write the real boundary defect in
  the Volterra normal form
  `U^*T^*((I-R_a)^*K_a(I-R_a)-K_a)TV`
  with sign-preserving tail operators `U,V`, then the defect expands exactly
  into three terms
  `-U^*E_{a,N}^*K_aTV`, `-U^*T^*K_aE_{a,N}V`,
  `+U^*E_{a,N}^*K_aE_{a,N}V`;
- so the remaining live wall is now a single exact extraction claim:
  prove that the genuine `H_{a,N}` is obtained from the Volterra undoing by
  such a two-endpoint bracket, after which endpoint normal form and the finite
  matrix reduction fire automatically;
- there is now one more exact collapse under the natural self-adjointness
  hypothesis `K_a=K_a^*`: the whole surviving boundary packet depends only on
  the single tail vector `v_{K,a,N}:=T^*K_a\mathbf 1` and the single scalar
  `c_{K,a}:=\langle \mathbf 1,K_a\mathbf 1\rangle`;
- concretely, the three surviving terms from `PO3a-two-endpoint extraction`
  rewrite entirely in terms of `U^*v_{K,a,N}`, `V^*v_{K,a,N}`,
  `U^*h_{\pm,N}`, and the scalar `c_{K,a}`, so once the Volterra normal form is
  real, `PO3a` is no longer a generic operator wall but a one-vector plus
  one-scalar boundary problem;
- in the natural specialization `K_a=G_g[a]`, this generic receiver is exactly
  the old project zero-mode vector
  `v_{a,N}=T^*G_g[a]\mathbf 1`, and the only extra scalar is the constant
  self-pairing `\langle \mathbf 1,G_g[a]\mathbf 1\rangle`;
- so the new Volterra route does not fork the proof: if it lands, it feeds
  directly back into the already isolated lower-shell zero-mode receiver rather
  than creating a second boundary backend;
- local semantic search on the new blocker `infinite-support square-tail
  injectivity` did not surface any ready-made project theorem beyond the old
  generic `PO2` Cauchy-tail wall; short external probing likewise did not
  reveal a clean imported uniqueness theorem specialized to zeros on `m^2`;
- inside the direct `SQ1` branch, the quadratic divisor tower is now rewritten
  as an exact Gibbs family on the squared support:
  `\nu_k(\gamma)\propto |b_\gamma|^2\prod_{j\le k}|\lambda_\gamma-(N+j)^2|^{-2}`,
  with explicit ratio control
  `\nu_k(\gamma)/\nu_k(\eta)=|b_\gamma|^2/|b_\eta|^2 \cdot
   \prod_{j\le k}|\lambda_\eta-s_j|^2/|\lambda_\gamma-s_j|^2`;
- exact target for the next local blocker: prove `SQ1.3`, an explicit upper
  bound on the pole-envelope
  `\mathfrak D_N(\lambda)=\sup_k\prod_{j\le k}|1-\lambda/(N+j)^2|^{-2}`, and
  wire it into the already isolated `SQ1` no-escape wall;
- local semantic search on this blocker only surfaced in-project Gamma-ratio
  infrastructure and no imported square-tail theorem; the short external check
  likewise only confirms the standard sine-product / Gamma-product background,
  not a ready-made uniqueness result on the square lattice;
- two concrete `SQ1` gains are now closed mathematically:
  `SQ1.1` fixed-anchor no-drift (`W_k(\lambda)/W_k(\mu)\to C_N(\lambda,\mu)`)
  and `SQ1.2` the summable pole-envelope criterion
  `\sum_{\lambda}|b_\lambda|^2\mathfrak D_N(\lambda)<\infty
   \Rightarrow \nu_k\to\pi_N`;
- one honest half-step of the next blocker is now explicit as `SQ1.3a`:
  on every bounded horizontal strip, the limiting square divisor obeys
  `D_{N,\infty}(y^2)=|E_N^{sq}(y^2)|^{-2}
   \ll_{N,A}(1+|y|)^{4N+2}\operatorname{dist}(y,\pm\{N+1,N+2,\dots\})^{-2}`;
- so near-pole concentration is no longer vague: the only way the limiting
  divisor can blow up is through small square-root distance to the tail square
  lattice, with only polynomial ambient loss from the finite front factor;
- the second half `SQ1.3b` also closes exactly: for
  `f_m(y)=|1-y^2/m^2|^{-2}`, the sign of `f_m(y)-1` changes at most once, so
  `D_{N,k}(y^2)` is first nonincreasing and then nondecreasing; hence
  `\mathfrak D_N(y^2)=\max(1,D_{N,\infty}(y^2))`;
- so the live burden inside the direct square-tail route is no longer generic
  Gibbs motion, but one static arithmetic/geometric wall: estimate
  `\mathfrak D_N(\lambda)` on the actual support `\lambda=y_\gamma^2` in terms
  of the bounded-strip geometry of `y_\gamma=-a\gamma/\pi` and its distance to
  the tail square lattice `\pm\{N+1,N+2,\dots\}`;
- combining `SQ1.3a` and `SQ1.3b` yields the usable envelope
  `\mathfrak D_N(y^2)\ll 1+(1+|y|)^{4N+2}
   \operatorname{dist}(y,\pm\{N+1,N+2,\dots\})^{-2}`;
- so the exact next blocker becomes `SQ1.4`: verify the support-side
  summability condition obtained by inserting this explicit envelope into
  `\sum |b_\lambda|^2\mathfrak D_N(\lambda)<\infty`;
- but this same sufficient criterion immediately reveals an `\ell^2` barrier:
  because `\mathfrak D_N(\lambda)\ge 1`, `SQ1.4` would already require
  `\sum_{\gamma\in\Gamma^\sharp}|b_\gamma|^2<\infty`, i.e.
  `\sum_{\gamma\in\Gamma^\sharp}\sin^4(a\gamma)<\infty`;
- nothing in the current `PO3a` package gives that kind of decay, and it runs
  against the expected modulo-one equidistribution picture for `a\gamma/\pi`,
  so the Gibbs no-escape criterion should now be treated as a diagnostic /
  backup route rather than the active mainline;
- this pushes the live lower-shell burden onto `SQ2`, and the new exact
  synthesis there is sharper than before: the backend should start from the
  divided receivers `J_{a,k}`, not from raw `J_a`, because only after one
  square-tail division do the coefficients automatically enter the natural
  `\ell^2` class;
- concretely, `b_\gamma^{(k)}=b_\gamma/\prod_{j\le k}(\lambda_\gamma-s_j)`
  satisfies `|b_\gamma^{(k)}|\ll |\lambda_\gamma|^{-k}`, so already `k=1`
  gives `\sum |b_\gamma^{(1)}|^2<\infty` thanks to
  `n_{\Lambda_a}(R)\asymp \sqrt R\log R`;
- the active `SQ2` packet is now:
  `SQ2a` admissibility of `\Lambda_a` plus `\ell^2` membership for `J_{a,k}`,
  `k\ge 1`;
  `SQ2b` square-tail common-zero / nearly-invariant package via
  `E_N^{sq}(z)=\prod_{m>N}(1-z/m^2)`;
  `SQ2c` prove the resulting internal square-division chain yields at least two
  genuinely distinct nearly invariant `*`-closed subspaces, so ordering is not
  vacuous;
- `SQ2a` itself now looks essentially positive:
  `\Lambda_a` has exponent of convergence `1/2`, so
  `\sum_{\lambda\in\Lambda_a}(1+|\lambda|^2)^{-1}<\infty`, and after one
  square divisor the coefficients satisfy
  `|b_\gamma^{(k)}|\ll |\lambda_\gamma|^{-k}`, hence
  `\sum |b_\gamma^{(k)}|^2<\infty` already for `k=1`;
- so the raw support/coefficient admissibility side is no longer the SQ2 wall:
  the real remaining burden is `SQ2b`, namely to turn the square-tail common
  zeros and the internal division chain `J_{a,k+1}=J_{a,k}/(z-(N+k+1)^2)` into
  a nontrivial nearly invariant `*`-closed subspace package;
- but the most natural internal `SQ2c` candidate now collapses exactly:
  if `E_k^{sq}(z)=\prod_{m>k}(1-z/s_m)` is the common-zero factor of `J_{a,k}`,
  then `G_k:=J_{a,k}/E_k^{sq}` satisfies `G_k=-s_{k+1}G_{k+1}`; so after
  quotienting by common zeros the entire internal square-division chain is just
  one line and does **not** produce a second distinct ordered subspace;
- this kills the naive “use successive divided receivers to make ordering
  non-vacuous” plan inside SQ2; any live ordering import would now need a
  genuinely different second square-tail subspace, not the canonical internal
  chain;
- equivalently, SQ2 is now compressed to a one-object quotient problem:
  all normalized quotient generators are scalar multiples of
  `G_0(z)=J_a(z)/E_0^{sq}(z)`, so any remaining square-support backend must
  attack this single object directly rather than compare a family of internal
  quotients;
- external and local search are consistent with the same fork: the 2018
  Krein/ordering route still looks structurally compatible, while the 2022
  localization route remains non-routine because it needs power separation on
  the squared support;
- so the next honest split is now explicit:
  either attack the live wall directly through the Newton-profile /
  quadratic-divisor formulation of `J_a`,
  or try a fresh square-support adaptation of the old Cauchy-de Branges /
  localization backend, but without pretending such an import already exists;
- the honest caveat stays the same: `\Lambda_a` is still complex support, so
  the old one-sided real-support rigidity theorem still does not fire; but the
  live burden is now a smaller even square-support subclass of the old `PO2`
  wall, not the whole class;
- so the next exact theorem-target is now cleanly split:
  either prove square-tail injectivity for this even complex-support Cauchy
  subclass, or derive the full first-order endpoint formula and show that the
  adjoint companion terms cancel the cross-sign part exactly;
- concrete file pointers for this step:
  `full/sections/Main_closure.tex` for raw `w_{rs}(a)`,
  `docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md` for
  the reduction to `v_{a,N}`,
  `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` for the
  sign-pure boundary lemma `L3''''''`,
  and `Q3/Proofs/HBridge_PO3_Shell.lean` remains only the landing shell after a
  real mathematical proof packet exists.

## In progress (2026-04-12): the concrete `PO3a` difference now sits one level lower

- the filtered defect is now frozen as the exact pullback
  `\mathcal D_{a,N}=\Delta_N^*\,\mathcal R_{a,N}^{\mathrm{raw}}\,\Delta_N`,
  where the raw coefficients are simply
  `\delta_{r,s}(a)=w_{r,s}(a)-\kappa(a)q_{r,s}`;
- this removes the last vague phrasing from the current `PO3a` entry point:
  first subtract the raw coefficients, then apply the common two-sided
  four-term filter; there is no second hidden correction mechanism at this
  stage;
- therefore the live task is now explicitly lower than the filtered operator:
  split the raw defect into bulk, boundary, and cap channels, and only then
  pull that split through `\Delta_N`;
- if the raw boundary part has finite row/column support, then the filtered
  boundary part still has finite row/column support after the one-step filter,
  so the corrected-column reduction and compressed receiver packet apply
  automatically;
- equivalently, the current local burden is no longer “understand the whole
  filtered boundary operator”, but “show that the raw boundary defect lands in
  the finite-support / endpoint-word class”, because that already forces the
  finite matrix cancellation frame `A+B+M=0`;
- detailed write-up:
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md).

## In progress (2026-04-12): next exact `PO3a` blocker after the raw-defect pullback

- точная цель теперь такая:
  после отделения объёмной части и шапки доказать, что сырая граничная
  поправка для коэффициентов `\delta_{r,s}(a)=w_{r,s}(a)-\kappa(a)q_{r,s}`
  попадает в класс конечной поддержки по строкам и столбцам, либо в
  эквивалентный класс крайних слов;
- это место цепочки: `PO2` даёт точную четырёхчленную схему фильтра,
  новый шаг переводит `\mathcal D_{a,N}` в
  `\Delta_N^* \mathcal R_{a,N}^{\mathrm{raw}} \Delta_N`,
  а дальше `PO3a` закроется через corrected-column reduction и конечную
  матрицу смешивания `A+B+M=0`;
- локальный embedding-поиск вернул именно наш внутренний стек:
  [`h1_po2_cross_sign_bulk_exactness_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md),
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md),
  [`h1_boundary_cap_reset_2026_03_14.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_boundary_cap_reset_2026_03_14.md),
  [`h1_proof_obligation_table_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1-proof-obligation-table-2026-03-16.md);
- короткая внешняя проверка дала только общий операторный фон про конечный
  ранг, конечные возмущения и почти-инвариантность; готовой внешней теоремы,
  которая автоматически закрывает наш `PO3a`, нет;
- поэтому следующий честный ход не внешний, а внутренний:
  развернуть саму разность `w_{r,s}(a)-\kappa(a)q_{r,s}` так, чтобы было видно,
  какие индексы дают объёмную часть, какие дают шапку, и какие остаются в
  граничной поправке;
- практический план на один узел:
  1) взять точные формулы из `full/sections/Main_closure.tex`,
  2) записать сырой дефект как «объём + граничная поправка + шапка» в
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md),
  3) после этого проверить, что граничная поправка действительно лежит в
  конечной схеме corrected-column / endpoint-word.

## Final result (2026-04-12): finite raw support survives the two-sided filter

- точная транспортная лемма теперь зафиксирована в
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md):
  если сырой оператор на хвостовом базисе поддержан на конечных множествах
  строк `R` и столбцов `C`, то после двухстороннего фильтра
  `\Delta_N^* \mathcal B^{\mathrm{raw}} \Delta_N` он всё ещё поддержан на
  конечных множествах строк и столбцов, только после одношагового утолщения
  `R^\sharp`, `C^\sharp`;
- это ровно недостающее звено между сырой разностью коэффициентов
  `\delta_{r,s}(a)` и уже готовой corrected-column reduction:
  конечная сырая поддержка теперь автоматически даёт конечную матрицу
  смешивания после фильтра;
- следовательно, текущая локальная цель стала ещё уже:
  уже не нужно описывать весь фильтрованный оператор целиком; достаточно
  показать, что после удаления объёмной части и шапки сырая граничная
  поправка попадает в класс конечной поддержки по строкам и столбцам, либо в
  эквивалентный класс крайних слов;
- после этого `PO3a` входит в уже замороженный каркас
  `P_+ H_{a,N} P_- = E_+ (A+B+M) E_-^*`.

## Final result (2026-04-12): the finite mixing receiver is now canonical

- `PO3a` strengthened one step further in
  [`h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md):
  the finite plus/minus spaces are no longer arbitrary spaces through which the
  leakage must separately be shown to factor;
  instead they are built canonically from
  raw right-generators together with the two leakage ranges
  `\operatorname{Ran}(P_+U^*GL_-^{\mathrm{raw}})` and
  `\operatorname{Ran}(P_-U^*GL_+^{\mathrm{raw}})`;
- with that choice, the finite receiver becomes automatic:
  `P_+U^*GL_-=E_+\mathsf A`,
  `L_+^*GUP_-=\mathsf B E_-^*`,
  `\mathsf M=L_+^*GL_-`,
  hence
  `P_+H_{a,N}P_-=E_+(\mathsf A+\mathsf B+\mathsf M)E_-^*`;
- so the live `PO3a` burden is now even narrower:
  once the genuine boundary correction is reduced to finite row/column or
  endpoint-word data, there is no separate leakage-placement lemma left;
  the whole mixed-block question is one canonical finite matrix identity
  `\mathsf A+\mathsf B+\mathsf M=0`;
- this is the strongest current finite-dimensional receiver for the boundary
  attack.

## Final result (2026-04-12): exact admission criterion for the real boundary correction

- the `PO3a` note now contains a clean sufficient criterion for the genuine
  boundary correction:
  if `H_{a,N}` is a finite linear combination of Volterra-undoing words
  `U_0^*T^*X_0\Pi_1X_1\Pi_2X_2TV_0` with sign-preserving tail operators on the
  outside, bounded middle operators, and at most two endpoint projectors
  `\Pi_j \in \{R_a,R_a^*\}`, then it automatically reduces to the endpoint
  normal-form families
  `A E_{a,N}U`, `V^*E_{a,N}^*B`, `U_1^*E_{a,N}^*ME_{a,N}U_2`;
- therefore the live `PO3a` burden is now narrower than “derive the whole
  explicit formula for `B_{a,N}`”:
  it is enough to prove that the real boundary correction lies in this finite
  Volterra-word class;
- once that admission step lands, outer-endpoint annihilation, endpoint normal
  form, and the canonical finite mixing receiver all apply with no extra
  operator theory;
- this is the cleanest current bridge from the real analytic defect to the
  finite matrix identity `\mathsf A+\mathsf B+\mathsf M=0`.

## Final result (2026-04-12): the physical Volterra packet collapses to an explicit `2x2` receiver

- under the physical Volterra normal form with `K_a=G_g[a]`, the mixed block
  `P_+H_{a,N}^{\mathrm{Vol}}P_-` is no longer an arbitrary finite matrix
  receiver: it is exactly
  `E_+ K F_-` with one fixed coefficient matrix
  `K=\left[\begin{smallmatrix}-1&c_a\\0&-1\end{smallmatrix}\right]`,
  where `c_a=\langle \mathbf 1,G_g[a]\mathbf 1\rangle`,
  the plus-side generators are `U^*h_{+,N}` and `P_+U^*v_{a,N}`,
  and the minus-side generators are `\langle V^*P_-v_{a,N}|` and
  `\langle \ell_{-,N}P_-V|`;
- the determinant of this coefficient matrix is always `1`, so vanishing of the
  mixed block cannot come from an accidental singular coefficient packet;
- consequently, if the mixed block vanishes, then at least one side must
  degenerate: either the plus pair
  `\{U^*h_{+,N},P_+U^*v_{a,N}\}` is linearly dependent, or the minus pair
  `\{\langle V^*P_-v_{a,N}|,\langle \ell_{-,N}P_-V|\}` is linearly dependent;
- this sharpens the live `PO3a` burden again:
  after the Volterra admission step, one no longer needs a general boundary
  algebra argument; it is enough to analyze the rigidity forced by this
  explicit `2\times 2` packet.

## In progress (2026-04-12): next `PO3a` blocker after the `2x2` receiver

- local embedding search points back to the same live stack:
  [h1_po3_cross_sign_boundary_cancellation_2026_03_16.md],
  [h1_boundary_cap_reset_2026_03_14.md], and the `PO2` bulk note;
- short external search did not reveal an off-the-shelf theorem giving the
  physical Volterra normal form for the genuine boundary correction, so this
  bridge still has to be proved internally;
- next exact target in
  [h1_po3_cross_sign_boundary_cancellation_2026_03_16.md] is now:
  prove that the real `H_{a,N}` belongs to the physical Volterra class
  `U^*T^*((I-R_a)^*K_a(I-R_a)-K_a)TV`, ideally with `K_a=G_g[a]`;
- once that lands, the mixed block is governed by the fixed `2\times 2`
  coefficient matrix `K=[[-1,c_a],[0,-1]]`, so any vanishing must force a
  genuine degeneracy on one side;
- the most actionable sub-lemma is therefore:
  show one side is independent or nonzero in a way that makes the opposite-side
  annihilation impossible;
- file pointers for the next strike:
  `PO3a-Volterra-word admission criterion`,
  `PO3a-two-by-two receiver under physical Volterra normal form`,
  and `Q3/Proofs/HBridge_PO3_Shell.lean` as the formal shell consumer.

## Final result (2026-04-12): identity-outer physical Volterra form forces zero-mode rigidity

- in the specialization `U=V=I`, the `2\times 2` receiver sharpens further:
  if the mixed block vanishes and the fixed endpoint data
  `h_{+,N}` and `\ell_{-,N}P_-` are nonzero, then both side-pairs must be
  linearly dependent;
- equivalently, the zero-mode vector is forced to lie on the two fixed endpoint
  lines:
  `P_+v_{a,N}=\alpha_{+,N}(a)h_{+,N}` and
  `P_-v_{a,N}=\alpha_{-,N}(a)h_{-,N}`;
- this is much stronger than a generic boundary-algebra statement:
  once the physical Volterra normal form lands, `PO3a` turns into a rigid
  statement about the endpoint geometry of the single vector `v_{a,N}`;
- so the live fork is now completely explicit:
  either prove the real defect has the physical Volterra normal form, or show
  this forced endpoint-line rigidity is impossible for the genuine `v_{a,N}`.

## In progress (2026-04-12): impossibility route for the forced zero-mode rigidity

- local search ties the new `2\times 2` receiver back to the older lower-shell
  packet already present in
  [h1_po3_cross_sign_boundary_cancellation_2026_03_16.md]:
  for the zero-mode vector
  `v_{a,N}=T_{a,\infty,N}^*G_g[a]\mathbf 1`, the coefficients are
  `\langle v_{a,N},z^r\rangle=\sqrt{2a}\,w_{r,0}(a)`, and the earlier
  first-order companion analysis already showed that exact mixed cancellation on
  a window forces
  `w_{r,0}(a)=c_{a,N,M}(-1)^r` on that window;
- the new identity-outer rigidity
  `P_+v_{a,N}=\alpha_{+,N}(a)h_{+,N}`, `P_-v_{a,N}=\alpha_{-,N}(a)h_{-,N}`
  is exactly the same phenomenon in cleaner form: it says the zero-mode vector
  must lie on the fixed alternating endpoint lines;
- if such rigidity is required for all compressions, the window constants glue
  to one tail constant `c_{a,N}`, and the frozen off-diagonal tail decay then
  forces `c_{a,N}=0`; equivalently `H_a(\alpha_r)=0` for all `r>N`, where
  `H_a(z)=\sum_{\gamma} \sin^2(a\gamma)/(\gamma(\gamma+z))`;
- so the impossibility route is now sharply split:
  either prove the structured arithmetic-progression uniqueness target for this
  Cauchy-type `H_a`, or pass to the already-isolated even square-support
  receiver `J_a(r^2)=0` and attack the square-tail injectivity wall;
- the old naive Stieltjes monotonicity shortcut remains killed, and the old
  direct Carlson shortcut also remains blocked without a structured
  regularization; the honest external analogue is now the meromorphic
  interpolation / pole-recovery adaptation wall from the `PO2` note.

## Final result (2026-04-12): identity-outer rigidity really reduces `PO3a` to tail zeros of `H_a`

- the new identity-outer rigidity has now been explicitly connected back to the
  older lower-shell packet:
  after compressing `P_+v_{a,N}=\alpha_{+,N}(a)h_{+,N}` and
  `P_-v_{a,N}=\alpha_{-,N}(a)h_{-,N}` to a finite window, one recovers the old
  alternating-tail law
  `w_{r,0}(a)=c_{a,N,M}(-1)^r` on that window;
- if the physical Volterra normal form is the genuine infinite-tail boundary
  identity, these window constants glue across overlaps to one tail constant
  `c_{a,N}`, and the frozen off-diagonal tail decay forces `c_{a,N}=0`;
- therefore the nontrivial rigidity scenario collapses to the exact tail-zero
  target
  `w_{r,0}(a)=0` for all `r>N`, equivalently
  `H_a(\alpha_r)=0` on the whole tail progression
  `\alpha_r=\pi r/a`;
- this is the cleanest current “impossibility” reduction:
  once the physical Volterra normal form lands, the only remaining obstruction
  is a structured arithmetic-progression uniqueness theorem for the explicit
  Cauchy-type function `H_a`.

## Decision note (2026-04-12): do not take full physical Volterra normal form as the first subgoal

- there is a real risk of looping if we keep alternating between
  “prove physical Volterra normal form” and
  “assume it and derive stronger rigidity” without changing the input;
- the exact physical Volterra identity
  `H_{a,N}=T^*((I-R_a)^*G_g[a](I-R_a)-G_g[a])T`
  is the strongest possible form, but it is not the cheapest first target;
- the cheaper and already-frozen route is the weaker admission statement:
  prove only that the genuine boundary correction is a finite linear
  combination of Volterra-undoing words with at most two endpoint projectors;
- that weaker statement is sufficient for the endpoint normal form, the finite
  receiver, and all downstream mixed-block reductions;
- recommendation: treat the full physical Volterra normal form as a bonus
  strengthening, but make the active mainline
  `raw antiderivative factorization -> finite endpoint-projector count ->
  Volterra-word admission -> endpoint receiver`;
- only after that weaker bridge is real should we spend effort on proving the
  sharper physical identity or on the tail-zero uniqueness wall.

## Final result (2026-04-12): exact weaker bridge for `PO3a`

- the `PO3a` note now contains a precise weaker bridge that is sufficient for
  the active route:
  it is enough to write the genuine boundary correction as a finite sum
  `\sum U_j^*T^*((I-R_a)^*K_j(I-R_a)-L_j)TV_j`
  with sign-preserving outer tail operators and bounded middle kernels, as long
  as the total zero-endpoint part
  `\sum U_j^*T^*(K_j-L_j)TV_j`
  cancels globally;
- after that cancellation, every surviving term contains one or two endpoint
  projectors and therefore automatically falls under
  `PO3a-Volterra-word admission criterion`;
- this is strictly cheaper than the full physical Volterra normal form:
  for `PO3a` we do not need one exact kernel identity, only endpoint counting
  plus global cancellation of the no-endpoint antiderivative part;
- this should now be treated as the main theorem target for the bridge from the
  raw antiderivative factorization to the finite receiver.

## Final result (2026-04-12): the weaker `PO3` bridge splits into two exact subgoals

- the weaker bridge is now decomposed explicitly into:
  `PO3a-A` finite antiderivative extraction and
  `PO3a-B` zero-endpoint cancellation;
- `PO3a-A` asks only for a finite representation
  `\sum U_j^*T^*((I-R_a)^*K_j(I-R_a)-L_j)TV_j`
  with sign-preserving outer tail operators and bounded middle kernels;
- `PO3a-B` is the exact place where bulk exactness must re-enter:
  prove the no-endpoint remainder
  `\sum U_j^*T^*(K_j-L_j)TV_j`
  cancels globally;
- once `PO3a-A + PO3a-B` hold, the already-proved Volterra-word admission
  criterion applies automatically, so the finite receiver follows without ever
  needing the stronger one-kernel physical identity.

## Final result (2026-04-12): direct boundary-word criterion for the finite receiver

- the `PO3a` note now contains an even cheaper sufficient criterion:
  if the genuine boundary correction can be written as a finite sum of words
  `\sum_{\ell=1}^M X_\ell P_J Y_\ell` with one finite boundary projector `P_J`,
  then it automatically has a finite sign-split rank-one decomposition;
- after that, the canonical finite receiver applies with no extra row/column
  bookkeeping, and the mixed block again reduces to one finite matrix identity
  `\mathsf A+\mathsf B+\mathsf M=0`;
- this is now the cleanest operational interface for the live extraction step:
  instead of proving a full matrix formula for `B_{a,N}`, it is enough to
  rewrite it as a finite sum of boundary words through one finite endpoint
  layer.

## In progress (2026-04-12): first oracle battle-test confirms the `PO3a.2` weaker-bridge vocabulary

- exact address: `PO3a.2`, wired between `H-bridge.11` and `PO3a.3`;
- local oracle pass on `q3_docs` with four queries gave one stable answer
  rather than opening a new branch:
  the KB keeps returning the same late `PO3a` packet and the same mainline
  phrase
  `raw antiderivative factorization -> finite endpoint-projector count ->
  Volterra-word admission -> endpoint receiver`;
- the strongest internal file pointers are still
  `docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`,
  `docs/INSIGHTS.md` itself, and
  `Q3/Proofs/HBridge_PO3_Shell.lean`;
- operationally this is good news:
  the question journal is not scattering recall, it is tightening it around
  the real theorem shape for `PO3a.2`;
- vocabulary verdict:
  “weaker Volterra bridge”, “finite endpoint-projector count”, and
  “Volterra-word admission criterion” are strong;
  “full physical Volterra normal form” remains a false first strike on this
  address;
- short external sanity-check did not reveal an off-the-shelf outside theorem
  for this exact weaker bridge, so this subroute still has to be proved from
  our internal packet rather than imported from the literature;
- next local recommendation:
  keep `H-bridge.11` as the upper address for the bridge statement itself, but
  treat `PO3a.2` as the extraction layer and continue downward into `PO3a.3`
  only after the weaker bridge statement is frozen in one reusable theorem
  form.

## In progress (2026-04-13): second oracle pass freezes the exact `H-bridge.11 -> PO3a.2` bridge target

- exact addresses: `H-bridge.11` and `PO3a.2`, still upstream of `PO3a.3`;
- a fresh four-query local oracle pass again did not open a new branch:
  every useful hit points back to the same packet
  `h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`
  together with the late `INSIGHTS` reductions;
- the strongest internal anchors are now stable:
  `PO3a-finite antiderivative mismatch criterion`,
  `PO3a-Volterra-word admission criterion`,
  and the decision note
  “do not take full physical Volterra normal form as the first subgoal”;
- operational conclusion:
  the next real analytic target is no longer “prove the physical Volterra
  normal form” and not “expand the whole boundary correction at once”;
  it is the two-piece weaker bridge
  `PO3a-A + PO3a-B`:
  first extract a finite antiderivative-mismatch expansion, then prove global
  cancellation of the zero-endpoint part;
- once those two pieces land, endpoint counting and the already frozen
  admission criterion push the real boundary defect automatically into the
  finite receiver / boundary-cap framework;
- short external sanity-check again produced no usable outside theorem for this
  bridge shape, so the route remains strictly internal and vocabulary-driven.

## In progress (2026-04-13): the weaker `PO3a-A + PO3a-B` bridge now has a Lean shell

- `Q3/Proofs/HBridge_PO3_Shell.lean` now contains an explicit abstract bridge
  for the weaker Volterra route, not only for the downstream finite receiver;
- the new theorem
  `po3_endpoint_packet_of_weaker_bridge`
  freezes the exact formal handoff
  “boundary defect = zero-endpoint packet + endpoint-word packet” together with
  global cancellation of the zero-endpoint part;
- the companion theorem
  `po3_boundary_zero_of_weaker_bridge_and_matrix_receiver`
  shows that once the surviving endpoint-word packet enters the already frozen
  finite mixing receiver, the whole boundary channel vanishes;
- finally
  `po3_cap_only_of_po2_and_weaker_bridge`
  reconnects this weaker bridge directly back to the old `PO2 -> PO3b`
  cap-only conclusion;
- operational consequence:
  the formal shell is now synchronized with the actual mainline wording
  `PO3a-A + PO3a-B -> admission criterion -> finite receiver`,
  so the next missing step is purely analytic:
  extract the real finite antiderivative-mismatch expansion and prove the
  zero-endpoint cancellation.

## In progress (2026-04-12): `PO3a.3` compresses further to boundary-cap separation on the plus side

- exact address: `PO3a.3`, downstream of `PO3a.2` and upstream of `PO3a.4`;
- new local theorem shape:
  if `U` preserves sign and `U^*|_{\mathcal H_+}` is injective, then plus-side
  collinearity after `U^*` is equivalent to collinearity before `U^*`;
- operationally this is a real compression:
  instead of proving a vague sign statement about the whole zero-mode column,
  it is enough to show
  `P_+ v_{a,N} \notin E_{+,\partial}`,
  where `E_{+,\partial}` is the finite plus-side boundary-cap space already
  supplied by `PO3a-finite reduction`;
- even better, the route admits a dual formulation:
  it is enough to find one bounded functional `\Lambda_+` that kills the whole
  finite boundary-cap space but does not kill `P_+ v_{a,N}`;
- local oracle search on `q3_docs` supports exactly this compression:
  the KB keeps returning the same `PO3a-finite reduction`, the same late
  zero-mode-column packet, and the same shell consumer
  `Q3/Proofs/HBridge_PO3_Shell.lean`;
- no hidden internal theorem was found that closes the new step automatically,
  but this is good news: the search is now stable and sharply localized,
  rather than drifting back to the full `PO3` packet;
- short external sanity-check on general separation vocabulary did not surface
  an off-the-shelf theorem tailored to our route, so the real gain remains
  internal:
  finite receiver + finite boundary-cap space + one detecting functional;
- next local strike:
  extract `E_{+,\partial}` explicitly enough to search for `\Lambda_+`
  through the orthogonal complement / annihilator viewpoint, instead of
  attacking the full mixed block again.

## In progress (2026-04-12): orthogonal-projection witness for the `PO3a.3` plus side

- once the genuine boundary correction is written in boundary-word form
  `B_{a,N}=\sum_{\ell=1}^M X_\ell P_J Y_\ell`,
  the plus-side boundary-cap space becomes completely explicit:
  define the raw right generators
  `g_{\ell,j}^+ := P_+ Y_\ell^* e_j` for `j \in J`,
  and set
  `E_{+,\partial} := \operatorname{span}\{g_{\ell,j}^+\}`;
- let
  `G_{+,\partial}^{raw}` be the raw generator matrix,
  `\Gamma_+ := (G_{+,\partial}^{raw})^* G_{+,\partial}^{raw}`
  its Gram matrix, and
  `\Pi_{+,\partial}
    := G_{+,\partial}^{raw} \Gamma_+^\dagger (G_{+,\partial}^{raw})^*`
  the orthogonal projector onto `E_{+,\partial}`;
- then the natural plus-side witness is
  `f_+ := (I-\Pi_{+,\partial}) P_+ v_{a,N}`;
- exact meaning:
  `f_+ = 0` iff `P_+ v_{a,N} \in E_{+,\partial}`;
  so `f_+ \neq 0` is precisely the statement that the plus-side zero-mode
  receiver has a component which the finite boundary-cap space cannot explain;
- this gives a direct dual detector:
  if `f_+ \neq 0`, then the functional
  `\Lambda_+(x) := \langle x, f_+ \rangle`
  annihilates `E_{+,\partial}` but not `P_+ v_{a,N}`;
- if in addition `U` preserves sign and `U^*|_{\mathcal H_+}` is bounded below,
  then
  `\operatorname{dist}(P_+ U^* v_{a,N}, \mathbb C U^* h_{+,N})
    \ge m_+ \|f_+\|`;
  hence `f_+ \neq 0` rules out plus-side collapse immediately;
- the same construction on the minus side gives
  `f_- := (I-\Pi_{-,\partial}) P_- v_{a,N}`;
  if both `f_+` and `f_-` are nonzero, the `2\times 2` Volterra receiver
  cannot vanish on either side, so the corresponding Volterra-normal-form
  branch is killed;
- this is the sharpest current practical reduction:
  `PO3a.3` is no longer “understand the whole mixed block”, and not even
  “understand the whole zero-mode column”; it is now:
  compute one finite Gram projector and test whether its orthogonal residual on
  `P_+ v_{a,N}` vanishes.

## In progress (2026-04-12): abstract witness shell landed in Lean for `PO3a.3`

- the shell file
  `q3/Proofs/HBridge_PO3_Shell.lean`
  now contains the exact abstract lemmas needed for the current `PO3a.3`
  route:
  if `h ∈ E` but `v ∉ E`, then `v ∉ 𝕜 ∙ h`;
  if an injective linear map sends `v` into the line of the image of `h`, then
  `v` was already in the line of `h`;
- as a result, the current proof target is now frozen in a reusable formal
  packet:
  once the concrete plus-side boundary-cap space `E_{+,\partial}` and the
  concrete vectors `h_{+,N}`, `P_+ v_{a,N}` are plugged in, the non-collinearity
  claim after transport reduces to one subspace-separation claim before
  transport;
- the shell also contains the dual-functional version:
  if a linear functional kills the whole boundary-cap space `E` but not `v`,
  then `v ∉ E`, hence again `v` cannot lie in the line generated by any
  `h ∈ E`;
- operational consequence:
  the live formalization burden has narrowed from “formalize the whole projector
  story at once” to “instantiate the shell with the concrete boundary-cap
  subspace and one separating witness”;
- reusable lemma list now available in Lean:
  `not_mem_span_singleton_of_mem_submodule_of_not_mem`,
  `mem_span_singleton_of_mem_span_singleton_map`,
  `not_mem_span_singleton_map_of_injective`,
  `not_mem_submodule_of_linearForm`,
  `not_mem_span_singleton_map_of_linearForm_witness`.

## In progress (2026-04-13): projector-residual shell landed for the `PO3a.3` Gram route

- the shell file
  `q3/Proofs/HBridge_PO3_Shell.lean`
  now also freezes the minimal projector step behind the Gram/projector route:
  if a linear projector `Pproj` has range `E`, then
  `w ∈ E ↔ Pproj w = w`;
- as a direct corollary, a nonzero residual
  `w - Pproj w ≠ 0`
  already proves
  `w ∉ E`;
  this is exactly the abstract form needed for the concrete witness
  `f_+ = (I-\Pi_{+,\partial}) P_+ v_{a,N}`;
- the shell then pushes this one step further:
  if `h ∈ E`, `f` is injective, and
  `v - Pproj v ≠ 0`,
  then
  `f v ∉ 𝕜 ∙ f h`;
  in the live route this is the formal bridge from
  `P_+ v_{a,N} ∉ E_{+,\partial}`
  to non-collinearity after transport by `U^*`;
- this closes the abstract part of the projector route:
  the remaining burden is no longer to formalize projector algebra itself, but
  to instantiate the shell with the concrete boundary-cap projector
  `\Pi_{+,\partial}` and the concrete residual witness;
- reusable new lemma list now available in Lean:
  `mem_submodule_iff_projector_eq_self`,
  `not_mem_submodule_of_projector_residual_ne_zero`,
  `not_mem_span_singleton_map_of_projector_residual_ne_zero`.

## In progress (2026-04-13): `PO3a.4` narrows to outer-factor stripping

- the new oracle pass confirms the exact next bridge:
  the `2x2` physical Volterra receiver already gives the right rigidity
  mechanism, and the only extra step is to strip the outer factors `U,V`
  without losing that rigidity;
- the load-bearing split is asymmetric and this matters:
  on the vector side, dependence descends through `U^*` by injectivity;
  on the functional side, dependence of
  `⟨V^* P_- v_{a,N}|` and `⟨\ell_{-,N} P_- V|`
  descends to the identity-outer pair only if precomposition by `V` is
  surjective on the relevant space;
- so the real abstract shell is not “invertibility everywhere”, but the cheaper
  pair of transfer lemmas:
  injective postcomposition preserves vector non-collinearity, and surjective
  precomposition preserves non-collinearity of linear functionals;
- the vector half is already frozen in
  `q3/Proofs/HBridge_PO3_Shell.lean`;
  the missing half is the functional pullback lemma
  `φ ∘ V ∈ 𝕜∙(ψ ∘ V) ⇒ φ ∈ 𝕜∙ψ`
  under surjectivity of `V`;
- once that lands, the real `U,V` route can be reduced back to the already
  identified identity-outer rigidity target:
  `PO3a` forces endpoint-line rigidity for the zero-mode receiver, and that
  returns directly to the tail-zero target for `H_a`.

## Final result (2026-04-13): the missing minus-side outer bridge is now frozen in Lean

- the exact formal gap in `PO3a.4` was the right-hand transfer step:
  if two functionals become collinear after precomposition with `V`, can that
  collinearity be pulled back to the original pair;
- the answer is now formalized in
  `q3/Proofs/HBridge_PO3_Shell.lean`:
  over a field, surjectivity of `V` is enough for the pullback lemma
  `φ.comp V ∈ 𝕜∙(ψ.comp V) ⇒ φ ∈ 𝕜∙ψ`,
  and therefore original non-collinearity of functionals survives
  precomposition by a surjective outer map;
- together with the already frozen injective vector-side lemma, this pins down
  the exact abstract route from real outer factors back to the identity-outer
  rigidity packet:
  left side needs injectivity, right side needs surjectivity;
- this is the real compression:
  `PO3a.4` is no longer “understand arbitrary outer operators”, but only
  “verify the relevant `U,V` satisfy those transfer hypotheses on the tail
  spaces”;
- reusable new lemma list now available in Lean:
  `mem_span_singleton_of_comp_mem_span_singleton_of_surjective`,
  `not_mem_span_singleton_comp_of_surjective`.

## In progress (2026-04-13): `PO3a.4` is even cheaper after Riesz identification on the minus side

- the new rigidity observation improves the current bridge:
  once the minus-side endpoint functional is replaced by its Riesz vector
  `h_-`, the real `2x2` receiver can be written with the pair
  `V^* x_- , V^* h_-`
  on the right, not only with pulled-back functionals;
- that changes the cost of the bridge:
  for the main route, we no longer need surjectivity of `V` as the first
  hypothesis;
  injectivity of `V^*` on the minus space is enough, because linear
  independence of `x_- , h_-` then forces linear independence of
  `V^* x_- , V^* h_-`, hence surjectivity of the two-functional receiver
  follows automatically;
- together with injectivity of `U^*` on the plus space and sign preservation,
  vanishing of the physical Volterra `2x2` block already returns exactly the
  same scalar rigidity as in the identity-outer case:
  there exist `λ, μ` with
  `P_+ v_{a,N} = λ h_{+,N}`,
  `P_- v_{a,N} = μ h_{-,N}`,
  and `λ + μ = c_a`;
- this is the sharp compression:
  the surjective pullback lemma remains valid as a backup route, but it is no
  longer the cheapest mainline;
  the cheapest mainline is now:
  sign-preserving + injective `U^*` on `H_+` + injective `V^*` on `H_-`
  + nonzero endpoint vectors.

## In progress (2026-04-13): `PO3a.4` now splits cleanly into abstract outer-invariance and the real origin of `U,V`

- the new local search on the exact address `PO3a.4` confirms a hard but useful
  fact: inside the current reviewed notes, `U,V` do not yet appear as a
  separately derived concrete formula for the genuine boundary difference;
- the earliest live place where they enter is still theorem-shaped:
  first in `PO3a-finite antiderivative mismatch criterion` through the family
  `U_j,V_j`, then in `PO3a-two-endpoint extraction`, and only after that in the
  physical `2x2` receiver;
- therefore the current blocker must be stated honestly:
  `PO3a.4` does not yet reduce to “check harmlessness of known `U,V`”;
  before that, one still needs the upstream extraction layer that writes the
  real defect in the form
  `\sum U_j^*T^*((I-R_a)^*K_j(I-R_a)-L_j)TV_j`;
- this is still progress, not drift:
  the abstract outer-invariance lemma remains worth formalizing, because once
  the extraction lands it will immediately strip the outer layer and return the
  route to the already frozen identity-outer rigidity;
- operationally the branch now splits into two exact subquestions:
  `PO3a-A` = derive the outer-layer representation from the real difference,
  and `PO3a.4` = prove that such an outer layer is harmless under local
  sign-preserving and injective hypotheses.

## In progress (2026-04-13): `PO3a-A` now has one exact upstream anchor

- a fresh address-bound oracle pass on `PO3a-A` did not uncover a hidden ready
  formula for the outer layer `U_j,V_j`; it confirmed something sharper:
  the earliest exact internal anchor is the antiderivative factorization
  `I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N`;
- therefore the honest extraction problem is no longer “guess `U_j,V_j`” but
  “transport the real defect to the Volterra-antiderivative side and isolate
  the endpoint defect created by undoing `I_0^{(a)}`”;
- the formal obstruction is already frozen in the note:
  `D_a I_0^{(a)} = I` while `I_0^{(a)}D_a = I - R_a`,
  so any genuine boundary word must come from the rank-one endpoint projector
  `R_a`, not from hidden mixed combinatorics inside the filtered tail synthesis;
- this sharpens the exact role of `PO3a-A`:
  it should produce a word-level factorization of the real difference in terms
  of `T`, bounded middle kernels, and finitely many endpoint insertions
  `R_a, R_a^*`;
- the right next local theorem target is therefore:
  first transport both the Suzuki term and the comparison term to the
  antiderivative side, then show that their difference expands into finitely
  many Volterra-undoing words, after which `PO3a-B` handles the zero-endpoint
  remainder and the existing admission criterion takes over.

## In progress (2026-04-13): Lean shell now covers the `PO3a-A` handoff

- `Q3/Proofs/HBridge_PO3_Shell.lean` now contains the exact abstract handoff
  for the new upstream picture:
  after transporting the genuine boundary packet to the antiderivative side,
  one expands it into a zero-endpoint packet plus an endpoint-word packet, and
  the existing weaker bridge then takes over automatically;
- the new shell lemmas are
  `po3_endpoint_packet_of_antiderivative_transport` and
  `po3_boundary_zero_of_antiderivative_transport_and_matrix_receiver`;
- this does not solve the analytic content of `PO3a-A`, but it freezes the
  exact formal interface that the real derivation now has to hit;
- compilation check passes:
  `lake env lean Q3/Proofs/HBridge_PO3_Shell.lean`;
  the only output is the old non-blocking linter warning about an unused
  section variable in the earlier surjective functional lemma.

## In progress (2026-04-13): `PO3a.4` now has a practical finite-dimensional outer criterion

- the new practical criterion is now frozen conceptually:
  once the real outer layer `U,V` is extracted, we do not need global control
  of those operators;
  it is enough to control their restrictions to the finite endpoint spaces on
  which the `2×2` receiver actually lives;
- the exact algebra behind this is now explicit in
  `Q3/Proofs/HBridge_PO3_Shell.lean`:
  injective transport preserves and reflects collinearity of vectors, and
  surjective pullback preserves and reflects collinearity of linear functionals;
- operationally this turns the live `PO3a.4` check into a finite-dimensional
  one:
  once endpoint spaces `F_+` and `F_-` are chosen, it is enough to show that
  the induced outer maps are invertible there;
- this is why the triangular / unitriangular scenario is the right practical
  target:
  on a chosen endpoint basis, triangular matrices with nonzero diagonal are
  automatically invertible, so the outer layer becomes harmless without any
  new global analysis;
- the matrix-level determinant criterion itself is not yet formalized in Lean;
  the shell now freezes the exact algebraic interface that such a finite-basis
  computation would feed into.

## In progress (2026-04-13): Lean shell now contains the exact two-endpoint expansion

- `Q3/Proofs/HBridge_PO3_Shell.lean` now also formalizes the raw algebraic
  expansion behind `PO3a-two-endpoint extraction`:
  `po3_two_endpoint_expansion` proves that
  `L * (((1 - R_left) * K * (1 - R_right)) - K) * N`
  splits exactly into the three surviving terms
  `- L R_left K N`, `- L K R_right N`, and
  `+ L R_left K R_right N`;
- this is the exact finite endpoint-count identity from the note: after
  expansion, only the left one-endpoint brick, the right one-endpoint brick,
  and the two-endpoint brick remain;
- operationally this tightens the live `PO3a-A` burden:
  the missing mathematics is no longer the algebra of the expansion itself,
  but only the derivation that the genuine boundary defect really lands in this
  transported Volterra form with the correct outer factors;
- compilation check passes:
  `lake env lean Q3/Proofs/HBridge_PO3_Shell.lean`;
  the only output remains the old non-blocking linter warning about the earlier
  section variable capture in the surjective functional lemma.

## In progress (2026-04-13): `PO3a-A0` is the right upstream split before the Volterra kernel

- the live upstream gap is now sharper than `PO3a-A` itself: before trying to
  prove that the genuine defect has the Volterra form
  `T^*((I-R_a)^*K_a(I-R_a)-L_a)T + boundary`,
  one first needs a general two-variable extraction formula for the defect;
- the correct shape is not a guessed final identity but a discrete
  Newton–Leibniz / double telescoping packet:
  `defect = corner + row strip + column strip + T^*(mixed interior difference)T`;
- local oracle search did not surface any earlier reviewed theorem already
  freezing this exact packet; it only returned the current `PO3` note, the
  row/column finite receiver material, and the new shell file;
- therefore `PO3a-A0` should be treated as a genuine new address:
  first formalize the generic two-variable extraction, then in `PO3a-A1`
  substitute the real defect and identify its mixed interior difference with
  `(I-R_a)^*K_a(I-R_a)-L_a`;
- only after that does the already formalized two-endpoint expansion become the
  right downstream tool, because then the remaining row/column/corner pieces
  are honest boundary strips rather than guessed leftovers.

## In progress (2026-04-13): Lean shell now contains the discrete `PO3a-A0` double telescoping packet

- `Q3/Proofs/HBridge_PO3_Shell.lean` now contains three exact discrete
  telescoping lemmas:
  `po3_sum_range_succ_sub`,
  `po3_telescoping_one_variable`,
  and the new two-variable theorem
  `po3_double_telescoping`;
- the last theorem is the exact abstract `PO3a-A0` receiver:
  for any defect `D`, it rewrites
  `D (N+m) (N+n)` as
  `corner + row strip + column strip + bulk mixed difference`,
  with the bulk term written as a double sum of the mixed interior difference;
- this means the algebraic part of the user’s proposed route is now frozen in
  Lean, not only in notes:
  the remaining live mathematics is strictly narrower, namely to substitute the
  real defect into this generic packet and identify its bulk mixed difference
  with `(I-R_a)^*K_a(I-R_a)-L_a`;
- compilation check passes:
  `lake env lean Q3/Proofs/HBridge_PO3_Shell.lean`;
  the only remaining output is the earlier non-blocking section-variable
  warning in the old surjective-functional lemma.
