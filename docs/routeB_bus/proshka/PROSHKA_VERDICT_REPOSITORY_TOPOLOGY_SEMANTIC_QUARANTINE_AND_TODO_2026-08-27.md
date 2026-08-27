# STATUS: CONDITIONAL — KEEP THE PROOF MONOREPO; QUARANTINE LEGACY NOW; SPLIT TOOLING ONLY AFTER EXIT GATES

```yaml
PRIMARY: KEEP_MONOREPO_WITH_HARD_SEMANTIC_BOUNDARIES
PRIMARY_COUNT: 1

REQUEST:
  kind: OWNER_DIRECT_ARCHITECTURE_AND_EXECUTION_PLAN
  date: 2026-08-27
  queue_status_mutated: false

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  audited_head: 809b776bd628c39a5e99dc54e9720a4e7a4bd0a0
  local_linux_worktree_byte_identity_verified: false

DECISION:
  create_new_repository_now: false
  selected_pattern: STRANGLER_MONOREPO_WITH_IMPORT_FIREWALL
  proof_core_and_live_challengers_same_repo: true
  legacy_quarantine_in_place_first: true
  mass_file_move_now: false
  public_claim_freeze_until_p0_done: true

SEMANTIC_ZONES:
  - CORE_SHARED
  - PUBLIC_CANONICAL
  - CHALLENGER_ROUTE_B
  - LEGACY_QUARANTINE
  - LAB_AND_DISCOVERY_SIDECAR

FUTURE_SPLITS:
  q3_discovery:
    status: CONDITIONAL
    allowed_after:
      - STABLE_VERSIONED_SCHEMA
      - INDEPENDENT_CLI_OR_PACKAGE_BOUNDARY
      - HOLDOUT_BACKTEST_VALUE
      - ZERO_LIVE_ROUTE_WRITES
      - MAINTENANCE_COST_BELOW_SAVED_WORK
  chen_q3_legacy_archive:
    status: CONDITIONAL
    allowed_after:
      - ZERO_ACTIVE_IMPORTS
      - ZERO_PUBLIC_EXPORTS
      - FROZEN_READ_ONLY_CONTENT
      - HISTORY_PRESERVATION_PLAN
  route_b:
    status: DO_NOT_SPLIT
    reason: SAME_FAMILY_SOURCE_LOCK_AND_ATOMIC_CROSSWALKS_ARE_LIVE
  proof_certificates:
    status: DO_NOT_SPLIT
    reason: SOURCE_AND_CERTIFICATE_MUST_REMAIN_ATOMICALLY_PINNED

IMMEDIATE_FATAL_SURFACES_FOR_PUBLIC_CLAIM:
  - LEGACY_BROAD_CONE_RH_EXPORT_IN_Q3_MAIN
  - T1_6_ARCH_FLOOR_SOURCE_CONTRADICTION
  - STALE_ROOT_README_STATUS
  - UNPROTECTED_RH_CLEAN_WITHOUT_REQUIRED_CHECKS

CLOSES:
  - REPOSITORY_TOPOLOGY_DECISION
  - NEW_REPOSITORY_NOW_AMBIGUITY
  - LEGACY_QUARANTINE_STRATEGY_AMBIGUITY
  - DISCOVERY_SIDECAR_EXTRACTION_POLICY_AMBIGUITY
  - SEMANTIC_CLEANUP_EXECUTION_ORDER_AMBIGUITY

OPENS: []
CARRIES_OPEN:
  - LEGACY_EXPORT_SEMANTIC_QUARANTINE
  - T1_6_ARCH_FLOOR_CORRECTION
  - PUBLIC_EXPORT_AXIOM_AUDIT
  - MONOREPO_IMPORT_FIREWALL
  - REQUIRED_CI_AND_BRANCH_PROTECTION
  - SINGLE_AUTHORITATIVE_STATE_AND_GENERATED_VIEWS
  - ABSOLUTE_PATH_PORTABILITY_CLEANUP

REGISTERED_PREDICTIONS:
  P_REPO_1:
    probability: 0.93
    prediction: A_PHYSICAL_SPLIT_NOW_WOULD_INCREASE_SOURCE_LOCK_AND_VERSION_DRIFT
  P_REPO_2:
    probability: 0.96
    prediction: IMPORT_FIREWALL_PLUS_PUBLIC_EXPORT_QUARANTINE_REMOVES_THE_HIGHEST_RISK_SEMANTIC_FAILURES
  P_REPO_3:
    probability: 0.86
    prediction: DISCOVERY_TOOLING_DESERVES_A_SEPARATE_REPO_ONLY_AFTER_AN_INDEPENDENT_STABLE_API_AND_MEASURED_VALUE
  P_REPO_4:
    probability: 0.91
    prediction: MOVING_ROUTE_B_DURING_THE_LIVE_SAME_FAMILY_FRONT_WOULD_CREATE_MORE_ERRORS_THAN_IT_REMOVES

SCOPE: ABSTRACT
VERIFIER: PAPER_AND_SOURCE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Вопрос | Решение | Причина | Статус |
|---|---|---|---|
| Делать новый repository прямо сейчас? | **Нет** | Главная ошибка — не размер Git, а ложные semantic edges между объектами. Split добавит cross-repo version drift. | `[ABSTRACT][PAPER]` |
| Оставлять всё как есть? | **Нет** | Текущая корневая поверхность позволяет принять legacy export за канонический результат. | `[ABSTRACT][SOURCE]` |
| Что делать сейчас? | **Strangler monorepo** | Сначала вводится import firewall, honest public surface и legacy quarantine без массового перемещения файлов. | `[ABSTRACT][PAPER]` |
| Что можно вынести позже? | **Discovery sidecar** | У него отдельный engineering lifecycle; существующий mandate уже требует сначала shadow value. | `[ABSTRACT][SOURCE]` |
| Что нельзя выносить сейчас? | **Route B и certificates** | Same-family crosswalks, Lean source и verification receipts должны оставаться в одном атомарном commit graph. | `[COFINAL_FAMILY][PAPER]` |

## 1. Решение по topology

**Monorepo** — один Git-repository для нескольких частей проекта. Он безопасен только тогда, когда физическое соседство файлов не означает разрешённый dependency.

**Semantic boundary** — машинно проверяемая граница: какие modules могут импортировать какие modules, какие theorems могут входить в public export и какой axiom profile разрешён.

**Strangler migration** — постепенная замена опасной старой поверхности новой: сначала вводится firewall и новый честный entrypoint, затем legacy перестаёт быть dependency, и только после этого старый слой перемещается или выносится.

Выбранная схема:

```text
Malaeu/chen_q3
│
├── CORE_SHARED
│   definitions, exact transforms, general Lean engines, checked adapters
│
├── PUBLIC_CANONICAL
│   only the corrected public RH contract; no challenger or legacy imports
│
├── CHALLENGER_ROUTE_B
│   live source-locked experiments and theorems; explicitly NOT_RH
│
├── LEGACY_QUARANTINE
│   broad-cone compiled route, historical axioms, old wrappers and snapshots
│
└── LAB_AND_DISCOVERY_SIDECAR
    numerics, agent OS, discovery compiler, generated exploratory artifacts
```

Физические directories не требуется немедленно переименовывать. Сначала classification и import graph становятся executable. Массовое `git mv` до этого создаст churn, но не создаст границу.

### Почему не три новых repository сейчас

1. **Core и Route B используют общие exact objects.** Разделение заставит версионировать crosswalks между repositories и повышает риск `same coordinates, two laws`.
2. **Certificates должны ехать вместе с consumers.** Раздельные commits уничтожат атомарность source lock.
3. **Legacy ещё импортируется compiled surface.** Вынести его сейчас — значит либо сломать build, либо создать compatibility package, который снова сделает legacy активным.
4. **Discovery sidecar ещё не доказал независимую ценность.** Его текущая архитектура уже классифицирована как same-repo shadow first, separate repo only after measured value.
5. **Количество repositories не является semantic firewall.** Без schema, import rules и versioned contracts ложные bridges просто переедут в network calls и pinned SHAs.

Мы не используем непроверяемую внутреннюю организацию OpenAI как аргумент. Успех любого большого monorepo объясняется не названием компании, а жёсткими module boundaries, ownership, path-based CI, generated status и dependency checks.

## 2. Факты, требующие немедленного ремонта

### 2.1 Корневой status врёт по времени

`README.md` всё ещё показывает `Current Status (2026-01-21)` и старый счёт аксиом. Это первая поверхность нового читателя.

### 2.2 Default Lean entry выглядит как доказанный RH theorem

`Q3.Main.RH_of_Weil_and_Q3 : Q3.RH` существует в default namespace, хотя source-комментарий признаёт:

```text
compiled broad-cone route;
background-only;
not the corrected Weil-square export;
depends on Weil_criterion and prime_term_le_at_t_critical_axiom.
```

Комментарий не является firewall.

### 2.3 `Axioms.lean` содержит source-level contradiction

T1.3 доказывает только `a_star 0 > 0` и прямо пишет, что global pointwise positivity false. T1.6 затем обосновывает `c_arch_pos` фразой `a_star ξ > 0 for all ξ (T1.3)`. Следом torus-symbol floor `c_star` переносится на pointwise `c_arch` без доказанного object crosswalk.

### 2.4 `rh_clean` fail-open

Ветка не защищена, required status checks отсутствуют, `.github/workflows` отсутствует. SHA receipts проверяют доставку, но canonical branch не требует kernel gate.

### 2.5 Stable architecture и live surface расходятся

`PROJECT_ORCHESTRATOR.md` правильно разделяет public mainline, fallback и Route B challenger. Но `README.md`, `Q3.Main`, legacy docs и generated surfaces не принуждены следовать этому разделению.

## 3. Target architecture contracts

### 3.1 Module classes

Каждый public-facing Lean module и каждый status document получает один class:

```text
CORE_SHARED
PUBLIC_CANONICAL
CHALLENGER
CONDITIONAL_COMPILED
LEGACY
EXPERIMENT
ARCHIVE
GENERATED_VIEW
```

### 3.2 Import firewall

**Import firewall** — script, который строит import graph и отклоняет forbidden edges.

Правила:

```text
PUBLIC_CANONICAL may import:
  CORE_SHARED
  verified external/classical adapters explicitly allowed by policy

PUBLIC_CANONICAL must not import:
  CHALLENGER
  CONDITIONAL_COMPILED
  LEGACY
  EXPERIMENT
  ARCHIVE

CHALLENGER may import:
  CORE_SHARED

CHALLENGER must not be imported by PUBLIC_CANONICAL.

LEGACY may import CORE_SHARED,
but no active public module may import LEGACY.

LAB may read exported schemas,
but must not mutate proof state or supply theorem truth.
```

### 3.3 Public export contract

**Public export** — theorem intended as the canonical statement a reader or paper may cite.

Each public export must ship:

```yaml
THEOREM:
LEAN_PATH:
STATEMENT_HASH:
TEST_CLASS:
SOURCE_OBJECT:
AXIOM_PROFILE:
SCOPE:
VERIFIER:
ROUTE:
PUBLIC_STATUS: PROVED | CONDITIONAL | OPEN
```

No theorem named as an unconditional RH result may remain in the default public namespace while its profile contains project assumptions or the wrong test class.

### 3.4 Axiom policy

Classify every nonstandard dependency:

```text
STANDARD_KERNEL
EXTERNAL_CLASSICAL_THEOREM
PROJECT_CONDITIONAL_ASSUMPTION
FORBIDDEN_IN_PUBLIC_EXPORT
```

`#print axioms` is evaluated for every public theorem, not only the top wrapper.

### 3.5 State policy

One authoritative machine state produces all human views.

```text
machine state / append-only event log
       ↓
generated README status
route dashboard
queue view
proof graph
publication status
```

Hand-maintained duplicate status paragraphs become prohibited selectors.

## 4. Granular TODO ledger

Status vocabulary:

```text
OPEN      task is ready or waiting on listed dependencies
BLOCKED   cannot start until an exact dependency closes
HOLD      intentionally not selected
DONE      acceptance test passed and receipt exists
KILL      task or representation rejected with autopsy
```

### Phase P0 — freeze, inventory and public honesty

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P0.001 | OPEN | Record current `rh_clean` head and tag the pre-cleanup state. | none | Immutable tag/receipt names `809b776b…` or newer exact head. | `PRE_CLEANUP_PIN_MISSING` |
| P0.002 | OPEN | Freeze new public RH-completion claims during cleanup. | P0.001 | Status file says `UNCONDITIONAL_RH_PROOF: NO`; no new promotion. | `PUBLIC_CLAIM_DURING_QUARANTINE` |
| P0.003 | OPEN | Inventory every theorem whose name or docstring suggests RH closure. | P0.001 | Table includes theorem, file, statement, route and exact dependencies. | `PUBLIC_EXPORT_INVENTORY_INCOMPLETE` |
| P0.004 | OPEN | Run `#print axioms` for every item from P0.003. | P0.003 | Machine receipt records all profiles. | `PUBLIC_AXIOM_PROFILE_MISSING` |
| P0.005 | OPEN | Inventory all test classes used by RH-facing theorems. | P0.003 | Exact Lean types distinguish broad cone, corrected square class and challengers. | `TEST_CLASS_ALIASING_UNRESOLVED` |
| P0.006 | OPEN | Classify each RH-facing theorem as `PROVED`, `CONDITIONAL`, `LEGACY`, or `OPEN`. | P0.004, P0.005 | No unclassified theorem remains. | `PUBLIC_STATUS_UNCLASSIFIED` |
| P0.007 | OPEN | Produce the single public status banner from P0.006. | P0.006 | Banner has exact date, head and axiom summary. | `PUBLIC_STATUS_BANNER_DRIFT` |
| P0.008 | OPEN | Replace root README status with generated content or an immutable pointer to it. | P0.007 | README no longer claims 2026-01-21 as current. | `ROOT_README_STALE` |
| P0.009 | OPEN | Mark paper/manuscript front pages with the same current status. | P0.007 | All public-facing PDFs/TeX sources carry the same honesty boundary. | `MANUSCRIPT_STATUS_DRIFT` |
| P0.010 | OPEN | Create a public theorem index with exact source links and verifier tags. | P0.006 | Every public claim has one canonical index row. | `PUBLIC_THEOREM_INDEX_INCOMPLETE` |

### Phase P1 — quarantine the compiled broad-cone export

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P1.001 | OPEN | Build reverse dependency graph of `Q3.Main.RH_of_Weil_and_Q3`. | P0.003 | Exact imports and theorem dependencies are listed. | `LEGACY_EXPORT_DEP_GRAPH_INCOMPLETE` |
| P1.002 | OPEN | Create honest namespace/name for the compiled conditional theorem. | P1.001 | New name contains `Conditional` or `LegacyBroadCone`; statement unchanged. | `LEGACY_EXPORT_RENAMED_WITH_WEAKENING` |
| P1.003 | OPEN | Preserve compatibility through a deprecated wrapper, not a public canonical export. | P1.002 | Existing internal imports compile; wrapper is explicitly deprecated/conditional. | `COMPAT_WRAPPER_STILL_PUBLIC_CANONICAL` |
| P1.004 | OPEN | Remove unconditional-looking RH theorem from default public entrypoint. | P1.003 | Default public module exports no `RH` theorem with project assumptions or wrong class. | `DEFAULT_EXPORT_STILL_LEGACY` |
| P1.005 | OPEN | Move or logically classify broad-cone modules as `CONDITIONAL_COMPILED`. | P1.001 | Import firewall identifies them uniquely. | `LEGACY_CLASSIFICATION_AMBIGUOUS` |
| P1.006 | OPEN | Add a negative plant: public module importing legacy must fail CI. | P1.005 | Plant is rejected by import-firewall test. | `IMPORT_FIREWALL_PLANT_ESCAPED` |
| P1.007 | OPEN | Add a positive control: legacy compatibility build still compiles separately. | P1.003 | Dedicated legacy target is green. | `LEGACY_COMPAT_BUILD_BROKEN` |
| P1.008 | HOLD | Physically move legacy files. | P1.004–P1.007 | Start only after zero public imports and clean dedicated target. | `PREMATURE_LEGACY_MOVE` |

### Phase P2 — repair the Archimedean floor collision

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P2.001 | OPEN | Search all consumers of `c_arch_pos`. | none | Exact theorem-level reverse dependency list. | `C_ARCH_CONSUMER_SCAN_INCOMPLETE` |
| P2.002 | OPEN | Search all consumers of `c_star_le_c_arch`. | none | Exact theorem-level reverse dependency list. | `C_STAR_C_ARCH_CONSUMER_SCAN_INCOMPLETE` |
| P2.003 | OPEN | Separate objects `a_star` and `P_A` in a typed crosswalk table. | none | Domains, measures, periodization and units recorded. | `ARCH_OBJECT_CROSSWALK_UNTYPED` |
| P2.004 | OPEN | Plant a point where global `a_star > 0` fails or source admits failure. | P2.003 | Plant prevents T1.3 from being consumed as global positivity. | `ARCH_GLOBAL_POSITIVITY_PLANT_ESCAPED` |
| P2.005 | OPEN | Quarantine `c_arch_pos` until an exact theorem exists. | P2.001, P2.004 | Public routes no longer depend on it as classical fact. | `C_ARCH_POS_STILL_PUBLIC_ASSUMPTION` |
| P2.006 | OPEN | Quarantine `c_star_le_c_arch` until exact periodization crosswalk exists. | P2.002, P2.003 | No consumer silently transfers a torus floor to a pointwise kernel infimum. | `TORUS_TO_POINTWISE_SURROGATE_ESCAPE` |
| P2.007 | OPEN | Decide weakest repaired statement actually needed by surviving consumers. | P2.001, P2.002 | One theorem-sized target, not a global positivity wish. | `ARCH_REPAIR_TARGET_TOO_STRONG` |
| P2.008 | BLOCKED | Prove repaired theorem or remove dead consumer. | P2.007 | Clean Lean theorem or dependency elimination. | `ARCH_FLOOR_REPAIR_OPEN` |

### Phase P3 — module classification and import firewall

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P3.001 | OPEN | Define machine schema for module classes. | none | Closed enum and path/module mapping schema exist. | `MODULE_CLASS_SCHEMA_MISSING` |
| P3.002 | OPEN | Classify all modules reachable from public exports. | P3.001, P0.003 | 100% reachable modules classified. | `PUBLIC_REACHABILITY_UNCLASSIFIED` |
| P3.003 | OPEN | Classify Route B modules as challenger, preserving current paths. | P3.001 | No mass rename; all Route B modules identified. | `ROUTEB_CLASSIFICATION_GAP` |
| P3.004 | OPEN | Classify legacy modules. | P3.001, P1.001 | All broad-cone and obsolete route modules identified. | `LEGACY_MODULE_SET_INCOMPLETE` |
| P3.005 | OPEN | Classify experiment/generated/archive modules. | P3.001 | No generated output can appear as proof source. | `GENERATED_SOURCE_CLASSIFICATION_GAP` |
| P3.006 | OPEN | Implement import graph extractor. | P3.001 | Graph is reproducible from clean checkout. | `IMPORT_GRAPH_NONREPRODUCIBLE` |
| P3.007 | OPEN | Implement forbidden-edge rules. | P3.002–P3.006 | CI rejects every forbidden class edge. | `FORBIDDEN_IMPORT_EDGE_SURVIVED` |
| P3.008 | OPEN | Add shared-context guard for source family and normalization adapters. | P3.007 | Similar surface types cannot bind across different family keys without theorem adapter. | `SAME_INTERFACE_WRONG_FAMILY_ESCAPE` |
| P3.009 | OPEN | Require explicit adapter theorem for every cross-zone mathematical transfer. | P3.008 | Each transfer names preserved/dropped structure and evidence. | `CROSS_ZONE_NARRATIVE_BRIDGE` |
| P3.010 | OPEN | Add import-firewall report to every public CI run. | P3.007 | Report is an attached required check. | `IMPORT_FIREWALL_NOT_REQUIRED` |

### Phase P4 — CI and protected canonical branch

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P4.001 | OPEN | Add direct Lean check for each changed proof file. | none | Clean checkout executes `lake env lean` on changed modules. | `CI_DIRECT_LEAN_MISSING` |
| P4.002 | OPEN | Add module-target build. | P4.001 | `lake build <module>` is required. | `CI_TARGET_BUILD_MISSING` |
| P4.003 | OPEN | Add full production build. | P4.001 | Full build is required before merge/push to protected branch. | `CI_FULL_BUILD_MISSING` |
| P4.004 | OPEN | Add `scripts/q3_check.sh` gate. | P4.001 | Standard checker is required and executable. | `CI_Q3_CHECK_MISSING` |
| P4.005 | OPEN | Add hole scan for `sorry`, `admit`, hidden `axiom`, fake constants. | none | New forbidden declarations fail. | `CI_HOLE_SCAN_MISSING` |
| P4.006 | OPEN | Add per-public-theorem axiom audit. | P0.004 | Expected profile compared exactly. | `CI_AXIOM_AUDIT_MISSING` |
| P4.007 | OPEN | Add import firewall check. | P3.010 | Forbidden imports fail. | `CI_IMPORT_FIREWALL_MISSING` |
| P4.008 | OPEN | Add state/view drift check. | P5.006 | Generated views match machine state. | `CI_STATE_DRIFT_MISSING` |
| P4.009 | OPEN | Add absolute-path portability check. | P6.003 | Forbidden machine paths fail. | `CI_ABSOLUTE_PATH_SCAN_MISSING` |
| P4.010 | OPEN | Add root-hygiene and generated-artifact check. | P6.006 | New root dumps/snapshots fail. | `CI_ROOT_HYGIENE_MISSING` |
| P4.011 | OPEN | Enable branch protection on `rh_clean`. | P4.001–P4.010 | Required checks enabled; force-push disabled. | `RH_CLEAN_UNPROTECTED` |
| P4.012 | OPEN | Define emergency bypass with explicit owner receipt and postmortem. | P4.011 | No silent bypass exists. | `BRANCH_PROTECTION_BYPASS_UNTRACKED` |

### Phase P5 — one authoritative state, generated views

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P5.001 | OPEN | Inventory every file claiming current route, active goal, axiom count or next action. | none | Complete status-surface map. | `STATUS_SURFACE_INVENTORY_INCOMPLETE` |
| P5.002 | OPEN | Select one authoritative machine state and append-only event log. | P5.001 | Exact precedence and schema are frozen. | `STATE_AUTHORITY_AMBIGUOUS` |
| P5.003 | OPEN | Separate mathematical facts from execution state. | P5.002 | Facts and mutable selectors live in distinct typed stores. | `FACT_STATE_CONFLATION` |
| P5.004 | OPEN | Generate README status, dashboards, queue summaries and proof graphs. | P5.002 | Generated headers include source state hash. | `GENERATED_VIEW_WITHOUT_SOURCE_HASH` |
| P5.005 | OPEN | Mark historical monitors as non-selectors in machine-readable metadata. | P5.001 | No historical monitor can select work. | `STALE_MONITOR_SELECTED_WORK` |
| P5.006 | OPEN | Implement view drift checker. | P5.004 | Manual divergence is detected. | `GENERATED_VIEW_DRIFT_UNDETECTED` |
| P5.007 | OPEN | Preserve append-only correction history. | P5.002 | Corrections never erase registered predictions or old verdicts. | `RETROACTIVE_STATE_REPAIR` |
| P5.008 | OPEN | Reduce duplicated full-history state files to event references and generated summaries. | P5.006 | Active state is small; history remains queryable. | `STATE_DUPLICATION_PERSISTS` |

### Phase P6 — portability and repository hygiene

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P6.001 | OPEN | Scan versioned files for `/Users/...`, `/mnt/...`, `/home/...` and stale repo names. | none | Machine-path inventory committed. | `ABSOLUTE_PATH_INVENTORY_INCOMPLETE` |
| P6.002 | OPEN | Classify each path as documentation receipt, executable config or forbidden dependency. | P6.001 | Every hit classified. | `ABSOLUTE_PATH_UNCLASSIFIED` |
| P6.003 | OPEN | Replace executable absolute paths with repo-root discovery or environment variables. | P6.002 | Mac and Linux commands resolve from clean checkout. | `EXECUTABLE_ABSOLUTE_PATH_REMAINS` |
| P6.004 | OPEN | Preserve historical absolute paths only inside clearly historical receipts. | P6.002 | Historical evidence remains immutable and non-executable. | `HISTORICAL_PATH_MUTATED_OR_ACTIVE` |
| P6.005 | OPEN | Audit symlinks across Mac/Linux and clean checkout. | none | `ACTIVE` and compatibility links have explicit cross-platform tests. | `SYMLINK_PORTABILITY_GAP` |
| P6.006 | OPEN | Inventory root-level generated/draft files and browser snapshots. | none | Each is KEEP, MOVE, ARCHIVE or IGNORE with reason. | `ROOT_ARTIFACT_UNCLASSIFIED` |
| P6.007 | OPEN | Move active generated Lean payloads into declared generated source directories with manifests. | P6.006 | No unclassified generated Lean file remains at root. | `ROOT_GENERATED_LEAN_REMAINS` |
| P6.008 | OPEN | Remove browser snapshots and Playwright dumps from proof-source surface; preserve needed receipts in archive. | P6.006 | New snapshots are ignored; historical evidence remains accessible. | `BROWSER_DUMP_ACTIVE_SURFACE` |
| P6.009 | OPEN | Enforce output directory policy for scripts. | P6.006 | No script writes results into repo root. | `SCRIPT_ROOT_OUTPUT` |
| P6.010 | OPEN | Add front matter to archival docs: historical, superseded_by, not_source_of_truth. | P5.001 | Search tools can exclude archive by default. | `ARCHIVE_SOURCE_CONFUSION` |

### Phase P7 — public canonical route and release gate

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P7.001 | BLOCKED | Define `PUBLIC_CANONICAL` Lean entrypoint for corrected test class. | P0–P3 | Exact theorem statement and class are source-locked. | `PUBLIC_CANONICAL_CONTRACT_OPEN` |
| P7.002 | BLOCKED | Ensure canonical entrypoint imports no legacy/challenger modules. | P7.001, P3.007 | Import firewall green. | `PUBLIC_CANONICAL_IMPORT_CONTAMINATION` |
| P7.003 | BLOCKED | Print and review exact axiom profile. | P7.001 | No undocumented project assumption. | `PUBLIC_CANONICAL_AXIOM_PROFILE_UNACCEPTED` |
| P7.004 | BLOCKED | Build clean reproduction package. | P4, P7.001–P7.003 | Fresh Linux and Mac builds reproduce receipts. | `PUBLIC_REPRODUCTION_FAIL` |
| P7.005 | BLOCKED | Generate statement sheet and dependency graph. | P7.001–P7.004 | One self-contained reviewer packet. | `PUBLIC_REVIEW_PACKET_INCOMPLETE` |
| P7.006 | BLOCKED | Run adversarial semantic review. | P7.005 | Wrong-object, wrong-class, finite/global and circularity plants rejected. | `PUBLIC_SEMANTIC_REVIEW_FAIL` |
| P7.007 | BLOCKED | Owner gate `PX_RH_CLAIM`. | P7.006 | Explicit owner authorization only after all gates. | `PX_RH_CLAIM_NOT_AUTHORIZED` |

### Phase P8 — conditional repository extraction

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P8.001 | HOLD | Define stable `q3-discovery` schema package independent of live route paths. | P3.001, P5.002 | Versioned schema has compatibility tests. | `DISCOVERY_SCHEMA_NOT_STABLE` |
| P8.002 | HOLD | Build independent CLI/package boundary. | P8.001 | Tool runs against an exported snapshot without repository internals. | `DISCOVERY_API_NOT_INDEPENDENT` |
| P8.003 | HOLD | Run blinded historical holdout backtests. | P8.002 | Predictions frozen before reveal; no repair after reveal. | `DISCOVERY_HINDSIGHT_BIAS` |
| P8.004 | HOLD | Measure top-k gain, wrong-object escape, kill latency and maintenance cost. | P8.003 | Precommitted thresholds met. | `DISCOVERY_VALUE_NOT_SHOWN` |
| P8.005 | HOLD | Extract `q3-discovery` to a new repository/package. | P8.004 | Independent value and maintenance case are positive. | `PREMATURE_DISCOVERY_REPO` |
| P8.006 | HOLD | Inventory zero-import legacy archive candidate. | P1.004–P1.008 | No active code imports candidate files. | `LEGACY_ARCHIVE_HAS_ACTIVE_IMPORTS` |
| P8.007 | HOLD | Preserve history with filter/subtree migration plan and immutable source tag. | P8.006 | Commit provenance remains recoverable. | `LEGACY_HISTORY_LOSS` |
| P8.008 | HOLD | Extract read-only `chen_q3-legacy-archive`. | P8.007 | Main repo retains only pointers/manifests; archive is frozen. | `PREMATURE_LEGACY_REPO` |
| P8.009 | KILL | Split Route B into a new repo during Goal058. | none | Forbidden until same-family and live bus dependencies close. | `ROUTEB_LIVE_SPLIT_FORBIDDEN` |
| P8.010 | KILL | Split proof certificates from Lean consumers. | none | Forbidden; certificates stay atomically source-locked with consumers. | `CERTIFICATE_CONSUMER_SPLIT_FORBIDDEN` |

### Phase P9 — ongoing mathematical work during cleanup

| ID | Status | Action | Depends on | Acceptance test | Stop / failure code |
|---|---|---|---|---|---|
| P9.001 | OPEN | Continue current Route B theorem-sized transaction unchanged. | none | Cleanup does not change Goal058 objects, phase key or schedule. | `CLEANUP_MUTATED_LIVE_ROUTE` |
| P9.002 | OPEN | Keep Route B `CHALLENGER / NOT_RH`. | none | No route promotion in cleanup commits. | `CLEANUP_PROMOTED_ROUTE` |
| P9.003 | OPEN | Keep semantic cleanup and mathematical theorem work in separate commits. | none | One concern per commit and receipt. | `CLEANUP_THEOREM_COMMIT_MIXED` |
| P9.004 | OPEN | Do not mass-rename live Route B Lean modules. | none | Current imports and source locks remain stable. | `LIVE_MODULE_RENAME_CHURN` |
| P9.005 | OPEN | Require every new bridge to close more than it opens. | none | `CLOSES/OPENS` ledger passes supplier contract. | `BRIDGE_GROWTH_NO_PROGRESS` |
| P9.006 | OPEN | Keep current smallest mathematical gap named independently of repository cleanup. | none | Route verdict still names its own minimal missing identity. | `CLEANUP_HID_MATH_GAP` |

## 5. Execution order

```text
WAVE 0 — READ-ONLY PREFLIGHT
  P0.003–P0.006
  P1.001
  P2.001–P2.003
  P5.001
  P6.001, P6.006

WAVE 1 — HONESTY SURFACE
  P0.007–P0.010
  P1.002–P1.007
  P2.004–P2.007

WAVE 2 — ENFORCEMENT
  P3.001–P3.010
  P4.001–P4.012

WAVE 3 — STATE AND HYGIENE
  P5.002–P5.008
  P6.002–P6.010

WAVE 4 — PUBLIC CANONICAL ENTRY
  P7.001–P7.007

WAVE 5 — OPTIONAL PHYSICAL SPLITS
  P8.001–P8.008 only after their gates
```

Do not begin Wave 2 by moving files. Enforcement precedes relocation.

## STRONGEST ATTACK

### Attack A — monorepo boundaries will be ignored again

Correct. A prose boundary is useless. The selected route survives only if the import firewall, public axiom audit, state drift check and branch protection become required checks.

**Kill condition:** if the project cannot enforce these checks on `rh_clean`, then the monorepo decision is revoked and a minimal `chen_q3-proof-core` extraction becomes mandatory.

### Attack B — a new clean repository would immediately simplify the project

It would simplify the directory listing but not the dependency truth. To create a clean proof repository today, we must decide which definitions, axioms, certificates and theorem adapters are canonical. That is exactly the unresolved semantic classification. Doing the split first forces those decisions through copy operations without a checked import graph.

### Attack C — cleanup will stall live mathematics

The ledger explicitly forbids this. Route B keeps its paths, source locks, live bus and current theorem transaction. Cleanup starts with read-only inventories and separate commits.

## FINAL PROPOSAL

Selected route:

\[
oxed{	ext{hard-boundary proof monorepo now; conditional tooling/archive split later}}
\]

Registered prediction:

```text
The first read-only inventory will show that a small number of public/default
exports and generated status surfaces create most of the semantic risk; the
live Route B theorem graph itself does not require a repository split.
```

Cheapest decisive test:

```text
Build the exact public-export dependency/axiom/test-class inventory without
editing source. If the public canonical slice cannot be separated from legacy
by import rules, revoke this decision and select proof-core extraction.
```

Likeliest failure point:

```text
compatibility dependencies on Q3.Main and Q3.Axioms are wider than the current
control documents imply.
```

Response:

```text
keep a deprecated compatibility package, but do not let it remain the default
public entrypoint.
```

## CODEX DIRECTIVE

```text
TASK_ID: REPOSITORY_SEMANTIC_QUARANTINE_PREFLIGHT

MODE:
  READ_ONLY

BASELINE:
  repo: Malaeu/chen_q3
  branch: rh_clean
  start_from_head: 809b776bd628c39a5e99dc54e9720a4e7a4bd0a0_or_newer_exactly_recorded

OBJECTIVE:
  Produce the exact inventory required by Wave 0. Do not edit Lean, docs,
  control files, state files, or GitHub settings.

READ_FIRST:
  README.md
  q3.lean.aristotle/Q3/Main.lean
  q3.lean.aristotle/Q3/Axioms.lean
  q3.lean.aristotle/Q3/CheckAxioms.lean
  q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_REPOSITORY_TOPOLOGY_SEMANTIC_QUARANTINE_AND_TODO_2026-08-27.md

REQUIRED_OUTPUT:
  1. Every RH-facing theorem/export reachable from Q3.Main and other default entrypoints.
  2. Exact Lean statement and exact source path.
  3. Exact dependency graph and reverse dependencies.
  4. Exact #print axioms output for every public theorem.
  5. Exact test class and source object for every theorem.
  6. Proposed module class:
       CORE_SHARED | PUBLIC_CANONICAL | CHALLENGER |
       CONDITIONAL_COMPILED | LEGACY | EXPERIMENT | ARCHIVE.
  7. All consumers of c_arch_pos and c_star_le_c_arch.
  8. Every file claiming current status, active route, axiom count or next action.
  9. Every executable absolute path and every root-level generated/draft artifact.
  10. A zero-edit migration ordering that preserves compilation.

MANDATORY_PLANTS:
  P1_PUBLIC_IMPORTS_LEGACY:
    confirm the future firewall would reject a public module importing legacy.
  P2_WRONG_TEST_CLASS_SAME_RH_TYPE:
    distinguish two theorems ending in Q3.RH but consuming different test classes.
  P3_TORUS_FLOOR_AS_POINTWISE_FLOOR:
    reject c_star -> c_arch without an explicit theorem crosswalk.
  P4_COMMENT_AS_FIREWALL:
    reject the idea that a warning comment changes namespace/public status.

FORBIDDEN:
  no file edits
  no renames
  no new repository
  no branch protection mutation
  no theorem weakening
  no replacement of #print axioms by source comments
  no raw file-count conclusions without dependency reachability

SUCCESS_CODE:
  REPOSITORY_SEMANTIC_QUARANTINE_INVENTORY_COMPLETE

FAILURE_CODE:
  REPOSITORY_SEMANTIC_QUARANTINE_INVENTORY_INCOMPLETE

REPORT:
  Return one machine-readable YAML header and a concise evidence table.
  Name the smallest executable first cleanup transaction.
```

## META CLOSEOUT

**Что стало меньше?**

Вопрос `monorepo или несколько repo` сжат до одного измеримого решения: сначала проверить, отделяется ли public canonical slice import firewall-ом. Physical split больше не является туманным предпочтением.

**Что убито?**

```text
split now because the root looks messy;
move Route B during a live same-family phase;
separate certificates from their Lean consumers;
assume that comments quarantine a theorem;
assume that repository count creates semantic safety.
```

**Что нельзя повторять?**

```text
mass git mv before import graph;
new clean repo populated by hand-copying "probably canonical" files;
public RH name with project assumptions and wrong test class;
torus-symbol floor used as pointwise a_star floor without theorem;
manual status duplicated across README, monitor, queue and code comments.
```

**Текущий smallest named gap для cleanup:**

```text
LEGACY_EXPORT_SEMANTIC_QUARANTINE_PREFLIGHT
```

**Следующий дешёвый decisive test:**

```text
exact public-export dependency + axiom + test-class inventory.
```

**Судьба зарегистрированных predictions:**

```text
UNTESTED — registered in this verdict before the preflight.
```

**Memory entry:**

```yaml
iteration: repository_topology_2026_08_27
  target: eliminate semantic contamination before any public claim
  status: PROGRESS
  failed_strategy: repository_count_as_architecture
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: LEGACY_EXPORT_SEMANTIC_QUARANTINE_PREFLIGHT
  invariant_learned: source, certificate, consumer and same-family crosswalk remain atomically pinned
  forbidden_future_move: split Route B or certificates during the live Goal058 phase
  next_decisive_test: public export dependency/axiom/test-class inventory
```
