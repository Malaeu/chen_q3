# D0.7e.5a — independent WPrime/ZEO consumer source request

Status: `EXTERNAL_SOURCE_OR_AUTHORITY_REQUIRED / ACTIVE_BLOCKER / NOT_RH`

Primary stop: `D0_7E_WPRIME_CONSUMER_MISSING`.

Owner R1-R5 is now physically ratified. The remaining input is mathematical
and provenance-bearing, not another DAG choice.

Supply one physical, source-pinned artifact that answers all of the following:

1. What is the independently defined exact approximant consumed by the
   historical `WPrime` statement (`FZeo`, `F_Zeo`, or another exact name)?
2. What is the exact definition of `WPrime` before the desired inequality is
   used?
3. Which scalar is its `b` argument: the amplitude ratio
   `bCal=bDet=Fhat(0)/Xi(0)`, the normalizing multiplier `bCal^(-1)`, or a third
   scalar with a proved crosswalk?
4. On which exact nonzero domain is that orientation legal? The current
   finite audit proves only
   `CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero` and proves
   that `TrialNonzero` alone is insufficient.
5. Give the exact source path, theorem/equation locator, and immutable hash or
   owner-ratified new-definition classification.

Acceptance firewalls:

- defining `WPrime` by the desired right-hand side is `D0_7E_TAUTOLOGY`;
- aliasing `bCal` with `bCal^(-1)` is
  `D0_7E_BCAL_BZEO_ALIAS_CONFLICT`;
- Contract v2, the alpha-demand audit, and FIT_NOT_LAW diagnostics are target
  or diagnostic sources, not an independent consumer proof;
- H3c/H4 theorems may not be imported into D0;
- no `alpha :=`, `DeltaE :=`, filter choice, `kappa`, or `N(lambda)` selector
  may be minted in this leaf;
- no Bus 010 may be created by Codex.

If no such artifact exists, return the explicit verdict
`NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE`. The canonical leaf then
remains blocked rather than being closed by bookkeeping.
