# SOURCE RECORD — GOAL058 selected Ferrers finite asset bank (Track 2)

```yaml
SUPPLIER_CONTRACT: v7
DATE: 2026-08-27
BODY: Linux (Claude)
TASK_ID: GOAL058_REENTRY_GATE_A_DUAL_TRACK_EXECUTION / TRACK2_PHASE1
PARENT_VERDICT: 071d3eb0
CONTRACT: d8e4bbe0 (TRACK2_ARISTOTLE_ASSET_BANKING, заморожен)
FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteAssetBank.lean
GIT_BLOB: cd606d5ffe2400d2c41ad9221baccf6080bb34a4
SHA256: 5de1e7c780161492ab270be52eb62f0b7d18e78e024957547245fe6fecdb0922
LINES: 808
GATE:
  lake_env_lean: EXIT 0
  lake_build_module: EXIT 0 (7747 jobs)
  lake_build_full: EXIT 0 (7817 jobs)
  q3_check: ok
  hole_scan: 0
  axioms_all_public: [propext, Classical.choice, Quot.sound]
PUBLIC_SURFACE_RESTRICTIONS_HONORED:
  Tendsto: 0
  Eventually: 0
  rate_hypotheses: 0
  cofinal_conclusions: 0
  new_analytic_suppliers: 0
  aliases_of_existing_nodes: 0
CLOSES:
  - NODE_A: trialGraphOperator (def) + posDef (A1) + точное тождество
    C·(ξ−d·q) = −d·r (A2, без Hermitian/floor-гипотез) + единственность и
    буквальная inverse-форма C⁻¹·(d·r) = d·q − ξ (A3) + скалярный транспорт
    трансформы (A4: proposition59RawTransform_smul)
  - NODE_B: диагонально-резольвентное тождество (n−ζ(z))·h_n(z) = c(z) на
    ВСЁМ ℂ, решётка включена кейс-анализом (B1) + комплексификация полного
    ранг-2 коммутатора (B2a) + ЦЕЛАЯ moved-action формула без обратных
    (B2b: (D−w)((M−a)κ) = s(Mη − aη) + (ηᵀκ)β − (βᵀκ)η)
  - NODE_C: penalty-конверты, identity- и Gram-метрика (C1, с Gram-CS через
    G-ортогональный дефект) + точное расщепление квадратичной формы
    завершением квадрата в C_b-метрике (C2: penalty_quadratic_split —
    Schur-механизм s_min)
  - NODE_D1: centering_factor_bound из якорного тождества и inv-log пола
OPENS: []
DEFERRED:
  - NODE_D2 (kernelL2 компакт-конверт): sin/решёточные оценки — вес на
    порядок выше остального банка; заявлен отдельным bounded-узлом
IMPORT_NOT_DUPLICATE:
  - selectedFerrersTrackedGroundTransform_realZeros_... (real zeros)
  - sourceOrderedCCMRawTransform_sub_projection_le (P59 CS-цепь)
  - preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0 (якорь для D1)
  - ccmWeilMatFinite_commutator (вещественный коммутатор для B2a)
  - selectedFerrersFiniteCCMResidual_orthogonal (⟨q,r⟩=0)
```

Семантические границы: generic-теоремы сформулированы на абстрактном
конечном носителе с литеральными гипотезами в формах диска (star-first,
floor-предикат в точной форме complexTrialComplementFloor, penalty-cert в
точной форме H2aPenalty); литеральные инстанцирования — чистая подстановка
существующих объектов. B1/B2b не содержат резольвентных записей — целые
тождества, компакты через полюса покрыты по построению.
