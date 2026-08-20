# Blueprint — Operator Methods for RH (skeleton, generated from assembly)

*Generated 2026-08-20 by blueprint_gen.py — DO NOT edit by hand:*
*regenerate after any assembly change. Green = kernel-proved rope,*
*red = hanging rope with its measured hole. Roof and Hurwitz transfer are concrete.*

## §0 Main Theorem and definitional faithfulness  ✅ (proved interface)

- `Q3.RH` := ∀ s, riemannZeta s = 0 → 0 < re s < 1 → re s = 1/2  (`Q3/Basic/Defs.lean:177`, Mathlib zeta)
- Bridge: `rh_iff_centeredXi_zeros_real` (`ClassicalXiInterface.lean:108`) ✅

## Правило замыкания (владельцу): закрой все 🔴 — и крыша встанет

- обязательны в ЛЮБОМ случае: G5 (1) + G6 (7);
- дальше ОДНО из двух: G3+G3p (5) ЛИБО дорога 058 (5);
- сумма = 13 классикой / 13 через 058; каждый закрытый 🔴 = перегенерация = позеленел;
- все 🔴 закрыты => входы rh_of_canonical_strip_slots поданы => Q3.RH
  через доказанный iff. Оговорка K6: 🔴 может оказаться стеной — kill
  тоже результат.

## §1 Roof  ✅

- `rh_of_canonical_strip_slots` (`CanonicalRHRouteSkeleton.lean:145`) — conditional, hole-free ✅
- Hurwitz transfer: `ZeroEscapeLogic` + `MontelNormalFamilies` ✅

## §G2 Pillar G2 — simple even ground (validation cell)  — 15/15 ropes fastened

- ✅ **1.** K эрмитова (симметричная) — `\lean{ccmWeilMatFinite_transpose_eq}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean`
  - `theorem ccmWeilMatFinite_transpose_eq (mProject N : ℕ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N) :
    (ccmWeilMatFinite mProject N).transpose =
      ccmWeilMatFinite mProject N`
- ✅ **2.** поблочная симметрия tau = W02 - WR - Prime — `\lean{ccmW02Entry_symm + ccmWREntry_symm + ccmPrimeEntryN1_symm}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`
- ✅ **3.** J инволюция с JKJ = K — `\lean{ccmWeilMatFinite_centrosymmetric}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean`
  - `theorem ccmWeilMatFinite_centrosymmetric (mProject N : ℕ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (i j : CCMModeFinite N) :
    ccmWeilMatFinite mProject N
        (ccmNegFinite N i) (ccmNegFinite N j) =
      ccmWe`
- ✅ **4.** оператор коммутирует с отражением — `\lean{ccmWeilOpFinite_commutes_reflection}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`
  - `theorem ccmWeilOpFinite_commutes_reflection (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    (ccmReflectionEndFinite N).comp (ccmWeilOpFinite mProject N) =
      (ccmWeilOpFinite mProject N).comp (ccmReflectionEnd`
- ✅ **5.** переход R -> C — `\lean{realPosDef_map_complex}` `q3.lean.aristotle/Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrumRealConsumer.lean`
  - `theorem realPosDef_map_complex {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Q.PosDef) :
    (Q.map (algebraMap ℝ ℂ)).PosDef`
- ✅ **6.** G PosDef — `\lean{Matrix.PosDef.one (Mathlib)}` `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
- ✅ **7.** сертификат K - beta*G + tau*(Gq)(Gq)^H >= 0 — `\lean{ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean`
  - `theorem ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (hbottom : ∀ x : CCMModeFinite N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mu`
- ☑ (validation-only, off critical path) **8.** рэлеевская нижняя граница epsilon — `\lean{Arb interval LDL @ 240 dps, все 121+120 пивотов положительны}` `docs/routeB_bus/phase1_results/ccm_control_cell_m13_N120_interval.json`
- ✅ **9.** ранг-один поправка tau*(Gq)(Gq)^H — `\lean{ccmShiftedWeil_rankOneCorrection_kernel_and_weightedSymmetric}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilShiftedRankOne.lean`
  - `theorem ccmShiftedWeil_rankOneCorrection_kernel_and_weightedSymmetric (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProjec`
- ✅ **10.** q: J-чётный, нормированный eta*q = 1 — `\lean{exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilEtaNonzero.lean`
  - `theorem exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector (mProject N : ℕ)
    (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (hxi0 : xi ≠ 0)
    (heig :
    `
- ✅ **11.** чётность собственного вектора — `\lean{ccmEigenvector_even_of_simple_eigenspace_and_normalized}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`
  - `theorem ccmEigenvector_even_of_simple_eigenspace_and_normalized (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) x`
- ✅ **12.** eta*xi != 0 (нормируемость) — `\lean{ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilEtaNonzero.lean`
  - `theorem ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector (mProject N : ℕ)
    (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject)
    (hN : 1 ≤ N)
    (hxi0 : xi ≠ 0)
    (heig :
      Matrix.m`
- ☑ (validation-only, off critical path) **13.** a = <q,Kq> — `\lean{a = 4.71998e-59 (строгий интервал Arb)}` `docs/routeB_bus/phase1_results/ccm_control_cell_m13_N120_interval.json`
- ☑ (validation-only, off critical path) **14.** beta с a < beta — `\lean{beta = 1e-56, beta - a = 9.95280e-57 > 0}` `docs/routeB_bus/phase1_results/ccm_control_cell_m13_N120_interval.json`
- ✅ **15.** простота нижнего собственного подпространства — `\lean{simplicity_clause}` `q3.lean.aristotle/Q3/Proofs/RouteB/H2aPenaltyCoercivity.lean`
  - `theorem simplicity_clause {G K : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β) :
    ∀ `

## §G3 Pillar G3 — real zeros bridge (Theorem 5.10)  — 12/15 ropes fastened

- 🔴 **1.** вещественность нулей для CCM-семьи  *[MISMATCH]*
  - hole: доказана для КОНКРЕТНОЙ семьи; слот сформулирован для абстрактной C.Pstar.family
- ✅ **2.** determinant identity — `\lean{zerosRealOn_of_hermitian_charpoly_mul (charpoly в факторизации)}` `q3.lean.aristotle/Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean`
- ✅ **3.** modified-Hilbert self-adjoint descent — `\lean{posDefSelfAdjoint_exists_hermitian}` `q3.lean.aristotle/Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean`
  - `theorem posDefSelfAdjoint_exists_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℂ) (hQ : Q.PosDef)
    (hSA : Q * D = Dᴴ * Q) :
    ∃ H : Matrix n n ℂ, H.IsHermitian ∧ H.charpoly = D.charpoly`
- ✅ **4.** complement/lattice factor — `\lean{realFactor с гипотезой ZerosRealOn}` `q3.lean.aristotle/Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean`
- ✅ **5.** nonvanishing phase — `\lean{hunit: forall z, unit z != 0}` `q3.lean.aristotle/Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean`
- 🔴 **6.** H2aAt как конкретный предикат  *[GAP]*
  - hole: свободный параметр Index -> Prop; должен упаковать ШЕСТЬ гипотез поставщика: heig, hnormalized, hbottom, hsimple, базис b, hm/hN. hxiEven ИСКЛЮЧЁН — выводится, см. шаг 11.
- ✅ **7.** базис фактора по ядру сдвинутой формы — `\lean{Module.finBasis (Mathlib) — базис строится, не постулируется}` `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- ✅ **8.** согласование простоты: eigenspace vs обобщённая задача (K,G) — `\lean{finrank_eigenspace_eq_one_of_geig_simple (доказана, вне репы)}` `scratchpad/cand_b2.lean`
- ✅ **9.** предельный переход сохраняет вещественность — `\lean{zerosRealOn_of_zerosApproachOn}` `q3.lean.aristotle/Q3/Proofs/RouteB/ZeroEscapeLogic.lean`
  - `theorem zerosRealOn_of_zerosApproachOn (S : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, ZerosRealOn Set.univ (F n))
    (htransfer : ZerosApproachOn S F f) :
    ZerosRealOn S f`
- ✅ **10.** конечное -> бесконечное с живым якорем — `\lean{montel_anchor_nonzero_limit}` `q3.lean.aristotle/Q3/Proofs/RouteB/MontelNormalFamilies.lean`
  - `theorem montel_anchor_nonzero_limit (f : ℕ → ℂ → ℂ) (a c : ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hA : ∀ n, f n a = c) (hc : c ≠ 0) :
   `
- ✅ **11.** выход в классическую RH — `\lean{rh_iff_centeredXi_zeros_real}` `q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean`
  - `theorem rh_iff_centeredXi_zeros_real  : Q3.RH ↔ CenteredXiZerosReal`
- ✅ **12.** ker сдвинутой формы <-> eigenspace (обычная задача) — `\lean{ccmShiftedWeilOpFinite_ker_eq_eigenspace}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean`
  - `theorem ccmShiftedWeilOpFinite_ker_eq_eigenspace (mProject N : ℕ) (epsilon : ℝ) :
    LinearMap.ker (ccmShiftedWeilOpFinite mProject N epsilon) =
      (ccmWeilOpFinite mProject N).eigenspace epsilon`
- ✅ **13.** Rayleigh-граница снизу -> PosSemidef сдвинутой матрицы — `\lean{ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean`
  - `theorem ccmShiftedWeilMatFinite_posSemidef_of_bottomRayleigh (mProject N : ℕ) (epsilon : ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (hbottom : ∀ x : CCMModeFinite N → ℝ,
      epsilon * (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mu`
- ✅ **14.** чётность собственного вектора (hxiEven) — `\lean{ccmEigenvector_even_of_simple_eigenspace_and_normalized}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`
  - `theorem ccmEigenvector_even_of_simple_eigenspace_and_normalized (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (heig : Matrix.mulVec (ccmWeilMatFinite mProject N) x`
- 🔴 **15.** нормирующий множитель c_N и сходимость F_N -> centeredXi  *[GAP]*
  - hole: sourceLagrangePolynomial = sum_k xi(k) * prod_{j!=k}(lam j - X): при 2N+1 модах произведение из 2N сомножителей порядка N, рост ~N^(2N). centeredXi конечна. Без нормировки c_N сходимость невозможна в 

## §G3p Pillar G3 — CvS engine port (value crosswalk + assembly)  — 0/2 ropes fastened

- 🔴 **1.** P1: GROUND_CANONICAL_PSTAR_VALUE_CROSSWALK — ground-значная CanonicalApproximation ЛИБО точное равенство selected-функции и (ненулевой множитель)×proposition59CCMTransform ground-строки  *[GAP]*
  - hole: вердикт батча 19.08: CvS подходит ПО ТИПУ, не по значению (trial против ground); постулировать запрещено
- 🔴 **2.** P2: Theorem510RealZeroBridge_of_groundP59 — сборка моста из CvS-движка  *[GAP]*
  - hole: сборка после P1; CvS-доказательство НЕ реформализуется

## §G5 Pillar G5 — uniform critical moment budget  — 0/1 ropes fastened

- 🔴 **1.** равномерный по k моментный бюджет: ∃C ∀k centeredCriticalMoment ≤ C·|rawFplus 0|  *[GAP]*
  - hole: мера ядром 19.08 (apply?): единственный аналитический канат G5; PairCofinal приезжает полем пакета D (шаг 25 GOAL057)

## §G6 Pillar G6 — S2 wall: continuum numerator + edge  — 21/28 ropes fastened

- ✅ **0.** СТАРТ: проба не является источниковым объектом — `\lean{аудит GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_AUDIT_2026-08-07}` `docs/routeB_bus/GOAL057_ACTUAL_NUMERATOR_SOURCE_TARGET_AUDIT_2026-08-07.md`
- ✅ **1.** B1: привязка источникового ряда коэффициентов — `\lean{D0PstarCCMFiniteSourceResidual}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean`
- ✅ **2.** B2: перенос в операторный носитель (Riesz) — `\lean{D0PstarCCMFiniteRieszOperator}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean`
- ✅ **3.** B3.0A: формула Фурье для мод — `\lean{D0PstarVModeFourierFormula}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeFourierFormula.lean`
- ✅ **4.** B3.0B1: взвешенная L2-норма мод — `\lean{D0PstarVModeLogWeightedL2}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean`
- ✅ **5.** B3.0B2: доминирование точного арх. символа — `\lean{D0PstarExactArchSymbolLogDomination}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean`
- ✅ **6.** B3.0B3: точный арх. символ в взвешенном L2 — `\lean{D0PstarExactArchSymbolWeightedModeL2}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolWeightedModeL2.lean`
- ✅ **7.** B3.0C: интегрируемость спаривания мод — `\lean{D0PstarSourceArchModePairingIntegrable}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingIntegrable.lean`
- ✅ **8.** B3.0D: эрмитовость ядра спаривания — `\lean{D0PstarSourceArchModePairingKernel}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean`
- ✅ **9.** B3.0E: crosswalk CCM <-> WR (E1,E2,E3,E4A,E4B1,E4B2,E4C) — `\lean{закрыто 08.08 16:47 'Close all-mode CCM-WR crosswalk'}` ``
- ✅ **10.** B3.0F: подъём формы CCM-WR до матрицы — `\lean{закрыто 08.08 18:03 'Close finite CCM-WR form lift'}` ``
- ✅ **11.** B3.0G: источниковое W02-спаривание — `\lean{sourceW02ModePairing_eq_ccmW02Entry}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02ModePairing.lean`
  - `theorem sourceW02ModePairing_eq_ccmW02Entry (i : PairIndex) (n r : ℤ) :
    sourceW02ModePairing i n r =
      (Q3.RouteB.ccmW02Entry (L_m i) n r : ℂ)`
- 🔴 **12.** обитатель CCMLemma73PreAnchorPort selectedFerrersPreAnchorData (НЕ forall D — C04/C10-kill): P.convergence ТЕОРЕМОЙ (бумага 2511.22755)  *[GAP]*
  - hole: РАЗЛОЖЕН НА 9 ЭТАЖЕЙ (вердикт FLOORS 20.08, REQ-D): L73.0 provenance (ждёт Codex, 1/10) → L73.1 sourceScale из нормировки I4h0-I0h4, НЕ из вывода (3/10) → L73.2 Lemma-7.2 rate O(λ^-2) — ГЛАВНАЯ СТЕНА 
- 🔴 **13.** равномерная нижняя оценка нормы пробной функции (даёт SelectedTrialNormalizerBounded)  *[OWNER_DATA]*
  - hole: ТОЧНАЯ ФОРМУЛИРОВКА, установлено чтением 2026-08-08. sTrial_m_N = ||gTrial_m_N||^{-1} (D0KTrialStage3.lean:39). TrialNonzero даёт ПОТОЧЕЧНО: forall k, 0 < ||gTrial_m_N(k)||. Для SelectedTrialNormalize
- 🔴 **14.** N2: SelectedNormalizedGalerkinMellinCompactDecay (compact-open, НЕ Hilbert-norm)  *[GAP]*
  - hole: разложена на этажи N2_0..N2_5 вердиктом 20.08; MINIMAL_MISSING_IDENTITY = source-scaled Mellin projection tail rate; исполнение ДО обитателей D и порта запрещено
- 🔴 **15.** SelectedPhysicalFourierEnergyControl — суммируемость и ограниченность энергий  *[OWNER_DATA]*
  - hole: Предикат-конъюнкция, объявлен PFE:66. (а) для каждого k ряд sum_n physicalFourierWeight i n * ||physicalFourierCoefficient i (gTrial_m ...) n||^2 суммируем; (б) IsBoundedUnder (<=) atTop (norm . selec
- 🔴 **16.** SelectedPhysicalBandwidthCofinal — полоса уходит в бесконечность  *[OWNER_DATA]*
  - hole: Предикат: Tendsto (fun k => physicalFourierBandwidth (selectedPairIndex S k)) atTop atTop, объявлен PFE:81. Утверждение о ВЫБОРЕ пути (selectedPairIndex), а не о математике — кандидат на дешёвое закры
- ✅ **17.** B3.0H: подъём W02 до конечной формы — `\lean{D0PstarSourceW02FiniteFormCCMW02Crosswalk}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean`
- ✅ **18.** B3.0I: источниковое prime-спаривание — `\lean{D0PstarSourcePrimeModePairing}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean`
- ✅ **19.** B3.0J: подъём prime до конечной формы — `\lean{D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk.lean`
- ✅ **20.** B3.0K: ПОЛНАЯ форма Вейля = матричная форма CCM — `\lean{sourceWeilFiniteForm_eq_ccmWeilMatrixForm}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilFiniteFormCCMWeilCrosswalk.lean`
  - `theorem sourceWeilFiniteForm_eq_ccmWeilMatrixForm (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    ((∑ j, ∑ k,
        star (c j) *
          sourceW02ModePairing i
            (ccmModeFinite i.N j)
            (c`
- ✅ **21.** B3.0L: изометрия Фурье в L2 — `\lean{D0PstarSourceLogWindowFourierL2Isometry}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierL2Isometry.lean`
- ✅ **22.** B3.0M: конечный Фурье-реестр — `\lean{D0PstarSourceWeilFiniteFourierLedger}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilFiniteFourierLedger.lean`
- ✅ **23.** B3.0N: РАВНОМЕРНАЯ нижняя оценка арх. символа — `\lean{sourceArchimedeanMultiplier_add_explicitShift_nonneg}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExactArchSymbolLowerBound.lean`
  - `theorem sourceArchimedeanMultiplier_add_explicitShift_nonneg (t : ℝ) :
    0 ≤ sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6)`
- ✅ **24.** B3.0O: сдвинутый арх. sqrt-вес — `\lean{D0PstarShiftedArchSqrtWeight}` `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchSqrtWeight.lean`
- ✅ **25.** обитатель SelectedProlatePreAnchorData (пакет: index,pair,кофинальности,lambda_eq,MemLp) — `\lean{selectedFerrersPreAnchorData (def, kernel-green 20.08, Linux-тело за Codex)}` `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean`
- 🔴 **26.** N3: same-family locally-uniform crosswalk D0Pstar->Muntz  *[GAP]*
  - hole: сборка (вердикт G6-узлов 19.08); комбинирует N1-композер с N2
- 🔴 **27.** N4: SlotS2 из фиксированного selected-предела  *[GAP]*
  - hole: строгая потребительская сборка; квантификация по всем ClusterData

## §058 Route 058 — ground diagonal to Xi (replaces G2+G3)  — 3/8 ropes fastened

- 🔴 **0.** точный объект, координата и нормировка зафиксированы  *[GAP]*
  - hole: G0 OPEN_PARTIAL. Целые узлы источника и полюсы 2*pi*k/L определены; кофинальное расписание (m_j, N_j) и точная невырожденная нормировка не закреплены.
- 🔴 **1.** кофинальный конечный simple-even ground-пакет  *[GAP]*
  - hole: G1 OPEN_MAIN_SPECTRAL_FRONT. Нужен пакет (epsilon_j, xi_j, heig, hbottom, hsimple, hnormalized) на кофинальном пути. Чётность отдельно НЕ поставляется — её выводит обёртка ..._simple_normalized. Шесть
- ✅ **2.** вещественность нулей лагранжева многочлена ground-строки — `\lean{ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized}` `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`
  - `theorem ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mProject N : ℕ) (epsilon : ℝ)
    (xi : CCMModeFinite N → ℝ)
    (hm : 2 ≤ mProject`
- ✅ **3.** перенос МНОЖЕСТВА нулей с многочлена на преобразование Proposition-5.9 — `\lean{Proposition59GroundLagrangeZeroSetBridge}` `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean`
  - `theorem Proposition59GroundLagrangeZeroSetBridge {ι : Type*} [Fintype ι] [DecidableEq ι] (mProject N : ℕ) (epsilon : ℝ) (xi : CCMModeFinite N → ℝ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) (heig : Matrix.mulVec (ccmWeilMatFinite `
- 🔴 **4.** та же F_j отслеживает projected prolate trial локально равномерно  *[GAP]*
  - hole: G3 MAIN_WALL. Главная стена маршрута. Переносится СХОДИМОСТЬ на ground-семью, не вещественность на trial: вещественность неустойчива к возмущению. Убитое решение: exact ground equals trial.
- 🔴 **5.** projected trial отслеживает continuum CCM trial  *[GAP]*
  - hole: G3c. Проекция конечного среза на континуальный пробник CCM.
- 🔴 **6.** CCM Lemma 7.3: континуальное trial-преобразование сходится к Xi  *[GAP]*
  - hole: G4 PAPER_PROVED_PROJECT_IMPORT_OPEN. Это тот же объект, что doc-alias hermfact1: статус PAPER_PROVED, Lean-порт OPEN. Локально равномерно на замкнутых подполосах.
- ✅ **7.** zero-escape: вещественные нули аппроксимантов запрещают невещественные у предела — `\lean{rh_of_canonical_strip_slots · ZerosApproachOn · ClassicalXiInterface}` `q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean`

## §A Attribution (from provenance counter)

- our Lean / Mathlib / data per pillar — see session_start ОПОРЫ И КАНАТЫ;
- paper engines (Connes, CvS): blueprints, not premises — port status per verdicts.
