1. Does k2_odd set mu2? [YES; parity(xi2)=-1.0000000000000002; overlaps={'xi1_k1': 0.9999999980715731, 'xi2_k2_even': 6.442327039079938e-16, 'xi2_k2_odd': 0.9999999950206858}; slopes=-310.01068766594295 +/- 9.337151006864415]
2. Tail: nu >= lambda3_G + margin? [NO; margin=-4.538284247347875e-15]
3. W_actual decay slope: [other; value 312.2478992398691 +/- 10.69108075669377]

# Route B TwoLevelSpectralLadder Pilot Report

Status: NOT a proof of RH. Diagnostic Route B/G4 numerical falsifier only.

## Verdict
FAILURE_CODE: N_LIMIT_NOT_STABLE

## Files searched and definitions used

- Search log: `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/definition_search.log`.
- No executable repo implementation of `QW_lambda`, prolate packet, E-map, `k_lambda`, or `b_lambda` was used.
- Local source formulas used: `q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md` (arXiv:2511.22755), especially Sections 2.2, 3.1, 4.1-4.3, and 5.1.
- Implementation file: `ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_ladder_pilot.py`.

## Conventions

- `L = 2*log(lambda)`, basis indices are `n=-N..N`, and `T=QW_lambda^N` is assembled as `W02 - WR - WP`.
- `WR` uses the Prop. 4.2 decomposed coefficients `alpha_L`, `beta_L`, `gamma_L`; `Phi(z,2,a)` is evaluated by its fast `|z|<1` series.
- `WP` sums prime powers `1 < k <= exp(L)` with weight `Lambda(k)*k^(-1/2)`.
- Packet vectors are built from the MATH SPEC zero-integral prolate combinations; `b` is the direct quadrature norm of `E(g04)` and is not fitted.
- Numerical evidence only: no RH claim and no zero-side matching.

## Calibration log

```json
{
  "N": 20,
  "checks": {
    "C1": {
      "pairs": [
        {
          "closed": "0.10081797847626570075554387649910458380210099476388101304167252425114476537598795",
          "direct": "0.10081797847626570075554387649910458380202392647307145144435182128869045135637737",
          "m": 0,
          "n": 0,
          "rel_error": "7.70682908095615973207029624543140196105817352605878810889826510994323382636755e-41"
        },
        {
          "closed": "-0.019941260846673573390585317500573512911825497554805641695011745754368356604412931",
          "direct": "-0.019941260846673573390585317500573512911955125423347262487906495662196974826506116",
          "m": 2,
          "n": 1,
          "rel_error": "1.2962786854162079289474990782861822209318525517028274794563796783175406646602111e-40"
        }
      ],
      "pass": true,
      "threshold": "1e-8"
    },
    "C2": {
      "max_error": "0.0",
      "pairs": [
        {
          "error": "0.0",
          "m": 0,
          "n": 0,
          "tau": "0.10081797847626570075554387649910458380210099476388101304167252425114476537598795",
          "tau_reflected": "0.10081797847626570075554387649910458380210099476388101304167252425114476537598795"
        },
        {
          "error": "0.0",
          "m": 2,
          "n": 1,
          "tau": "-0.019941260846673573390585317500573512911825497554805641695011745754368356604412931",
          "tau_reflected": "-0.019941260846673573390585317500573512911825497554805641695011745754368356604412931"
        },
        {
          "error": "0.0",
          "m": -1,
          "n": 2,
          "tau": "0.067080943474975136781835337957353949072222953771688439757048604017950502348179448",
          "tau_reflected": "0.067080943474975136781835337957353949072222953771688439757048604017950502348179448"
        },
        {
          "error": "0.0",
          "m": 3,
          "n": 3,
          "tau": "1.4408801483692453798540157220340318425565554177600145697355328340135149749824491",
          "tau_reflected": "1.4408801483692453798540157220340318425565554177600145697355328340135149749824491"
        },
        {
          "error": "0.0",
          "m": 4,
          "n": -2,
          "tau": "0.06873586932726299946228903954849743984026917148393411983588733395501398589172764",
          "tau_reflected": "0.06873586932726299946228903954849743984026917148393411983588733395501398589172764"
        }
      ],
      "pass": true,
      "threshold": "1e-40"
    },
    "C3": {
      "pairs": [
        {
          "m": 0,
          "n": 0,
          "planted_rel_error": "0.00029048870864854522302380973782598585930792797395433117960484313125796740248986384"
        },
        {
          "m": 2,
          "n": 1,
          "planted_rel_error": "0.000056251680377941665428072937519830132288827715919196192248253857538300641987442345"
        }
      ],
      "pass": true
    },
    "C4": {
      "N": 20,
      "dps": 133,
      "dps_plus_80": 213,
      "lambda": "1.5",
      "mu1_dps": "0.00014650259148478903223622143876583282481252439873983825797019266741611348966342488",
      "mu1_dps_plus_80": "0.00014650259148478903223622143876583282481252439873983825797019266741611497643380329",
      "pass": true,
      "rel_error": "1.4867703784158788198107039597001046310528889473132924575010052987137431002028313e-72",
      "threshold": "1e-30"
    }
  },
  "dps": 133,
  "elapsed_s": 144.62045907974243,
  "lambda": "1.5"
}
```

## N-stabilization table (lambda=sqrt(14))

```json
{
  "drift_90_to_120": {
    "Delta": 0.20032990049494165,
    "W_actual": 0.5385315714983357,
    "mu1": 0.26194553305801327,
    "mu2": 0.2003352930115277,
    "nu": 0.32354937080926677
  },
  "lambda_sq": 14,
  "pass": false
}
```

## Full ladder table

- lambda=sqrt(12), N=60, dps=186, elapsed_s=32.87766695022583, mu1=9.1907269287163904361908775088869630586991323393353422236510041274444146786534318e-54, mu2=7.1125967928050143683181380496449564780379788561303581206311307212803157185972505e-50, Delta=7.1116777201121427292745189618940677817321089428964245864087656208675712771293852e-50, nu=-1.6593594110058074e-15, W_actual=141898716690166233033442562009287357.28391491594861322458875916247386156986105507, json=`out/lambda_sq_12_N_60.json`
- lambda=sqrt(12), N=90, dps=186, elapsed_s=101.87732100486755, mu1=5.880655557157496495092059786419257732697063160263222308137631832968559170799945e-54, mu2=4.4562983985917311517476017726294859186960532478669254933242377795512787313660565e-50, Delta=4.4557103330360154020980925666508439929227835415508991710934240163679818754489765e-50, nu=-3.3932967503757214e-15, W_actual=632869213004451784252885158281605085.94964904408719295559778837701227024817200028, json=`out/lambda_sq_12_N_90.json`
- lambda=sqrt(12), N=120, dps=186, elapsed_s=232.90283489227295, mu1=5.1220197336635622555094279585937696681464214768335891307527645618439534823224445e-54, mu2=4.0388151226475172531154009790627002660343414636206475946280875005626924513614516e-50, Delta=4.0383029206741508968898500362668408890675268214729642357150122241065080560132193e-50, nu=-3.4575120998997544e-15, W_actual=1074402221254108632456454643945650009.0617937310503294357634667517072280517637705, json=`out/lambda_sq_12_N_120.json`
- lambda=sqrt(13), N=60, dps=191, elapsed_s=34.784167766571045, mu1=1.0135629071691990735997593852745923519567821962511079401549513600182940654999691e-58, mu2=8.5468768301090444860558558929895691142516095123340021712336948888560763754200521e-55, Delta=8.5458632672018752869822561336042945218996527301377510632935399374960580813545521e-55, nu=-1.7605176787762307e-15, W_actual=14921663944605615051307840577947464140964.825387284125863270596363237492927339067, json=`out/lambda_sq_13_N_60.json`
- lambda=sqrt(13), N=90, dps=191, elapsed_s=106.18094515800476, mu1=4.1905358555512152436127626888013956233252289841205365671605892538857574394359324e-59, mu2=3.5484915360935449211825494682521753220579588869174256299816096556599161148363783e-55, Delta=3.5480724825079897996581881919832951824956263640190135763248935967345275390924347e-55, nu=-3.0132096297239507e-15, W_actual=83370377813635319775448341776163298580639.374024348756019409681585433334409859947, json=`out/lambda_sq_13_N_90.json`
- lambda=sqrt(13), N=120, dps=191, elapsed_s=242.02892208099365, mu1=3.4839881993312774991981449396917996125624116158168230912842483927534761108618876e-59, mu2=3.0559133975151656689625792551763612791466009511955487857179350037791429390739945e-55, Delta=3.0555649986952325412126594406823920991853447100339671034088065789398675914629084e-55, nu=-2.5155967218380805e-15, W_actual=142042987159288927618739396865785375511535.11274335552478943964759044452218491726, json=`out/lambda_sq_13_N_120.json`
- lambda=sqrt(14), N=60, dps=197, elapsed_s=33.641002893447876, mu1=2.8385851801697412973983648344651957201151733265631271058509454756350508475238748e-63, mu2=2.2812186535329693431603508564279848109669117217752823670447311818825856582996013e-59, Delta=2.2809347950149523690306110199445382913949002044426260543341460873350221532148489e-59, nu=-2.50949614038424e-15, W_actual=496787753381631782114262759241911256093411234.93640922206166064939769301534510527, json=`out/lambda_sq_14_N_60.json`
- lambda=sqrt(14), N=90, dps=197, elapsed_s=104.76632022857666, mu1=1.8422044334104198880599568819021510886663567874628651756311661320036442453173117e-64, mu2=2.0021619795311044740036299792533034643446065455784558983918675831209934647413772e-60, Delta=2.0019777590877634320148239835651132492357399098997096118743044665077931003168454e-60, nu=-3.0682720489526015e-15, W_actual=14297518669032682106668760399725394257998112195.171731524291758392219602794531816, json=`out/lambda_sq_14_N_90.json`
- lambda=sqrt(14), N=120, dps=197, elapsed_s=236.58579897880554, mu1=1.4598129516305608574358609264922179071797113743878582206556358479950433608366779e-64, mu2=1.6680022583588869596654056727736096522590303309993518433644085253282379668077549e-60, Delta=1.6678562770637239035796620866809604304683123598619130575423429617434384624716713e-60, nu=-4.535840335640321e-15, W_actual=30982658370487248593891314334559415071298861977.664714194975651077930535435004569, json=`out/lambda_sq_14_N_120.json`

## Fits

```json
{
  "Delta": {
    "key": "Delta",
    "n": 3,
    "slope": -310.01018023303203,
    "stderr": 9.337037263764865
  },
  "N_stabilization": {
    "drift_90_to_120": {
      "Delta": 0.20032990049494165,
      "W_actual": 0.5385315714983357,
      "mu1": 0.26194553305801327,
      "mu2": 0.2003352930115277,
      "nu": 0.32354937080926677
    },
    "lambda_sq": 14,
    "pass": false
  },
  "W_actual": {
    "key": "W_actual",
    "n": 3,
    "slope": 312.2478992398691,
    "stderr": 10.69108075669377
  },
  "W_bound": {
    "key": "W_bound",
    "n": 3,
    "slope": 0.790995945158673,
    "stderr": 1.6763940601537461
  },
  "b": {
    "key": "b",
    "n": 3,
    "slope": -0.005438574681786291,
    "stderr": 0.00015316313750279547
  },
  "eta1_over_1_minus_chi4": {
    "key": "eta1_over_1_minus_chi4",
    "n": 3,
    "slope": -3.7187933807547213,
    "stderr": 2.0392406668441985
  },
  "mu1": {
    "key": "mu1",
    "n": 3,
    "slope": -314.7944103131186,
    "stderr": 10.626411439062624
  },
  "mu2": {
    "key": "mu2",
    "n": 3,
    "slope": -310.01068766594295,
    "stderr": 9.337151006864415
  },
  "nu": {
    "key": "nu",
    "n": 3,
    "slope": 3.369250785488762,
    "stderr": 6.873021272588722
  }
}
```

## Next exact theorem/gap suggestion

Use the failure code above as the next exact blocker.

## NConvergenceTriage - 2026-07-03

Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. QW formulas, packet definitions, and Q3 mainline files were not changed.

### Headline

1. T1 `N_NOT_CONVERGING` stop? [NO; no `mu_i` has `rho <= 1.2`; mu-rho min=`4.363188856959323...`, max=`69.41485005036813...`]
2. Registered `rho ~= 2` / p~1 window? [NO; all `mu_i` miss `[1.5,2.5]`, so the old p~1 finite-N model is rejected]
3. T3 class law after Richardson? [FIT_NOT_LAW; `mu1` slope=`12.302118398616892 +/- 0.17684564747116005`; `mu2` slope=`16.339829092635913 +/- 0.10106375830389963`; `Delta` slope=`16.340243501186563 +/- 0.10105671946946808`; `eta1` insufficient extrapolated points]
4. SingleAnchorDeflatedStaticSchur at `(lambda_sq,N)=(13,120)`? [YES; static `S0` reproduces saved/fresh `mu1,mu2,mu3` with max relative error `3.822889888e-8`]
5. Direct-vs-deflated Schur solver agreement? [YES; relative `K_schur` difference `8.07861962331509e-54`; LU residual `5.28866285871307e-63`; spectral residual `9.72530615213224e-71`]
6. Edge/vector cache? [YES; fresh `xi_i`, `m_i/y_i`, mass bands, top coefficients, static dressed-vector probes persisted]
7. Verdict code: `NCONV_TRIAGE_ANCHOR_CONFIRMED_RHO_P1_MISMATCH`

### Files Written

- T1-T5 summary JSON: `out/nconv_triage.json`
- Anchor JSON: `out/nconv_anchor_lambda_sq_13_N_120.json`
- Schur block cache: `out/nconv_anchor_block_cache_lambda_sq_13_N_120.json`
- Progress log: `out/nconv_anchor_progress.log`

### T1-T3 Interpretation

The cheap saved-scalar triage did not fire the requested hard stop `N_NOT_CONVERGING`, because every `mu_i` ratio stayed above `1.2`. However, it also did not support the registered p~1 finite-N model: the `mu_i` ratios range from about `4.36` to about `69.41`, far outside the `[1.5,2.5]` window.

The Richardson extrapolation is therefore logged as diagnostic only, with `FIT_NOT_LAW` for `mu1`, `mu2`, and `Delta`; `eta1` did not have enough positive-power extrapolated points.

### T4-T5 Anchor Interpretation

The one allowed static-Schur anchor at `(13,120)` succeeded. The hidden effective static Schur model is not just a scalar artifact: the run created a request-local block cache, solved `C Y = B`, compared direct LU against the deflated spectral solve, and persisted fresh low eigenvectors plus `m/y` decompositions.

Static `S0` eigenvalues from the LU/refined solve:

```text
theta1 = 3.4839881993313208770576036193691913678566990027895825822059248811595439701671787e-59
theta2 = 3.0559134563989372551938084545848193089331646122242631282819636512679754548707352e-55
theta3 = 1.3118543347202131626775204657566931315304620472673474492658686387171172964495502e-51
```

Saved `mu` values:

```text
mu1 = 3.4839881993312774991981449396917996125624116158168230912842483927534761108618876e-59
mu2 = 3.0559133975151656689625792551763612791466009511955487857179350037791429390739945e-55
mu3 = 1.3118542845694683681589287710261197349911170400431222295428371514482852469210597e-51
```

The first five low `C` modes contribute only about `4.078160439978e-25` of total `K_schur` norm in this anchor. This supports the earlier broad-tail self-energy diagnosis and makes the next check an operator/static-Schur stability gate, not an RH-level conclusion.

### Next Exact Gap Suggestion

Ask Proshka whether the next gate should rerun `StaticSchurEffectivePacketAudit` using the new cached/column-wise Schur solver, or move directly to an operator-level static-Schur stability gate. The p~1 scalar N-convergence model is rejected, but the effective static-Schur anchor is strengthened.

### Proshka Review

Proshka verdict: `STATUS: CHOOSE OPTION 2`.

Next gate: `OperatorStaticSchurStabilityGate`.

Reason: the scalar p~1 N-model is rejected, but the static-Schur mechanism is strengthened. The next object should be operator-level stability of

```text
S0 = G - B^* C^(-1) B
```

as an aligned 3x3 packet operator, not another attempt to repair raw `mu_i(N)` scalar fits.

Proshka also allows exactly one internal purchase, `(lambda_sq,N)=(12,120)`, if that is the only missing hard anchor required for the operator stability comparison. Do not run Phase 2, boundary/prolate audits, slope refits, or raw scalar N-convergence repair before this gate.

### User Goal Addendum

The next `OperatorStaticSchurStabilityGate` goal has an appended requirement file:

```text
operator_static_schur_stability_goal_append.md
```

Additions:
- Run a parity-zero structural judge first at every anchor; odd/even cross entries of `G`, `K_schur`, and `S0` must be numerically zero with threshold `<= 1e-25`; violation is `PARITY_CONTAMINATION`.
- Exploit `S0 = (2x2 even) direct_sum (1x1 odd)` and report `S0_oo`, `eig(even 2x2)`, and `Delta_eff = S0_oo - eig1(even 2x2)` separately.
- Compare dimensionless shape invariants `theta2/theta1` and `theta3/theta1`; ratio drift from `90->120` should be at least `10x` smaller than raw theta drift for Case-B.
- Replace the rejected p~1 scalar model with a geometric N-model on aligned `S0` entries and `eig(S0)`: `rho = drift(60->90)/drift(90->120)`, registered `rho >= 3`, with geometric extrapolation labeled `FIT_NOT_LAW`.
- A fresh `(12,120)` anchor is acceptable only if the parity-zero judge passes and deflated-vs-direct agreement is at least 25 digits.
