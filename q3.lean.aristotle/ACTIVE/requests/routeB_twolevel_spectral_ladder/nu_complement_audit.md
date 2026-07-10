# Route B TwoLevelSpectralLadder Nu Complement Audit

Status: A-only instrument repair diagnostic. Not a proof of RH. Not a Route B kill.
Phase 2 was not run. The full ladder was not rerun. QW formulas and packet definitions were not changed.

## Proshka Route Review

- Next gate: A.
- `FAILURE_CODE = N_LIMIT_NOT_STABLE`.
- `PRIMARY_DIAGNOSIS = NUMERICAL_FLOOR_IN_NU`.
- `SECONDARY_DIAGNOSIS = BASIS_TRUNCATION_NOT_STABLE_PENDING_PACKET_PRECISION`.
- Route B status: not killed until high-precision complement-basis `nu` is recomputed.

## Verdict

`NU_FLOOR_FIXED_TAIL_FAIL`

## Diagnostic Runs

| run | dps | old full-projection float64 nu | new complement nu | lambda3_G | tail_margin | U_perp dim | elapsed_s |
|---|---:|---:|---:|---:|---:|---:|---:|
| base | 197 | -4.0049875337510944e-15 | 3.296093549548185071913852905077107443365952943543e-53 | 1.1552588608928484370318667777805945411432515263325e-27 | -1.155258860892848437031866744819659045661400807194e-27 | 238 | 229.23750472068787 |
| dps+80 | 277 | -4.535840335640321e-15 | 3.2960935495481700929646432473708934960801252697114e-53 | 1.1552642872984287820819161765566765319384054509856e-27 | -1.1552642872984287820819161435957410364567045213392e-27 | 238 | 282.1205940246582 |

## Precision Check

```json
{
  "nu_rel_error": "1.4978949209657706213947285827673831654744265469956913332741862887870438770277306e-67",
  "tail_margin_rel_error": "5.4264055803450500493987760819907953037141451795655054396227751094964162196092235e-33",
  "threshold": "1.0e-30"
}
```

## Conditioning

### base

```json
{
  "gram_condition_mp": "1.2531023673497912399075054777895455295704924701179265908618548659107247173621764",
  "mperp_cross_error": "implicit_secular_nullspace",
  "q_orth_error": "8.3610891304336663808925365720410188012344693074189629488853630385994520237561597e-198",
  "q_stats": {
    "accepted": 3,
    "max_rejected_norm": "0.0",
    "min_accepted_norm": "0.99367038625276913218416633729215644003552947664166753272637395505267750790502637",
    "rejected": 0,
    "tol": "1.0e-65"
  },
  "u_orth_error": "implicit_secular_nullspace",
  "u_stats": {
    "accepted": 238,
    "mode": "implicit_secular_nullspace",
    "note": "U_perp is represented implicitly as null(Q_M^*) for the secular restricted eigenvalue solve."
  }
}
```

### dps+80

```json
{
  "gram_condition_mp": "1.2531023673497912399075054777895455295704924701179265908618548659107247173621764",
  "mperp_cross_error": "implicit_secular_nullspace",
  "q_orth_error": "1.2692772955299582956736999008252905350768136567047774310861187356469476768608418e-277",
  "q_stats": {
    "accepted": 3,
    "max_rejected_norm": "0.0",
    "min_accepted_norm": "0.99367038625276913218416633729215644003552947664166753272637395505267750790502637",
    "rejected": 0,
    "tol": "1.0e-80"
  },
  "u_orth_error": "implicit_secular_nullspace",
  "u_stats": {
    "accepted": 238,
    "mode": "implicit_secular_nullspace",
    "note": "U_perp is represented implicitly as null(Q_M^*) for the secular restricted eigenvalue solve."
  }
}
```

## Next Step

Tail failure remains after the complement-basis repair. Inspect the rogue tail eigenvector before any broader Route B claim.
