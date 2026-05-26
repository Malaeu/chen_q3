# Step32F Q-radius serialization repair

Purpose: enlarge the active Step22 Q radii around the exact midpoint CSV
decimals imported by Lean.

- dry_run: False
- L/ell/delta: 3.0 / 0.30 / 0.25
- arb_prec: 256
- slack_rel: 1.000000001
- slack_abs: 1e-60

## Blocks

### primary_k11

- radius CSV: `docs/insights/q3_psdpd_step22_radii_k11.csv`
- Q rows audited: 46
- entries rewritten: 0
- failures before: 0
- failures after: 0
- max shortfall: 0
- radius sha256 before: `6e29b6de57d2be9e6f1460d90061d65dfa18833eaa9062ec2408ca7816e41675`
- radius sha256 after: `6e29b6de57d2be9e6f1460d90061d65dfa18833eaa9062ec2408ca7816e41675`

### control_k9

- radius CSV: `docs/insights/q3_psdpd_step22_radii_k9.csv`
- Q rows audited: 46
- entries rewritten: 0
- failures before: 0
- failures after: 0
- max shortfall: 0
- radius sha256 before: `ee50429a7ed0cd9929f39e8ee5a924b61b5ddeb413c0705624a631c96c9c0c17`
- radius sha256 after: `ee50429a7ed0cd9929f39e8ee5a924b61b5ddeb413c0705624a631c96c9c0c17`

