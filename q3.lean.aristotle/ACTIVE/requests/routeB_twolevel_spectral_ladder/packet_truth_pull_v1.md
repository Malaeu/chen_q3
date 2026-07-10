# PacketTruthPull_v1

Route B diagnostic only. Not RH. No Phase 2. Primary point `(lambda_sq,N)=(13,120)`.

## Verdict

- status: `complete`
- codes: `['ROTATION_REAL', 'Y_LADDER_TAIL']`
- theta code: `ROTATION_REAL`
- theta literal `[1e-5,6e-5]` pass: `False`; edge `[1e-5,7e-5]` pass: `True`
- y code: `Y_LADDER_TAIL`
- PSD requested pass: `True`

## T0 Pulls

- a1_raw: `5.37295373544e-59`
- a1_projected: `4.71997997951e-59`
- g12: `(1.29111393041e-55 - 7.75036235566e-137j)`
- lambda1(G_even): `3.89216559799e-59`
- lambda2(G_even): `2.01370652357e-51`
- theta_intra: `6.41162922101e-5`
- |<xi1,k1_new>| raw/projected: `0.999999997654` / `0.999999997654`
- |<xi1,k2e_new>| projected: `0.113738510846`
- E_tail_y: `5.73146458609e-36`
- c*_y: `8.61612218014e-19`; registered band pass `False`
- PSD requested `|g12|^2 <= lambda1*lambda2`: `True`; lhs `1.6669752e-110`, rhs `7.8376793e-110`
- PSD standard `|g12|^2 <= g11*g22`: `True`

## T1 Moments

- moment2 `<k1,T^2k1>`: `5.06085265253e-60`
- moment2 alt `<Tk1,Tk1>` abs diff: `1.8062947e-224`
- s: `1.23599178018`
- m_h: `5.06085265253e-60`
- registered s pass: `True`; registered m_h pass: `False`
- eta_from_moment: `2.249633893e-30`

## T2 Residual Split

- ||r||: `2.249633893e-30`
- ||r_low||: `3.46026183483e-49`
- ||r_rest||: `2.249633893e-30`
- bulk dominated: `True`; low part pass `<1e-45`: `True`

## T4 N=90

- ||y||(13,90): `8.0852644385e-9`
- ||y||(13,120): `2.57915167102e-9`
- y90/y120: `3.13485419619`
- N90 mu1 rel error vs saved: `8.1094078e-82`

## Stop

Stop after report + handoff.
