# PROSHKA_VERDICT_HARD_GATE_VS_SOFT_PENALTY_2026-08-09

## STATUS
META_POSTMORTEM (methodology)

## SOURCE
Тред: `2026-8-9 10-14-19-___________________________________.md`.

## VERDICT
Постмортемы PROOF_GEOMETRY_V0 и SPECTRAL_CUT (Rayleigh-дискриминатор):
мультипликативный soft-штраф не выдерживает экспоненциального спада потенциала с глубиной —
доверие должно быть hard gate, не множителем. Убитые ветки ложатся на дно (kill в top-3
только на вырожденном cp24). Rayleigh-дискриминатор — разделитель веток.
