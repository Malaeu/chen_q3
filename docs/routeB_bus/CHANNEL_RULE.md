# Proshka GitHub channel

This directory is the outbound Route B mirror for Proshka. Top-level artifacts are flat; source-locked subtrees are preserved only when an explicit goal requires their relative paths.

Permanent handoff rule: after every closed Route B goal, refresh this mirror, rebuild `MANIFEST.md`, commit only `docs/routeB_bus/`, and push the current canonical-repository branch. Bus 010 remains void unless the owner explicitly creates it.

Каждый бриф внешнему агенту называет ветку явно: branch `rh_clean`; ссылки полные: https://github.com/Malaeu/chen_q3/tree/rh_clean/docs/routeB_bus.

Source repository commit at refresh: `b37f3855dfe1cd270f28890d19b09611ae16dbc5`.
