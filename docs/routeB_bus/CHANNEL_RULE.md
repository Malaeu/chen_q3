# Proshka GitHub channel

This directory is the outbound Route B mirror for Proshka. Top-level artifacts are flat; source-locked subtrees are preserved only when an explicit goal requires their relative paths.

Permanent handoff rule: after every closed Route B goal, refresh this mirror, rebuild `MANIFEST.md`, and push the current canonical-repository branch. Bus 010 remains void unless the owner explicitly creates it.

Canon travels with the mirror (owner decision, 2026-07-30). The earlier form of this rule said *commit only* `docs/routeB_bus/`. That was followed to the letter and left the canonical bus sitting uncommitted in the working tree. Mythos reads GitHub at dispatch time, so it diagnosed from a repository state that no longer matched the disk and issued goal 037 task B for a canon sync already done. Same trigger as before -- a closed goal -- but now the commit covers both the mirror and the canonical bus, so the two cannot drift apart.

Still forbidden: force-push, merging `rh_clean` into `main`, any push that raises Route B status or claims RH.

Каждый бриф внешнему агенту называет ветку явно: branch `rh_clean`; ссылки полные: https://github.com/Malaeu/chen_q3/tree/rh_clean/docs/routeB_bus.

Source repository commit at refresh: `9b8f55d52848922e658a5e2eb4c0726a6beb9b8e`.
