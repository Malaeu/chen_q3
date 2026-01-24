# PROSHKA POLICY (single source of truth)

**Goal:** keep Proshka inputs minimal, canonical, and non-duplicative.

## Canonical set (use these 3)

1) **Knowledge base (stable index)**
   - `ACTIVE/KNOWLEDGE_BASE.md`

2) **Current request (changes when target changes)**
   - `PROSHKA_REQUEST_4.md`

3) **Packed context (generated, one file)**
   - `PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md`

## Legacy / optional

- `ACTIVE/proshka_memory_pack.md` is a symlink to `ACTIVE/KNOWLEDGE_BASE.md`.
- Older requests (e.g., `PROSHKA_REQUEST_3.md`) are **archive only**.

## Rule of thumb

- If you need orientation → **Knowledge base**.
- If you need exact task → **Current request**.
- If you need everything in one file → **Packed context**.

## Build / update

Use:
```
python3 scripts/build_proshka_brief.py --mode full --max-file-lines 2000 \
  --include-glob 'full/q3.lean.aristotle/ACTIVE/spec_*.md' \
  --include-glob 'docs/Как работают модели типа Аристотель и их тренировка/*.md' \
  --include-file 'full/q3.lean.aristotle/aristotle_input/continuous_P_A_shift_tcritical.md' \
  --out full/q3.lean.aristotle/PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md
```

## Do not duplicate

Do **not** create parallel packs or parallel requests unless the target changes.

## Proshka pack updater
- scripts/refresh_proshka_pack.sh (manual refresh)
- .git/hooks/post-commit (auto refresh; local only)
