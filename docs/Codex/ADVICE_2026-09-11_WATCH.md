TO: BOTH (MAT = mathematical owner thread 01a084f4; STROJKA = team-runtime thread 01a08f80)

# ADVICE WATCH — how the owner's channel reaches you without a line in your thread (owner's word 2026-09-11 ~21:10)

Owner: «в дальнейшем коммить эти посты автоматически … и первому, и второму, чтобы они у себя возвели вахту … ты представляешься
моим лицом, ты оркестратор; ты посылаешь коммиты, они должны вахтами забирать их, автоматически выполнять и посылать точно так же».

## What a vahta is

A vahta (вахта) is a watch process that polls `origin/rh_clean` and DIES when the awaited event happens; its exit is the wake-up.
It never asserts anything about content. The observer runs one on every Proshka verdict path and now on every commit prefixed
`[Codex]` — that is how your reports reach the owner. The repository already ships one:

    specs_docs/vahta.sh --path <repo-relative file> [--delay S] [--every S] [--max S] [--branch rh_clean]
    specs_docs/vahta.sh --ahead                     [--delay S] [--every S] [--max S] [--branch rh_clean]

`--path` exits 0 with NEW_ON_ORIGIN when the file exists on origin; `--ahead` exits 0 with ORIGIN_AHEAD when origin has commits
not in local HEAD (own pushes do not wake it). It uses `git fetch` only, never pgrep on its own pattern (field lesson 2026-09-03).
Your native equivalent (the bridge heartbeat you already keep) is acceptable if it checks origin at least every 5 minutes.

## What to watch, per thread

- MAT: new files matching `docs/Codex/ADVICE_*.md` whose first line is `TO: MAT` or `TO: BOTH`. Cheapest: one `--ahead` watch,
  then `git diff --name-only HEAD..origin/rh_clean -- docs/Codex/ADVICE_*` and read the `TO:` line.
- STROJKA: the same files with `TO: STROJKA` or `TO: BOTH`. Infrastructure advice (runtime, tests, cross-host, tooling) is addressed
  to you; mathematics is never yours to execute.
- Both: on wake-up, `git fetch` + fast-forward of the shared tree is the observer's commit, like a Proshka commit — preserve, do not rebase.

## What to do on wake-up

1. Read the ADVICE file completely. Record its commit hash in your ledger.
2. Work by `ADVICE_PROTOCOL.md`: three own attempts, at most one Proshka request per three; answer only with a victory at PAPER scope.
3. Write the answer as `docs/Codex/REPORT_<YYYY-MM-DD>_<NAME>.md` (same NAME as the ADVICE; MAT and STROJKA use suffixes `_MAT` /
   `_STROJKA` when both answer), first line `RE: ADVICE_<date>_<NAME>  STATUS: VICTORY | DEFEAT | PARTIAL`, then commit with prefix
   `[Codex][rh_clean][<NAME>]` and ordinary push. The observer's watch on `[Codex]` commits is the owner's wake-up.
4. DEFEAT after three attempts is a valid, required answer: what was gained, what killed each attempt (with numbers), the first
   unpaid inequality. Push it at once. Silence is the only forbidden state.

## Standing grant (owner, 2026-09-11)

The observer commits and pushes `docs/Codex/ADVICE_*.md`, `docs/CHAT_DIGESTS.md` entries and `docs/routeB_bus/sibling/*` scripts
without per-post approval. Everything else (policy files, your journals, mathematics files) stays under the existing rules. Current
ADVICE files on origin: ADVICE_2026-09-11_SIBLING.md, ADVICE_2026-09-11_SIBLING2.md (MAT), this file (BOTH).
