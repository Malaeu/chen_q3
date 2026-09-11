# Owner advice channel (owner's word, 2026-09-11 evening, relayed by the observer)

Purpose: the owner and the observer push ideas into the executor's work without opening its thread.

1. Source. The owner tells the observer an idea (phone, chat). The observer checks it first: shelf (`./ask.sh`), a number by hand
   (rule 13), `alias-hunt`, and when needed a separate judge chat («Прошка Б») for owner/observer ideas only.
2. File. The observer writes `docs/Codex/ADVICE_<YYYY-MM-DD>_<NAME>.md` (one word NAME): the idea, what was verified with locators,
   the negative controls, the probe, IF_A / IF_B, and the owner's words quoted. Then a named commit and ordinary push.
3. Wake-up. The executor keeps a watch (`specs_docs/vahta.sh --path docs/Codex/ADVICE_*` or its native equivalent) exactly as
   the observer keeps one on Proshka's verdict paths. A new ADVICE file on origin is the kick; no owner line in the thread is needed.
4. Work rule, three attempts. The executor gets three attempts of its own (its internal checker included) and at most ONE Proshka
   request per three attempts. It answers in one message only when that message is a victory: the asked statement proved or
   refuted with a witness, at PAPER scope. Anything else is not an answer.
5. Failure rule. After three attempts without victory it stops, writes «поражение» plainly, records what was gained (identities,
   controls, killed branches with numbers, the first unpaid inequality) in the report, commits and pushes at once, then asks the
   owner/observer through the report. The observer's watch on the report path is the owner's wake-up.
6. Nothing here changes PX_RH_CLAIM, the writer lock, the immutable requests, or the review rules.
7. Addressing and wake-up (owner's word 2026-09-11 ~21:10). First line of every ADVICE: `TO: MAT | STROJKA | BOTH`. Each thread keeps
   its own watch on `origin/rh_clean` (vahta.sh or native heartbeat at the existing GOAL §3 cadence, 10 min) and reads new ADVICE files addressed to it. Answers go to
   `docs/Codex/REPORT_<date>_<NAME>[_MAT|_STROJKA].md`, first line `RE: … STATUS: VICTORY | DEFEAT | PARTIAL`, commit prefix
   `[Codex][rh_clean][<NAME>]`, ordinary push. The observer watches `[Codex]` commits for the owner.
8. Standing grant: the observer commits/pushes ADVICE files, CHAT_DIGESTS entries and sibling scripts without per-post approval.
   How-to for the threads: `ADVICE_2026-09-11_WATCH.md`.
