# Incoming Notes Inbox

This folder is for raw incoming markdown or zip material that is not yet trusted as a
search-ready knowledge source.

Examples:

- Proshka / O3 / ChatGPT conversation dumps
- long mathematical brainstorming notes
- external markdown summaries that still need checking
- partial proof sketches that may contain false claims, mixed notation, or stale repo references

Rules:

1. Put the raw markdown here first.
2. Do **not** treat files here as source of truth.
3. Do **not** rely on these files directly in mainline decisions.
4. Run `./scripts/ingest_incoming_notes.py prepare <file>` to extract zip inputs and create a review stub.
5. Review them and extract only the reusable claims into `docs/reviewed_notes/`.
6. After review, archive the raw source with `./scripts/ingest_incoming_notes.py archive ...`.
7. Only reviewed notes marked `safe for embeddings: yes` are promoted into `q3_docs`
   by `refresh_q3_docs.py`.

Suggested filename pattern:

- `YYYY_MM_DD_<source>_<topic>.md`

Example:

- `2026_03_07_proshka_common_family_gap.md`
- `2026_03_07_conversations.zip`
