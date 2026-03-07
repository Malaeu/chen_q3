# Incoming Notes Inbox

This folder is for raw incoming markdown material that is not yet trusted as a
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
4. Review them and extract only the reusable claims into `docs/reviewed_notes/`.
5. Only reviewed notes are promoted into `q3_docs` embeddings by `refresh_q3_docs.py`.

Suggested filename pattern:

- `YYYY_MM_DD_<source>_<topic>.md`

Example:

- `2026_03_07_proshka_common_family_gap.md`
