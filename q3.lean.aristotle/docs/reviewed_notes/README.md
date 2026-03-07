# Reviewed Notes

This folder is for distilled markdown notes that have already been checked
against the live repo and are safe to include in the local semantic search
collection `q3_docs`.

What belongs here:

- reviewed extracts from Proshka conversations
- distilled theorem candidates
- verified file/lemma maps
- compact mathematical synthesis that survives repo cross-checking

What does **not** belong here:

- raw chat transcripts
- unchecked brainstorming
- notes that still mix legacy and active routes without warning

Workflow:

1. Raw markdown or zip enters `docs/incoming_notes/`.
2. `./scripts/ingest_incoming_notes.py prepare <file>` creates a reviewed stub here.
3. We review it against Lean / TeX / control docs.
4. We extract the reusable core into one reviewed note here.
5. We mark it:
   - `review status: reviewed`
   - `safe for embeddings: yes`
6. We archive the raw source from `incoming_notes/`.
7. We refresh `q3_docs` so the reviewed note becomes searchable by embeddings.
   Only notes marked `safe for embeddings: yes` are indexed.

If a reviewed note later becomes stale, either:

- update it, or
- move it back out of the active reviewed set.
