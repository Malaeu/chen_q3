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

1. Raw markdown enters `docs/incoming_notes/`.
2. We review it against Lean / TeX / control docs.
3. We extract the reusable core into one reviewed note here.
4. We refresh `q3_docs` so the reviewed note becomes searchable by embeddings.

If a reviewed note later becomes stale, either:

- update it, or
- move it back out of the active reviewed set.
