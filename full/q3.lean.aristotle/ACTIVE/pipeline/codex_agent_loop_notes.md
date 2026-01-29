# Codex agent loop (OpenAI blog, 2026-01-23)

Source: OpenAI engineering post "Unrolling the Codex agent loop".

Key takeaways relevant to our workflow:

- The Codex CLI agent loop alternates model inference and tool calls until a
  final assistant message is produced.
- Prompt construction uses a role-ordered list of items: system > developer
  > user > assistant. The prompt is built from `instructions`, `tools`, and
  `input` items in the Responses API payload.
- Codex aggregates user instructions (AGENTS.md, skills, etc.) and includes
  environment context items in the prompt.
- Codex manages context growth via compaction; it can use the
  `/responses/compact` endpoint with an opaque `compaction` item to preserve
  latent context while shortening the prompt.
- The Codex CLI is open source and the post links to the repo for deeper
  implementation details.

Keep this note short; prefer linking to the source when needed.
