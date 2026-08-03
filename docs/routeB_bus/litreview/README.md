# litreview/ — literature & citation management (pipeline-integrated)

Purpose: one place for every external publication we USE, so the eventual paper cites
from evidence, not memory. Chain-of-evidence discipline (from ScientistOne CoE, adopted
this project): every citation claim must trace to a real source PDF in `pdfs/`.

## Layout

- `REFERENCES.md` — master index: each source → **which lemma/theorem/gap uses it** +
  access status. THE tracking file (the user's "не забыть какую публикацию для какой
  леммы/теоремы используем").
- `references.bib` — BibTeX, kept in sync with REFERENCES.md (for the manuscript).
- `pdfs/` — the actual PDF/DJVU files (open-access downloaded; paywalled dropped by
  owner via Uni proxy).
- `litreview_check.py` — validator: flags index rows with no PDF (unless owner-fetch),
  PDFs with no index row, and index rows with no usage mapping.

## The rule (integrate into the loop)

Whenever a goal / answer / verdict / dossier CITES an external publication:
1. add or append a row in `REFERENCES.md` with the exact WHAT-FOR (gap/lemma/theorem);
2. add the BibTeX entry to `references.bib`;
3. if open-access: `curl -sL https://arxiv.org/pdf/<id> -o pdfs/<id>.pdf` (or the DOI
   landing → PDF); if paywalled: mark PAYWALL/BOOK/SCAN and add to the TO-FETCH list —
   OWNER downloads via Uni proxy and drops it in `pdfs/`, then flip Access to HAVE.
4. never cite a source that is not in `REFERENCES.md`.

## Access reality (honest)

Conductor-CLI WebFetch is a plain fetcher with NO institutional proxy: it gets
open-access (arXiv, preprints, some gov) but 403s on Springer/Elsevier/Wiley full-text
and cannot OCR image scans. So: OA I fetch; PAYWALL/BOOK/SCAN the owner fetches via the
Uni proxy. This split is recorded per-row in REFERENCES.md.

## Pipeline hook

`litreview_check.py` runs alongside `orchestrator/spine.py` (both are cheap read-only
validators). A source used but not indexed = a broken citation chain = flagged. Deep
per-theorem extraction from the PDFs is done by launched sub-agents writing usage cards
into `REFERENCES.md` (append-only).

## Zotero live-sync (works — local HTTP API)

Zotero 7 desktop exposes a read-only local API on `http://localhost:23119/api/`
(mirrors the web API, no key needed). We are connected to the owner's actual library.

    python3 docs/routeB_bus/litreview/zotero_pull.py --list   # list all collections
    python3 docs/routeB_bus/litreview/zotero_pull.py          # pull RH collections -> zotero/

RH collections in the owner's Zotero: **Riemann** (YV2MMVPF, 55) · **Weil** (DIT7JPKH) ·
**ClayMath** (MGWGHJ2E). Pulled to `zotero/*.bib` — the live mirror of what the owner has.

**Direction of truth:** `zotero/` = what the OWNER has; `references.bib` = our working set
(Zotero + the fresh frontier we found this session). `zotero/TO_IMPORT_fresh_frontier.bib`
= the 24 papers our litreview has that Zotero LACKS (2024-2026 frontier: CvS 2511.23257,
Groskin ×2, Suzuki ×2, Kulikov ×3, Connes-2026, CC ζ-cycles/q-series, …). Owner imports it
into Zotero: File → Import → that .bib → drag into the Riemann collection. Then re-run
`zotero_pull.py` and the two sides converge.

Re-run the pull whenever the owner edits Zotero; reconcile any new keys into REFERENCES.md.
