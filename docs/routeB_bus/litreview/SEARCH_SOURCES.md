# Where to search — literature sources for Route B (all channels: Mythos, Proshka, Codex)

Maintained by Mythos. Last update: 2026-11-05.

**Rule.** Search the repo first. Then search the sources below. Before citing any paper, check it for an erratum or correction. The Lagarias 1999 paper has one (2005) that changes its Lemma 3.1; see `LAGARIAS_1999_CORRECTION_2005_NOTE.md`.

## 1. Inside the repo (github.com/Malaeu/chen_q3, branch rh_clean)

- `docs/routeB_bus/litreview/`: usage cards, notes, and `pdfs/`.
- `docs/literature/`: topic folders with PDFs.
- `docs/routeB_bus/litreview/pdfs/survey_2026-09-03_sources/`: `.txt` extractions, e.g. Báez-Duarte, Burnol.
- `docs/routeB_bus/mythos/DIGEST_GOAL058_SEPT_2026/`: digests of the September campaign.

**Git LFS warning.** Many PDFs are LFS pointers, about 130 bytes, containing `version https://git-lfs...`. Raw, contents-API or `git show` reads return only the pointer. Fetch the real file from:

    https://media.githubusercontent.com/media/Malaeu/chen_q3/rh_clean/<path>

Some PDFs use Type-3 fonts; pdftotext then returns garbage. Read the pages as images instead.

## 2. MCP tools

| Tool | Status (2026-11-05) | Use |
|---|---|---|
| Consensus MCP (`search`) | WORKS | Semantic search over ~400M papers. Returns DOIs and institutional links (uni-due digibib / LibKey). Good for "who extended theorem X". |
| Scite MCP | NOT ACTIVE: needs a paid plan or trial | Smart citations, erratum/correction flags, OA full-text excerpts |
| Scholar Gateway | available | semantic search |
| PubMed | irrelevant for RH | — |

## 3. Web sources for mathematics (domains seen in Proshka's searches)

| Domain | What is there | Reachable from Mythos sandbox (WebFetch) |
|---|---|---|
| arxiv.org | preprints, HTML and PDF | yes |
| eudml.org | EuDML metadata and links (Acta Arith. etc.) | metadata only |
| geodesic.mathdoc.fr | metadata, OA links | metadata only |
| matwbn.icm.edu.pl | **free full-text PDFs of Acta Arithmetica** and other Polish journals | NO (not on allowlist) |
| impan.pl, pldml.icm.edu.pl, bibliotekanauki.pl | IMPAN journals, full texts | NO |
| dlmf.nist.gov | DLMF special functions | yes (used by Proshka) |
| websites.umich.edu/~lagarias | Lagarias' own papers | check |
| aimath.org | AIM RH resources | check |
| mathnet.ru | Russian journals | check |
| sciencedirect.com, researchgate.net, explore.openaire.eu | publisher / OA aggregators | partly |
| urresearch.rochester.edu, www2.math.ethz.ch | university repositories | check |
| mathworld.wolfram.com | quick definitions only, never as a source of theorems | yes |

If a source is not reachable from one channel, another channel may fetch it. Failing that, the owner downloads it via his institutional access and drops the PDF into `docs/routeB_bus/litreview/pdfs/`.

## 4. Open items

- Lagarias, Acta Arith. 116 (2005) 293–294, DOI 10.4064/aa116-3-5 (the Correction): PDF still missing. Candidate sources: matwbn.icm.edu.pl, or uni-due access.
