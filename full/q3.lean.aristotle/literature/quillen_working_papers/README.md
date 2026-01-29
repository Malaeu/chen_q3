# Quillen Working Papers (1973-2003)

Daniel Quillen's handwritten research notebooks from the Clay Mathematics Institute archive.

## Structure

```
quillen_working_papers/
├── 1973/
│   ├── 1973-1.pdf
│   ├── 1973-1.ocr.md    ← OCR result (after processing)
│   ├── 1973-2.pdf
│   └── ...
├── 1974/
├── ...
└── 2003/
```

- **Total PDFs:** 490 files
- **Format:** Scanned handwritten mathematical notes
- **OCR Output:** `.ocr.md` files with LaTeX math formulas

---

## OCR Processing

### Tool: DeepSeek-OCR-2

Location: `/mnt/hdd01/Soft/GitHub/DeepSeek-OCR-2/`

### Quick Start

```bash
cd /mnt/hdd01/Soft/GitHub/DeepSeek-OCR-2
source .venv/bin/activate

# Single PDF:
python ocr_batch.py /path/to/file.pdf

# All PDFs in one year:
python ocr_batch.py /path/to/quillen_working_papers/1973/

# ALL years recursively:
python ocr_batch.py /path/to/quillen_working_papers/ --recursive

# Skip already processed:
python ocr_batch.py /path/to/quillen_working_papers/ -r --skip-existing
```

### Output Format

Each `YYYY-N.pdf` produces `YYYY-N.ocr.md`:

```markdown
# OCR: 1973-11

## Page 1

[text]
\( M' \times P' \leftarrow M \times P \)

[equation]
\[ Q(m) \leftarrow F \rightarrow Y \rightarrow Q(P) \]

---

## Page 2
...
```

### Performance

| GPU | Attention | Speed |
|-----|-----------|-------|
| TITAN RTX (Turing) | eager | ~30 sec/page |
| A100/H100 (Ampere+) | flash_attention_2 | ~5-10 sec/page |

---

## Knowledge Base Ingestion

After OCR processing, all `.ocr.md` files can be ingested into a vector database:

```bash
# Find all OCR results:
find quillen_working_papers/ -name "*.ocr.md" | wc -l

# Example ingestion command (for another agent):
# "Walk through all directories in quillen_working_papers/,
#  find every .ocr.md file, and ingest into knowledge base"
```

---

## Source

- Clay Mathematics Institute: https://claymath.org/publications/quillen-notebooks
- Index file: `docs/links/quillen_working_papers.json`
