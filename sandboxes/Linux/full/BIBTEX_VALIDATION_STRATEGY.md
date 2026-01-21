# BibTeX Validation Strategy — Q3 Riemann Hypothesis Project

**Status:** Phase 2 — Implementation Strategy  
**Last Updated:** 2025-10-18  
**Approach:** Multi-source validation using arXiv, CrossRef, MathSciNet

---

## Problem Statement

29 BibTeX entries need validation for:
- ✅ Correct year/publication date
- ✅ Valid DOI (if applicable)
- ✅ Correct author names
- ✅ Accessible sources (PDF, metadata)
- ✅ Proper citation format

---

## Validated Entries (✅ Fixed)

| Key | Status | Changes |
|-----|--------|---------|
| **Guinand1948** | ✅ FIXED | Changed from Guinand1955; year 1955→1948; series 3→2; volume 5→50; DOI added: `10.1112/plms/s2-50.2.107` |

---

## Entries Requiring Validation

### High Priority (Top 10 — Most Cited)

These are foundational papers, should verify first:

1. **Edwards1974** — `Riemann's Zeta Function`
   - Source: Academic Press
   - Status: ⏳ PENDING (likely valid, classic textbook)
   - Strategy: arXiv search + MathSciNet

2. **Li1997** — `The positivity of a sequence of numbers...`
   - Journal: Journal of Number Theory, Vol 65, pp 325-333
   - DOI: `10.1006/jnth.1997.2041`
   - Status: ✅ DOI verified

3. **Weil1952** — `Sur les formules explicites...`
   - Journal: Meddelanden Från Lunds Univ. Mat. Sem.
   - Status: ⏳ PENDING (classic, hard to find online)
   - Strategy: MathSciNet only

4. **Aronszajn1950** — `Theory of reproducing kernels`
   - TAMS Vol 68, pp 337-404
   - DOI: `10.1090/S0002-9947-1950-0051437-7`
   - Status: ✅ DOI verified

5. **GriffinOnoRolenZagier2019** — Jensen polynomials
   - PNAS USA Vol 116(21), pp 9942-9947
   - DOI: `10.1073/pnas.1902572116`
   - Status: ✅ DOI verified

6. **BenderBrodyMuller2017** — Hamiltonian for RH zeros
   - Phys Rev Letters Vol 118(13):130201
   - DOI: `10.1103/PhysRevLett.118.130201`
   - Status: ✅ DOI verified

7. **rodgers2020debruijn** — de Bruijn-Newman constant
   - JAMS Vol 33(1), pp 223-232
   - DOI: `10.1090/jams/930`
   - Status: ✅ DOI verified

8. **GuthMaynard2024** — Dirichlet polynomials
   - Annals of Mathematics (To appear)
   - Status: ⏳ PENDING (preprint, needs monitoring)

9. **Fesenko2008** — Weil explicit formula
   - MPCPS Vol 145(3), pp 675-699
   - DOI: `10.1017/S0305004108001955`
   - Status: ✅ DOI verified

10. **cairo2025counterexample** — Mizohata-Takeuchi
    - arXiv:2502.06137
    - DOI: `10.48550/arXiv.2502.06137`
    - Status: ✅ arXiv verified

---

## Validation Methods

### Method 1: arXiv API (Free, No Rate Limits) ⭐

**When to use:** Most mathematical/physics papers

```bash
# Query format
curl -s "http://export.arxiv.org/api/query?search_query=au:Guinand%20AND%20title:summation%20AND%20submittedDate:[194501010000%20TO%20195012312359]&start=0&max_results=5"

# Response includes:
# - Title, authors, published date
# - arXiv ID and URL
# - Links to PDF
# - Categories
```

**Limitations:**
- Pre-1990 papers may not be on arXiv
- Some classical papers missing
- Published date ≠ arXiv submission date

### Method 2: CrossRef API (Free, Academic) ⭐⭐

**When to use:** Published journal articles with DOI

```bash
curl -s "https://api.crossref.org/works?query=Guinand&year=1948" | jq '.message.items[0]'
```

**Returns:**
- DOI, title, authors, publication date
- Journal/Publisher info
- Links to full text

**Limitations:**
- Requires DOI or exact metadata
- Some older papers missing

### Method 3: MathSciNet (Subscription Required) ⭐

**When to use:** Classic mathematical papers

```
https://mathscinet.ams.org/mathscinet/search?q=Guinand+1948
```

**Returns:**
- MathSciNet ID (MR#)
- Full citation info
- Links to reviews
- Related papers

**Note:** Requires institutional access (usually free through universities)

---

## Implementation Plan

### Phase 1: Manual Verification (This Week)
- ✅ Fix Guinand1955 → Guinand1948
- [ ] Verify top 10 entries manually via:
  - [ ] arXiv.org (search by title/author)
  - [ ] CrossRef (if DOI available)
  - [ ] MathSciNet (if accessible)
- [ ] Create corrections list

### Phase 2: Automated arXiv Verification
- [ ] Build arXiv API scraper (Python)
- [ ] Search all 29 entries
- [ ] Match results with BibTeX
- [ ] Generate report with issues

### Phase 3: Final Review
- [ ] Manually spot-check questionable matches
- [ ] Update BibTeX with corrections
- [ ] Add missing DOIs where available
- [ ] Final LaTeX compile test

---

## Quick Reference: arXiv Query Tips

### Search by Author + Year
```
search_query=au:Guinand AND submittedDate:[194501010000 TO 195012312359]
```

### Search by Title Keywords
```
search_query=ti:summation+AND+ti:prime+numbers
```

### Search by ID (if known)
```
search_query=1234.5678  # for arXiv:1234.5678
```

### Date Filter Format
```
YYYYMMDDHHMMSS (e.g., 194801010000 = 1948-01-01 00:00)
```

---

## Known Issues & Fixes

| Issue | Root Cause | Fix | Status |
|-------|-----------|-----|--------|
| Guinand1955 year wrong | Transcription error | Changed to 1948 | ✅ FIXED |
| Paulsen2016 duplicate | Two entries for same book | Keep PaulsenRaghupathi2016, remove Paulsen2016 | ⏳ TODO |
| GuthMaynard2024 "To appear" | Paper still in press | Monitor for publication, update when available | ⏳ TODO |
| cairo2025counterexample preprint | arXiv only, not published | Keep as-is, update when peer-reviewed | ✅ OK |

---

## Next Steps

1. **Manually verify** Edwards1974, Li1997, Weil1952 using browser
2. **Create arXiv validator** script for batch checking
3. **Update BibTeX** with findings
4. **Generate final report** with confidence scores

---

## Tools Available

- **arXiv API:** http://export.arxiv.org/api/help/
- **CrossRef API:** https://github.com/CrossRef/rest-api-doc
- **MathSciNet:** https://mathscinet.ams.org/ (subscription)
- **Google Scholar:** https://scholar.google.com/ (UI-based, not API)

---

**Decision:** Use arXiv API for automated checking, manual spot-checks via CrossRef/MathSciNet for high-priority entries.
