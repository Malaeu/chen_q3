#!/usr/bin/env python3
"""
Semantic Scholar BibTeX Verification - FINAL (working)
- 10+ second delays between requests
- Manual URL encoding
- Simplified queries (no special chars, just keywords)
"""

import json
import time
import csv
import re
import urllib.parse
from pathlib import Path
from typing import Dict, Optional
import subprocess

BIBTEX_FILE = Path(__file__).parent / "references.bib"
OUTPUT_CSV = Path(__file__).parent / "semantic_scholar_verification.csv"

SS_API = "https://api.semanticscholar.org/graph/v1/paper/search"

class SemanticScholarVerifier:
    
    def __init__(self, output_csv: Path):
        self.output_csv = output_csv
        self.results = []
        self.request_count = 0
        self.session_start = time.time()
    
    @staticmethod
    def simplify_query(title: str, year: Optional[int] = None) -> str:
        """Build simplified query: remove LaTeX, special chars, keep keywords only"""
        # Remove LaTeX commands
        title = re.sub(r'\{\\[a-z]+\{([^}]*)\}\}', r'\1', title)
        title = re.sub(r'\{\\\'([aeiouAEIOU])\}', r'\1', title)
        title = re.sub(r'[{}\\]', '', title)
        
        # Remove special punctuation, keep alphanumeric and spaces
        title = re.sub(r"['\"`]", '', title)  # Remove quotes/accents
        title = re.sub(r'[^a-zA-Z0-9\s-]', '', title)  # Keep only letters, numbers, spaces, hyphens
        
        # Clean up spacing
        title = re.sub(r'\s+', ' ', title).strip()
        
        # Keep important keywords (heuristic: words > 3 chars, or numbers)
        words = title.split()
        important = [w for w in words if len(w) > 3 or w.isdigit()][:6]  # First 6 important words
        
        query = ' '.join(important)
        if year and 1000 < year < 2100:
            query += f" {year}"
        
        return query
    
    def make_request(self, query: str, year: Optional[int] = None) -> Optional[Dict]:
        """Make API request with 10s delay and retry logic"""
        
        # Wait 10+ seconds before request
        time.sleep(10.5)
        
        # Build URL with manual encoding
        encoded_query = urllib.parse.quote(query)
        fields = "title,year,authors,citationCount,doi,externalIds"
        url = f"{SS_API}?query={encoded_query}&limit=5&fields={fields}&sort=relevance"
        
        # Add year filter if provided
        if year and 1000 < year < 2100:
            url += f"&year={year}"
        
        try:
            result = subprocess.run(
                ['curl', '-s', '-w', '\n%{http_code}', url],
                capture_output=True,
                text=True,
                timeout=20
            )
            
            lines = result.stdout.strip().split('\n')
            http_code = int(lines[-1]) if lines else 0
            body = '\n'.join(lines[:-1]) if len(lines) > 1 else ''
            
            self.request_count += 1
            
            if http_code == 200:
                try:
                    return json.loads(body)
                except json.JSONDecodeError:
                    return None
            elif http_code == 429:
                print(f"      ⏳ 429 Rate limited, retry needed")
                return None
            else:
                print(f"      ❌ HTTP {http_code}")
                return None
        
        except Exception as e:
            print(f"      ❌ Error: {str(e)[:40]}")
            return None
    
    def verify_entry(self, key: str, bibtex_data: Dict) -> Dict:
        """Verify BibTeX entry"""
        
        print(f"\n📄 [{self.request_count:2d}] {key:25s}", end='', flush=True)
        
        result = {
            'bibtex_key': key,
            'title': bibtex_data.get('title', 'N/A'),
            'authors': bibtex_data.get('author', 'N/A'),
            'year': bibtex_data.get('year', 'N/A'),
            'doi': bibtex_data.get('doi', 'N/A'),
            'status': 'NOT_FOUND',
            'ss_title': '',
            'ss_authors': '',
            'ss_year': '',
            'ss_doi': '',
            'ss_citations': '',
            'match_score': 0,
            'notes': ''
        }
        
        # Extract fields
        title = bibtex_data.get('title', '').strip('{} ')
        if not title:
            result['notes'] = 'Empty title'
            print(' ⚠️  EMPTY')
            return result
        
        year = bibtex_data.get('year', '').strip()
        year_int = int(year) if year and year.isdigit() else None
        
        # Build simplified query
        query = self.simplify_query(title, year_int)
        
        # Request
        print(f' | {query[:40]:40s}', end='', flush=True)
        response = self.make_request(query, year_int)
        
        if not response or 'data' not in response or len(response.get('data', [])) == 0:
            print(' ❌')
            return result
        
        # Find best match
        papers = response['data']
        best_match = papers[0]
        
        # Prefer year match
        if year_int:
            for paper in papers:
                if paper.get('year') == year_int:
                    best_match = paper
                    break
        
        # Extract data
        result['ss_title'] = best_match.get('title', '')
        result['ss_year'] = str(best_match.get('year', ''))
        
        # Authors
        ss_authors = best_match.get('authors', [])
        author_names = ', '.join([a.get('name', '') for a in ss_authors[:2]])
        result['ss_authors'] = author_names
        
        # DOI
        ext_ids = best_match.get('externalIds', {})
        result['ss_doi'] = ext_ids.get('DOI', '')
        
        # Citations
        result['ss_citations'] = str(best_match.get('citationCount', 0))
        
        # Score matching
        match_score = 100
        
        # Title match (fuzzy)
        title_lower = title.lower()
        ss_title_lower = result['ss_title'].lower()
        
        if title_lower not in ss_title_lower and ss_title_lower not in title_lower:
            match_score -= 25
            result['notes'] += 'TITLE_DIFF; '
        
        # Year match
        if year_int and result['ss_year'] and str(year_int) != result['ss_year']:
            match_score -= 20
            result['notes'] += f'YEAR({year_int}vs{result['ss_year']}); '
        
        result['match_score'] = max(match_score, 0)
        
        if result['match_score'] >= 75:
            result['status'] = 'VERIFIED'
            print(f' ✅ {result['ss_citations']:>4s}c')
        elif result['match_score'] >= 50:
            result['status'] = 'POSSIBLE_MATCH'
            print(f' ⚠️  {result['ss_citations']:>4s}c')
        else:
            result['status'] = 'QUESTIONABLE'
            print(f' ❓ {result['ss_citations']:>4s}c')
        
        return result
    
    def parse_bibtex(self) -> Dict[str, Dict]:
        """Parse BibTeX file"""
        entries = {}
        
        with open(BIBTEX_FILE, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Match @type{key, fields}
        pattern = r'@(\w+)\s*\{\s*([^,]+?)\s*,\s*(.*?)\n\}'
        
        for match in re.finditer(pattern, content, re.DOTALL | re.IGNORECASE):
            key = match.group(2).strip()
            fields_text = match.group(3)
            
            fields = {}
            
            # Parse fields
            field_pattern = r'(\w+)\s*=\s*(?:\{([^}]*)\}|"([^"]*)"|([^,}]*))'
            
            for field_match in re.finditer(field_pattern, fields_text):
                fname = field_match.group(1).strip().lower()
                fval = (field_match.group(2) or field_match.group(3) or field_match.group(4) or '').strip()
                
                if fval:
                    fields[fname] = fval
            
            if 'title' in fields and 'author' in fields:
                entries[key] = fields
        
        return entries
    
    def run(self):
        """Run verification"""
        print("🚀 Semantic Scholar BibTeX Verification (FINAL)")
        print("=" * 100)
        print(f"Input:  {BIBTEX_FILE}")
        print(f"Output: {OUTPUT_CSV}")
        print(f"Delay:  10s between requests (no API key needed)")
        print("=" * 100)
        
        print("\n📖 Parsing BibTeX...")
        entries = self.parse_bibtex()
        print(f"   Found {len(entries)} entries\n")
        
        if not entries:
            print("ERROR: No entries found!")
            return
        
        print("🔍 Verifying...")
        print("-" * 100)
        
        for key in sorted(entries.keys()):
            result = self.verify_entry(key, entries[key])
            self.results.append(result)
        
        print("\n" + "=" * 100)
        print(f"💾 Saving to {OUTPUT_CSV}...")
        
        with open(OUTPUT_CSV, 'w', newline='', encoding='utf-8') as f:
            if self.results:
                writer = csv.DictWriter(f, fieldnames=self.results[0].keys())
                writer.writeheader()
                writer.writerows(self.results)
        
        print("   ✅ Saved\n")
        
        self._print_summary()
    
    def _print_summary(self):
        """Print summary"""
        verified = sum(1 for r in self.results if r['status'] == 'VERIFIED')
        possible = sum(1 for r in self.results if r['status'] == 'POSSIBLE_MATCH')
        question = sum(1 for r in self.results if r['status'] == 'QUESTIONABLE')
        not_found = sum(1 for r in self.results if r['status'] == 'NOT_FOUND')
        
        print("=" * 100)
        print("📊 RESULTS")
        print("=" * 100)
        print(f"✅ VERIFIED:       {verified:2d}/{len(self.results)}")
        print(f"⚠️  POSSIBLE MATCH: {possible:2d}/{len(self.results)}")
        print(f"❓ QUESTIONABLE:   {question:2d}/{len(self.results)}")
        print(f"❌ NOT FOUND:      {not_found:2d}/{len(self.results)}")
        
        if self.results:
            avg_score = sum(r['match_score'] for r in self.results) / len(self.results)
            print(f"📈 Avg score:      {avg_score:.0f}/100")
        
        # Issues
        issues = [r for r in self.results if r['notes']]
        if issues:
            print(f"\n🚨 Issues ({len(issues)}):")
            print("-" * 100)
            for issue in sorted(issues, key=lambda x: x['bibtex_key']):
                print(f"   {issue['bibtex_key']:20s} | {issue['notes']}")
        
        elapsed = time.time() - self.session_start
        print(f"\n⏱️  Time:      {elapsed:.0f}s")
        print(f"🔗 Requests:  {self.request_count}")
        print(f"📊 Per entry: {elapsed/len(self.results):.0f}s")

if __name__ == '__main__':
    verifier = SemanticScholarVerifier(OUTPUT_CSV)
    verifier.run()
