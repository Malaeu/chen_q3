#!/usr/bin/env python3
"""
Semantic Scholar BibTeX Verification Tool (v3)
With URL encoding fix and LaTeX special character handling
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

SS_API_BASE = "https://api.semanticscholar.org/graph/v1"
SS_PAPER_SEARCH = f"{SS_API_BASE}/paper/search"

class RateLimitHandler:
    """Handle rate limiting with exponential backoff"""
    
    def __init__(self, initial_delay=2, max_delay=120, max_retries=10):
        self.initial_delay = initial_delay
        self.max_delay = max_delay
        self.max_retries = max_retries
        self.last_request_time = 0
        self.request_count = 0
    
    def wait_before_request(self, min_delay=10):
        """Ensure minimum delay between requests (10s for Semantic Scholar)"""
        elapsed = time.time() - self.last_request_time
        if elapsed < min_delay:
            wait_time = min_delay - elapsed
            print(f"    ⏳ Waiting {wait_time:.1f}s before next request...")
            time.sleep(wait_time)
    
    def handle_response(self, http_code: int) -> tuple:
        """Handle HTTP codes: (should_retry, message)"""
        if http_code == 200:
            return False, "OK"
        elif http_code == 429:
            return True, "Rate limit (429)"
        elif http_code == 503:
            return True, "Service unavailable (503)"
        elif http_code == 500:
            return True, "Server error (500)"
        elif http_code == 400:
            return False, "Bad request (400)"
        elif http_code == 0:
            return True, "Connection error"
        else:
            return False, f"HTTP {http_code}"
    
    def backoff_sleep(self, attempt: int) -> float:
        """Exponential backoff with jitter"""
        import random
        delay = min(self.initial_delay * (2 ** attempt), self.max_delay)
        jitter = random.uniform(0, delay * 0.1)
        return delay + jitter

class SemanticScholarVerifier:
    
    @staticmethod
    def clean_latex_title(title: str) -> str:
        """Remove LaTeX special chars from title"""
        # Remove common LaTeX commands
        title = re.sub(r'\{\\[a-z]+\{([^}]*)\}\}', r'\1', title)  # {\v{s}} -> s
        title = re.sub(r'\{\\\'([aeiouAEIOU])\}', r'\1', title)    # {\'e} -> e
        title = re.sub(r'\{\\`([aeiouAEIOU])\}', r'\1', title)     # {\`e} -> e
        title = re.sub(r'\{\\"([aeiouAEIOU])\}', r'\1', title)     # {\"o} -> o
        title = re.sub(r'\{\\~([a-zA-Z])\}', r'\1', title)        # {\~n} -> n
        title = re.sub(r'\{\\c\{([a-zA-Z])\}\}', r'\1', title)    # {\c{c}} -> c
        title = re.sub(r'\{\\[a-z]+ ', '', title)                  # Remove other LaTeX
        title = re.sub(r'[{}]', '', title)                         # Remove braces
        title = re.sub(r'\{[Rr]', 'R', title)                      # {R -> R
        title = re.sub(r'\{[Dd]', 'D', title)                      # {D -> D
        title = re.sub(r'\{[Mm]', 'M', title)                      # {M -> M
        title = re.sub(r'\{[Hh]', 'H', title)                      # {H -> H
        title = title.strip()
        return title
    
    def __init__(self, output_csv: Path):
        self.output_csv = output_csv
        self.results = []
        self.rate_limiter = RateLimitHandler()
        self.session_start = time.time()
    
    def _make_request(self, url: str, query: str) -> Optional[Dict]:
        """Make HTTP request with retry and exponential backoff"""
        
        for attempt in range(self.rate_limiter.max_retries):
            self.rate_limiter.wait_before_request(min_delay=10)  # 10 second delay
            
            try:
                # Properly URL-encode the query
                params = {
                    'query': query,
                    'limit': '5',
                    'fields': 'paperId,title,authors,year,venue,doi,externalIds,citationCount'
                }
                
                # Build properly encoded URL
                query_string = urllib.parse.urlencode(params, safe='')
                full_url = f"{url}?{query_string}"
                
                # Use curl
                cmd = [
                    'curl', '-s', '-w', '\n%{http_code}',
                    '-H', 'User-Agent: Academic-BibTeX-Verifier/1.0',
                    '--max-time', '15',
                    full_url
                ]
                
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=20)
                
                # Parse response
                lines = result.stdout.strip().split('\n')
                
                try:
                    http_code = int(lines[-1])
                except (ValueError, IndexError):
                    http_code = 0
                
                response_body = '\n'.join(lines[:-1]) if len(lines) > 1 else ''
                
                self.rate_limiter.last_request_time = time.time()
                self.rate_limiter.request_count += 1
                
                should_retry, msg = self.rate_limiter.handle_response(http_code)
                
                if http_code == 200:
                    try:
                        return json.loads(response_body)
                    except json.JSONDecodeError:
                        print(f"      ❌ JSON parse error")
                        return None
                
                if should_retry and attempt < self.rate_limiter.max_retries - 1:
                    backoff = self.rate_limiter.backoff_sleep(attempt)
                    print(f"      ⏳ {msg}, waiting {backoff:.1f}s (attempt {attempt+1}/{self.rate_limiter.max_retries})")
                    time.sleep(backoff)
                    continue
                else:
                    if http_code != 200:
                        print(f"      ❌ {msg}")
                    return None
            
            except subprocess.TimeoutExpired:
                print(f"      ❌ Timeout (attempt {attempt + 1})")
                if attempt < self.rate_limiter.max_retries - 1:
                    time.sleep(self.rate_limiter.backoff_sleep(attempt))
                continue
            except Exception as e:
                print(f"      ❌ Error: {str(e)[:40]}")
                return None
        
        return None
    
    def verify_entry(self, key: str, bibtex_data: Dict) -> Dict:
        """Verify BibTeX entry against Semantic Scholar"""
        
        print(f"\n📄 [{self.rate_limiter.request_count:2d}] {key}")
        
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
            print(f"  ⚠️  No title")
            return result
        
        # Clean LaTeX from title
        title_clean = self.clean_latex_title(title)
        
        year = bibtex_data.get('year', '').strip()
        year_int = int(year) if year and year.isdigit() else None
        
        # Build search query
        query_parts = [title_clean]
        if year_int:
            query_parts.append(str(year_int))
        
        query = ' '.join(query_parts)
        
        print(f"    🔍 Query: '{query[:55]}...'")
        
        # Search
        response = self._make_request(SS_PAPER_SEARCH, query)
        
        if not response or 'data' not in response or len(response.get('data', [])) == 0:
            print(f"  ❌ Not found")
            return result
        
        # Find best match
        papers = response['data']
        best_match = papers[0]
        
        # Prefer year match if available
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
        author_names = ', '.join([a.get('name', '') for a in ss_authors[:3]])
        result['ss_authors'] = author_names + ('...' if len(ss_authors) > 3 else '')
        
        # DOI
        external_ids = best_match.get('externalIds', {})
        result['ss_doi'] = external_ids.get('DOI', '')
        
        # Citations
        result['ss_citations'] = str(best_match.get('citationCount', 0))
        
        # Score matching
        match_score = 100
        
        # Title matching
        title_lower = title_clean.lower()
        ss_title_lower = result['ss_title'].lower()
        
        if title_lower not in ss_title_lower and ss_title_lower not in title_lower:
            match_score -= 25
            result['notes'] += 'TITLE_MISMATCH; '
        
        # Year matching
        if year_int and result['ss_year'] and str(year_int) != result['ss_year']:
            match_score -= 20
            result['notes'] += f'YEAR_DIFF({year_int}→{result['ss_year']}); '
        
        # DOI matching
        bibtex_doi = bibtex_data.get('doi', '').lower()
        ss_doi = (result['ss_doi'] or '').lower()
        if bibtex_doi and ss_doi and bibtex_doi != ss_doi:
            match_score -= 15
            result['notes'] += 'DOI_DIFF; '
        
        result['match_score'] = max(match_score, 0)
        
        if result['match_score'] >= 75:
            result['status'] = 'VERIFIED'
            print(f"  ✅ VERIFIED (score {result['match_score']}, {result['ss_citations']} cites)")
        elif result['match_score'] >= 50:
            result['status'] = 'POSSIBLE_MATCH'
            print(f"  ⚠️  POSSIBLE (score {result['match_score']})")
        else:
            result['status'] = 'QUESTIONABLE'
            print(f"  ❓ QUESTIONABLE (score {result['match_score']})")
        
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
        print("🚀 Semantic Scholar BibTeX Verification (v3)")
        print("=" * 70)
        print(f"Input:  {BIBTEX_FILE}")
        print(f"Output: {OUTPUT_CSV}")
        print("=" * 70)
        
        print("\n📖 Parsing BibTeX...")
        entries = self.parse_bibtex()
        print(f"   Found {len(entries)} entries")
        
        if not entries:
            print("   ERROR: No entries!")
            return
        
        print(f"\n🔍 Verifying {len(entries)} entries against Semantic Scholar...")
        print("-" * 70)
        
        for key in sorted(entries.keys()):
            result = self.verify_entry(key, entries[key])
            self.results.append(result)
        
        print("\n" + "=" * 70)
        print(f"💾 Saving to {OUTPUT_CSV}...")
        
        with open(OUTPUT_CSV, 'w', newline='', encoding='utf-8') as f:
            if self.results:
                writer = csv.DictWriter(f, fieldnames=self.results[0].keys())
                writer.writeheader()
                writer.writerows(self.results)
        
        print("   ✅ Saved")
        
        self._print_summary()
    
    def _print_summary(self):
        """Print summary"""
        verified = sum(1 for r in self.results if r['status'] == 'VERIFIED')
        possible = sum(1 for r in self.results if r['status'] == 'POSSIBLE_MATCH')
        question = sum(1 for r in self.results if r['status'] == 'QUESTIONABLE')
        not_found = sum(1 for r in self.results if r['status'] == 'NOT_FOUND')
        
        print("\n" + "=" * 70)
        print("📊 RESULTS")
        print("=" * 70)
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
            print("-" * 70)
            for issue in sorted(issues, key=lambda x: x['bibtex_key']):
                print(f"   {issue['bibtex_key']:20s} | {issue['notes']}")
        
        elapsed = time.time() - self.session_start
        print(f"\n⏱️  Time:    {elapsed:.1f}s")
        print(f"🔗 Requests: {self.rate_limiter.request_count}")
        print(f"📊 Per entry: {elapsed/len(self.results):.2f}s")

if __name__ == '__main__':
    verifier = SemanticScholarVerifier(OUTPUT_CSV)
    verifier.run()
