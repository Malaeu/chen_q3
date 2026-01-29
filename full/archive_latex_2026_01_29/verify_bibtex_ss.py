#!/usr/bin/env python3
"""
Semantic Scholar BibTeX Verification Tool (v2)
With proper exponential backoff for rate limiting
"""

import json
import time
import csv
import re
from pathlib import Path
from typing import Dict, Optional
import subprocess

# Configuration
BIBTEX_FILE = Path(__file__).parent / "references.bib"
OUTPUT_CSV = Path(__file__).parent / "semantic_scholar_verification.csv"

# Semantic Scholar API
SS_API_BASE = "https://api.semanticscholar.org/graph/v1"
SS_PAPER_SEARCH = f"{SS_API_BASE}/paper/search"
SS_PAPER_DETAILS = f"{SS_API_BASE}/paper"

class RateLimitHandler:
    """Handle rate limiting with exponential backoff"""
    
    def __init__(self, initial_delay=0.5, max_delay=60, max_retries=10):
        self.initial_delay = initial_delay
        self.max_delay = max_delay
        self.max_retries = max_retries
        self.last_request_time = 0
        self.request_count = 0
    
    def wait_before_request(self, min_delay=0.1):
        """Ensure minimum delay between requests"""
        elapsed = time.time() - self.last_request_time
        if elapsed < min_delay:
            time.sleep(min_delay - elapsed)
    
    def handle_response(self, http_code: int) -> tuple[bool, str]:
        """
        Handle HTTP response codes
        Returns: (should_retry, message)
        """
        if http_code == 200:
            return False, "OK"
        elif http_code == 429:
            return True, "Rate limit exceeded"
        elif http_code == 503:
            return True, "Service unavailable"
        elif http_code == 500:
            return True, "Server error"
        elif http_code == 400:
            return False, "Bad request (invalid query)"
        else:
            return False, f"HTTP {http_code}"
    
    def backoff_sleep(self, attempt: int) -> float:
        """Calculate exponential backoff with jitter"""
        import random
        delay = min(self.initial_delay * (2 ** attempt), self.max_delay)
        jitter = random.uniform(0, delay * 0.1)
        total_delay = delay + jitter
        return total_delay

class SemanticScholarVerifier:
    def __init__(self, output_csv: Path):
        self.output_csv = output_csv
        self.results = []
        self.rate_limiter = RateLimitHandler()
        self.session_start = time.time()
    
    def _make_request(self, url: str, params: Dict) -> Optional[Dict]:
        """Make HTTP request with retry logic"""
        
        for attempt in range(self.rate_limiter.max_retries):
            # Rate limit: be nice
            self.rate_limiter.wait_before_request(min_delay=0.1)
            
            # Build URL with params
            param_str = '&'.join([f"{k}={v}" for k, v in params.items()])
            full_url = f"{url}?{param_str}"
            
            try:
                # Use curl with timeout
                cmd = [
                    'curl', '-s', '-w', '\n%{http_code}',
                    '-H', 'User-Agent: Academic-BibTeX-Verifier',
                    full_url
                ]
                
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=20
                )
                
                # Parse response and HTTP code
                lines = result.stdout.strip().split('\n')
                http_code = int(lines[-1]) if lines else 0
                response_body = '\n'.join(lines[:-1]) if len(lines) > 1 else ''
                
                self.rate_limiter.last_request_time = time.time()
                self.rate_limiter.request_count += 1
                
                should_retry, msg = self.rate_limiter.handle_response(http_code)
                
                if http_code == 200:
                    try:
                        return json.loads(response_body)
                    except:
                        return None
                
                if should_retry and attempt < self.rate_limiter.max_retries - 1:
                    backoff = self.rate_limiter.backoff_sleep(attempt)
                    print(f"      ⏳ Rate limited ({msg}), waiting {backoff:.1f}s... (attempt {attempt + 1}/{self.rate_limiter.max_retries})")
                    time.sleep(backoff)
                    continue
                else:
                    print(f"      ❌ {msg} (HTTP {http_code})")
                    return None
            
            except subprocess.TimeoutExpired:
                print(f"      ❌ Timeout (attempt {attempt + 1})")
                if attempt < self.rate_limiter.max_retries - 1:
                    backoff = self.rate_limiter.backoff_sleep(attempt)
                    time.sleep(backoff)
                continue
            except Exception as e:
                print(f"      ❌ Error: {str(e)[:50]}")
                return None
        
        return None
    
    def search_paper(self, title: str, year: Optional[int] = None, authors: str = "") -> Optional[Dict]:
        """Search for paper by title, year, and authors"""
        
        # Build query
        query_parts = [title]
        if year:
            query_parts.append(str(year))
        if authors:
            query_parts.append(authors.split(',')[0])  # First author
        
        query = ' '.join(query_parts)
        
        params = {
            'query': query,
            'limit': '5',
            'fields': 'paperId,title,authors,year,venue,doi,externalIds,citationCount'
        }
        
        print(f"    🔍 Searching: '{query[:50]}...'")
        response = self._make_request(SS_PAPER_SEARCH, params)
        
        if response and 'data' in response and len(response['data']) > 0:
            papers = response['data']
            
            # Find best match: prioritize year match
            best_match = papers[0]
            if year:
                for paper in papers:
                    if paper.get('year') == year:
                        best_match = paper
                        break
            
            return best_match
        
        return None
    
    def verify_entry(self, key: str, bibtex_data: Dict) -> Dict:
        """Verify single BibTeX entry"""
        
        print(f"\n📄 [{self.rate_limiter.request_count}] Verifying: {key}")
        
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
        title = bibtex_data.get('title', '').strip('{}')
        if not title:
            result['notes'] = 'Empty title'
            print(f"  ⚠️  Empty title")
            return result
        
        year = bibtex_data.get('year', '').strip()
        year_int = int(year) if year and year.isdigit() else None
        authors = bibtex_data.get('author', '').strip()
        
        # Search Semantic Scholar
        paper = self.search_paper(title, year_int, authors)
        
        if not paper:
            result['status'] = 'NOT_FOUND'
            print(f"  ❌ Not found in Semantic Scholar")
            return result
        
        # Extract results
        result['ss_title'] = paper.get('title', '')
        result['ss_year'] = str(paper.get('year', ''))
        
        # Authors
        ss_authors = paper.get('authors', [])
        author_names = ', '.join([a.get('name', '') for a in ss_authors[:3]])
        result['ss_authors'] = author_names + ('...' if len(ss_authors) > 3 else '')
        
        # DOI
        external_ids = paper.get('externalIds', {})
        result['ss_doi'] = external_ids.get('DOI', '')
        
        # Citations
        result['ss_citations'] = str(paper.get('citationCount', 'N/A'))
        
        # Match scoring
        match_score = 100
        
        # Title match (fuzzy)
        title_lower = title.lower()
        ss_title_lower = result['ss_title'].lower()
        if title_lower not in ss_title_lower and ss_title_lower not in title_lower:
            match_score -= 25
            result['notes'] += 'TITLE_MISMATCH; '
        
        # Year match
        if year_int and result['ss_year'] and str(year_int) != result['ss_year']:
            match_score -= 20
            result['notes'] += f'YEAR_MISMATCH({year_int}vs{result['ss_year']}); '
        
        # DOI match
        bibtex_doi = bibtex_data.get('doi', '').lower()
        ss_doi = (result['ss_doi'] or '').lower()
        if bibtex_doi and ss_doi and bibtex_doi != ss_doi:
            match_score -= 15
            result['notes'] += 'DOI_MISMATCH; '
        
        result['match_score'] = max(match_score, 0)
        
        if result['match_score'] >= 75:
            result['status'] = 'VERIFIED'
            print(f"  ✅ VERIFIED (score: {result['match_score']}, citations: {result['ss_citations']})")
        elif result['match_score'] >= 50:
            result['status'] = 'POSSIBLE_MATCH'
            print(f"  ⚠️  POSSIBLE_MATCH (score: {result['match_score']})")
        else:
            result['status'] = 'QUESTIONABLE'
            print(f"  ⚠️  QUESTIONABLE (score: {result['match_score']})")
        
        return result
    
    def parse_bibtex(self) -> Dict[str, Dict]:
        """Parse BibTeX file - improved parser"""
        entries = {}
        
        with open(BIBTEX_FILE, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Find all @type{key, ... }
        pattern = r'@(\w+)\s*\{\s*([^,]+?)\s*,\s*(.*?)\n\}'
        matches = re.finditer(pattern, content, re.DOTALL | re.IGNORECASE)
        
        for match in matches:
            entry_type = match.group(1)
            key = match.group(2).strip()
            fields_text = match.group(3)
            
            fields = {}
            
            # Parse individual fields: key = value or key = {value}
            field_pattern = r'(\w+)\s*=\s*(?:\{([^}]*)\}|"([^"]*)"|([^,}]*))'
            
            for field_match in re.finditer(field_pattern, fields_text):
                field_name = field_match.group(1).strip().lower()
                # Get value from one of the three groups
                field_value = (field_match.group(2) or field_match.group(3) or field_match.group(4) or '').strip()
                
                if field_value:
                    fields[field_name] = field_value
            
            if 'title' in fields and 'author' in fields:
                entries[key] = fields
        
        return entries
    
    def run(self):
        """Run full verification"""
        print("🚀 Semantic Scholar BibTeX Verification Tool (v2)")
        print("=" * 70)
        print(f"📋 Input:  {BIBTEX_FILE}")
        print(f"📊 Output: {OUTPUT_CSV}")
        print("=" * 70)
        
        # Parse BibTeX
        print("\n📖 Parsing BibTeX...")
        entries = self.parse_bibtex()
        print(f"   ✅ Found {len(entries)} valid entries")
        
        if not entries:
            print("   ❌ No entries found!")
            return
        
        # Verify each entry
        print(f"\n🔍 Verifying against Semantic Scholar API...")
        print("-" * 70)
        
        for key in sorted(entries.keys()):
            result = self.verify_entry(key, entries[key])
            self.results.append(result)
        
        # Save results
        print("\n" + "=" * 70)
        print(f"💾 Writing results to {OUTPUT_CSV}...")
        
        with open(OUTPUT_CSV, 'w', newline='', encoding='utf-8') as f:
            if self.results:
                writer = csv.DictWriter(f, fieldnames=self.results[0].keys())
                writer.writeheader()
                writer.writerows(self.results)
        
        # Print summary
        self._print_summary()
    
    def _print_summary(self):
        """Print summary statistics"""
        verified = sum(1 for r in self.results if r['status'] == 'VERIFIED')
        possible = sum(1 for r in self.results if r['status'] == 'POSSIBLE_MATCH')
        questionable = sum(1 for r in self.results if r['status'] == 'QUESTIONABLE')
        not_found = sum(1 for r in self.results if r['status'] == 'NOT_FOUND')
        
        print("\n" + "=" * 70)
        print("📊 SUMMARY")
        print("=" * 70)
        print(f"✅ VERIFIED:       {verified}/{len(self.results)}")
        print(f"⚠️  POSSIBLE MATCH: {possible}/{len(self.results)}")
        print(f"❓ QUESTIONABLE:   {questionable}/{len(self.results)}")
        print(f"❌ NOT FOUND:      {not_found}/{len(self.results)}")
        
        if self.results:
            avg_score = sum(r['match_score'] for r in self.results) / len(self.results)
            print(f"📈 Average score:  {avg_score:.1f}/100")
        
        # Issues found
        issues = [r for r in self.results if r['notes']]
        if issues:
            print(f"\n🚨 Issues found: {len(issues)}")
            print("-" * 70)
            for issue in sorted(issues, key=lambda x: x['bibtex_key']):
                print(f"   {issue['bibtex_key']:20s} | {issue['notes']}")
        
        elapsed = time.time() - self.session_start
        print(f"\n⏱️  Session time:   {elapsed:.1f}s")
        print(f"🔗 API requests:   {self.rate_limiter.request_count}")
        print(f"📊 Avg per entry:  {elapsed/len(self.results):.2f}s")

if __name__ == '__main__':
    verifier = SemanticScholarVerifier(OUTPUT_CSV)
    verifier.run()
