#!/usr/bin/env python3
"""
Semantic Scholar BibTeX Verification Tool
Verifies all entries in references.bib against Semantic Scholar API
"""

import json
import time
import csv
import sys
from pathlib import Path
from typing import Dict, List, Optional
import subprocess
import re

# Configuration
BIBTEX_FILE = Path(__file__).parent / "references.bib"
OUTPUT_CSV = Path(__file__).parent / "semantic_scholar_verification.csv"
API_DELAY = 1  # seconds between requests (be nice to API)
MAX_RETRIES = 3

# Semantic Scholar API endpoints
SS_API_BASE = "https://api.semanticscholar.org/graph/v1"
SS_PAPER_SEARCH = f"{SS_API_BASE}/paper/search"
SS_PAPER_DETAILS = f"{SS_API_BASE}/paper"

class SemanticScholarVerifier:
    def __init__(self, output_csv: Path):
        self.output_csv = output_csv
        self.results = []
        self.request_count = 0
        
    def _http_request(self, url: str, params: Dict = None) -> Optional[Dict]:
        """Make HTTP request to API using curl"""
        try:
            # Use curl for better control
            cmd = ['curl', '-s', '-H', 'User-Agent: Academic Research']
            
            # Add parameters
            if params:
                query_str = '&'.join([f"{k}={v}" for k, v in params.items()])
                url = f"{url}?{query_str}"
            
            cmd.append(url)
            
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
            
            if result.returncode == 0:
                data = json.loads(result.stdout)
                self.request_count += 1
                time.sleep(API_DELAY)  # Rate limiting
                return data
            else:
                print(f"  ❌ Curl error: {result.stderr[:100]}")
                return None
        except Exception as e:
            print(f"  ❌ Error: {e}")
            return None
    
    def search_paper(self, query: str, year: Optional[int] = None) -> Optional[Dict]:
        """Search for paper by title/authors"""
        try:
            # Build query string
            query_str = query
            if year:
                query_str += f" {year}"
            
            params = {
                'query': query_str,
                'limit': '5',
                'fields': 'paperId,title,authors,year,venue,doi,externalIds'
            }
            
            print(f"    🔍 Searching: {query_str[:60]}...")
            result = self._http_request(SS_PAPER_SEARCH, params)
            
            if result and 'data' in result and len(result['data']) > 0:
                papers = result['data']
                # Return best match (usually first)
                return papers[0]
            return None
        except Exception as e:
            print(f"    ❌ Search failed: {e}")
            return None
    
    def get_paper_details(self, paper_id: str) -> Optional[Dict]:
        """Get full details of paper by ID"""
        try:
            url = f"{SS_PAPER_DETAILS}/{paper_id}"
            params = {
                'fields': 'paperId,title,authors,year,venue,doi,externalIds,citationCount,isOpenAccess'
            }
            
            result = self._http_request(url, params)
            return result
        except Exception as e:
            print(f"    ❌ Details fetch failed: {e}")
            return None
    
    def verify_entry(self, key: str, bibtex_data: Dict) -> Dict:
        """Verify single BibTeX entry against Semantic Scholar"""
        print(f"\n📄 Verifying: {key}")
        
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
        
        # Search by title + year
        title = bibtex_data.get('title', '').strip('{}')
        if not title:
            result['notes'] = 'No title in BibTeX'
            return result
        
        year = bibtex_data.get('year')
        year_int = int(year) if year and year.isdigit() else None
        
        # Search Semantic Scholar
        for attempt in range(MAX_RETRIES):
            paper = self.search_paper(title, year_int)
            
            if paper:
                result['ss_title'] = paper.get('title', '')
                result['ss_year'] = str(paper.get('year', ''))
                
                # Get authors
                authors = paper.get('authors', [])
                author_names = ', '.join([a.get('name', '') for a in authors[:3]])
                result['ss_authors'] = author_names + ('...' if len(authors) > 3 else '')
                
                # Get DOI
                external_ids = paper.get('externalIds', {})
                result['ss_doi'] = external_ids.get('DOI', '')
                
                # Calculate match score
                match_score = 100  # Start optimistic
                
                # Title match
                bibtex_title_lower = title.lower()
                ss_title_lower = result['ss_title'].lower()
                if bibtex_title_lower not in ss_title_lower and ss_title_lower not in bibtex_title_lower:
                    match_score -= 20
                
                # Year match
                if year_int and result['ss_year'] and str(year_int) != result['ss_year']:
                    match_score -= 15
                    result['notes'] += f"YEAR MISMATCH: {year_int} vs {result['ss_year']}; "
                
                # DOI match
                if 'doi' in bibtex_data and bibtex_data['doi']:
                    if bibtex_data['doi'].lower() != (result['ss_doi'] or '').lower():
                        match_score -= 10
                        result['notes'] += f"DOI MISMATCH; "
                
                result['match_score'] = max(match_score, 0)
                
                if result['match_score'] >= 70:
                    result['status'] = 'VERIFIED'
                    print(f"  ✅ VERIFIED (score: {result['match_score']})")
                    
                    # Get citation count
                    details = self.get_paper_details(paper.get('paperId'))
                    if details:
                        result['ss_citations'] = str(details.get('citationCount', 'N/A'))
                        print(f"     Citations: {result['ss_citations']}")
                    
                    return result
                else:
                    result['status'] = 'POSSIBLE_MATCH'
                    print(f"  ⚠️  POSSIBLE MATCH (score: {result['match_score']})")
                    return result
            
            if attempt < MAX_RETRIES - 1:
                print(f"    ⏳ Retry {attempt + 1}/{MAX_RETRIES - 1}...")
                time.sleep(API_DELAY * 2)
        
        result['status'] = 'NOT_FOUND'
        result['notes'] = 'Not found in Semantic Scholar'
        print(f"  ❌ NOT FOUND in Semantic Scholar")
        return result
    
    def parse_bibtex(self) -> Dict[str, Dict]:
        """Parse BibTeX file"""
        entries = {}
        
        with open(BIBTEX_FILE, 'r') as f:
            content = f.read()
        
        # Simple BibTeX parser (handles basic cases)
        import re
        
        # Find all @article, @book, etc.
        pattern = r'@(\w+)\{([^,]+),\s*(.*?)\n\}'
        matches = re.finditer(pattern, content, re.DOTALL)
        
        for match in matches:
            entry_type = match.group(1)
            key = match.group(2).strip()
            fields_text = match.group(3)
            
            fields = {}
            # Parse fields
            field_pattern = r'(\w+)\s*=\s*[{"]?([^,}]+)[}"]?'
            for field_match in re.finditer(field_pattern, fields_text):
                field_name = field_match.group(1).strip().lower()
                field_value = field_match.group(2).strip().strip('{}\"')
                fields[field_name] = field_value
            
            entries[key] = fields
        
        return entries
    
    def run(self):
        """Run verification"""
        print("🚀 Semantic Scholar BibTeX Verification Tool")
        print("=" * 60)
        print(f"📋 BibTeX file: {BIBTEX_FILE}")
        print(f"📊 Output CSV: {OUTPUT_CSV}")
        print("=" * 60)
        
        # Parse BibTeX
        print("\n📖 Parsing BibTeX...")
        entries = self.parse_bibtex()
        print(f"   Found {len(entries)} entries")
        
        # Verify each entry
        print("\n🔍 Verifying entries against Semantic Scholar...")
        print("-" * 60)
        
        for key in sorted(entries.keys()):
            result = self.verify_entry(key, entries[key])
            self.results.append(result)
        
        # Write results to CSV
        print("\n" + "=" * 60)
        print(f"💾 Writing results to {OUTPUT_CSV}")
        
        with open(OUTPUT_CSV, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=self.results[0].keys())
            writer.writeheader()
            writer.writerows(self.results)
        
        # Print summary
        self._print_summary()
        
        print(f"\n✅ Total API requests: {self.request_count}")
        print(f"⏱️  Rate limit: {API_DELAY}s between requests")
    
    def _print_summary(self):
        """Print summary statistics"""
        verified = sum(1 for r in self.results if r['status'] == 'VERIFIED')
        possible = sum(1 for r in self.results if r['status'] == 'POSSIBLE_MATCH')
        not_found = sum(1 for r in self.results if r['status'] == 'NOT_FOUND')
        
        print("\n" + "=" * 60)
        print("📊 SUMMARY")
        print("=" * 60)
        print(f"✅ VERIFIED:       {verified}/{len(self.results)}")
        print(f"⚠️  POSSIBLE MATCH: {possible}/{len(self.results)}")
        print(f"❌ NOT FOUND:      {not_found}/{len(self.results)}")
        print(f"📈 Success rate:   {(verified/len(self.results)*100):.1f}%")
        
        # Issues found
        issues = [r for r in self.results if r['notes']]
        if issues:
            print(f"\n🚨 Issues found: {len(issues)}")
            for issue in issues:
                if issue['notes']:
                    print(f"   {issue['bibtex_key']}: {issue['notes']}")

if __name__ == '__main__':
    verifier = SemanticScholarVerifier(OUTPUT_CSV)
    verifier.run()
