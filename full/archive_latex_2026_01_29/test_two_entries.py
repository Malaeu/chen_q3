#!/usr/bin/env python3
"""Quick test of 2 BibTeX entries"""

import json
import time
import re
import urllib.parse
import subprocess
from typing import Dict, Optional

SS_API_BASE = "https://api.semanticscholar.org/graph/v1"
SS_PAPER_SEARCH = f"{SS_API_BASE}/paper/search"

def clean_latex_title(title: str) -> str:
    """Remove LaTeX special chars"""
    title = re.sub(r'\{\\[a-z]+\{([^}]*)\}\}', r'\1', title)
    title = re.sub(r'\{\\\'([aeiouAEIOU])\}', r'\1', title)
    title = re.sub(r'[{}]', '', title)
    title = re.sub(r'\{[A-Za-z]', '', title)
    return title.strip()

def make_request(query: str) -> Optional[Dict]:
    """Make API request with 10s delay"""
    time.sleep(10)
    
    params = {
        'query': query,
        'limit': '5',
        'fields': 'paperId,title,authors,year,citationCount,doi'
    }
    
    query_string = urllib.parse.urlencode(params, safe='')
    full_url = f"{SS_PAPER_SEARCH}?{query_string}"
    
    print(f"  🔗 URL: {full_url[:80]}...")
    
    cmd = ['curl', '-s', '-w', '\n%{http_code}', full_url]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=20)
    
    lines = result.stdout.strip().split('\n')
    try:
        http_code = int(lines[-1])
    except (ValueError, IndexError):
        http_code = 0
    
    response_body = '\n'.join(lines[:-1]) if len(lines) > 1 else ''
    
    print(f"  📊 HTTP {http_code}")
    
    if http_code == 200:
        try:
            return json.loads(response_body)
        except:
            return None
    return None

# Test data
test_entries = {
    'Edwards1974': {
        'title': "Riemann's Zeta Function",
        'authors': 'Harold M. Edwards',
        'year': '1974'
    },
    'Li1997': {
        'title': 'The positivity of a sequence of numbers and the Riemann hypothesis',
        'authors': 'Xian-Jin Li',
        'year': '1997'
    }
}

print("🚀 Testing 2 entries with 10s delay\n")
print("=" * 70)

for key, entry in test_entries.items():
    print(f"\n📄 Testing: {key}")
    print(f"   Title: {entry['title']}")
    print(f"   Year:  {entry['year']}")
    
    title_clean = clean_latex_title(entry['title'])
    query = f"{title_clean} {entry['year']}"
    
    print(f"   Query: {query}")
    
    response = make_request(query)
    
    if response and 'data' in response and len(response['data']) > 0:
        paper = response['data'][0]
        print(f"\n  ✅ FOUND!")
        print(f"     Title: {paper.get('title', 'N/A')[:60]}")
        print(f"     Year:  {paper.get('year', 'N/A')}")
        print(f"     Cites: {paper.get('citationCount', 'N/A')}")
        print(f"     DOI:   {paper.get('externalIds', {}).get('DOI', 'N/A')}")
    else:
        print(f"\n  ❌ NOT FOUND")
        if response:
            print(f"     Response: {json.dumps(response)[:100]}")

print("\n" + "=" * 70)
print("✅ Test complete!")
