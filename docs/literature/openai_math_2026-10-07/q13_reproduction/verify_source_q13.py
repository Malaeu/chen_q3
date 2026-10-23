"""Verify the authoritative Q13 bytes and all embedded source bodies."""
from pathlib import Path
import hashlib
import json
import sys

EXPECTED_BYTES = 195525
EXPECTED_LF = 3255
EXPECTED_SHA256 = 'f7a1dfc6954ea989f91bc101578e7b31408a70b37c878a4bfee3b7167a16118c'

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 verify_source_q13.py <authoritative-Q13.txt>')
    source = Path(sys.argv[1])
    raw = source.read_bytes()
    observed = hashlib.sha256(raw).hexdigest()
    if (len(raw), raw.count(b'\n'), observed) != (EXPECTED_BYTES, EXPECTED_LF, EXPECTED_SHA256):
        raise SystemExit('FAIL: source bytes differ from the audited packet')
    manifest = json.loads(Path(__file__).with_name('manifest.json').read_text(encoding='utf-8'))
    for item in manifest:
        marker = ('## File: ' + item['path'] + '\n\n').encode('utf-8')
        if raw.count(marker) != 1:
            raise SystemExit('FAIL: nonunique source marker: ' + item['path'])
        start = raw.index(marker) + len(marker)
        body = raw[start:start + item['bytes']]
        if len(body) != item['bytes'] or hashlib.sha256(body).hexdigest() != item['sha256']:
            raise SystemExit('FAIL: embedded body mismatch: ' + item['path'])
    print(json.dumps({'status':'MATCH_SOURCE_BYTES_NOT_MATHEMATICAL_PROOF',
                      'bytes':len(raw),'LF':raw.count(b'\n'),'sha256':observed,
                      'embedded_bodies':len(manifest)}, indent=2))

if __name__ == '__main__':
    main()
