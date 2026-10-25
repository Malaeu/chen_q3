"""Verify the byte-exact Q19 request and all ten embedded source bodies.
Usage: python3 verify_sources_q19.py /path/to/PROSHKA_CCM_COMPLEX_REFLECTION_PAIR_Q19_2026-10-25.txt
Only the supplied TXT is read; no repository or network access is used.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
NAME = 'PROSHKA_CCM_COMPLEX_REFLECTION_PAIR_Q19_2026-10-25.txt'
EXPECTED_BYTES = 199462
EXPECTED_LF = 3432
EXPECTED_SHA = '812017cb16df1b0687d8be1854eb57c97e002f47b9f25de0e3c63dfe7223a6f2'


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 verify_sources_q19.py /path/to/' + NAME)
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    raw.decode('utf-8', errors='strict')
    assert len(raw) == EXPECTED_BYTES, ('request bytes', len(raw))
    assert raw.count(b'\n') == EXPECTED_LF, ('request LF', raw.count(b'\n'))
    assert digest(raw) == EXPECTED_SHA, ('request sha256', digest(raw))
    assert raw.endswith(b'\n'), 'missing final LF'
    rows = re.findall(
        rb'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$',
        raw, flags=re.MULTILINE,
    )
    assert len(rows) == 10, ('manifest count', len(rows))
    sources = []
    for sid, source_path, size, sha in rows:
        start_marker = b'BEGIN_SOURCE ' + sid + b' ' + source_path + b'\n'
        assert raw.count(start_marker) == 1, ('start marker', sid)
        start = raw.index(start_marker) + len(start_marker)
        end = start + int(size)
        body = raw[start:end]
        assert digest(body).encode('ascii') == sha, ('body SHA', sid)
        assert raw[end:].startswith(b'\nEND_SOURCE ' + sid + b'\n'), ('end marker', sid)
        body.decode('utf-8', errors='strict')
        first = raw[:start].count(b'\n') + 1
        last = first + body.count(b'\n') - int(body.endswith(b'\n'))
        sources.append({
            'id': sid.decode(), 'path': source_path.decode(),
            'bytes': len(body), 'sha256': digest(body),
            'first_line': first, 'last_line': last,
        })
    result = {
        'request_file': NAME, 'bytes': len(raw), 'lf': raw.count(b'\n'),
        'sha256': digest(raw), 'final_lf': raw.endswith(b'\n'), 'sources': sources,
    }
    (ROOT / 'source_manifest.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8'
    )
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
