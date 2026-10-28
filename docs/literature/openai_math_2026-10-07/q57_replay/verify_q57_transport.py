#!/usr/bin/env python3
"""Verify Q57 request bytes and its 14 source frames; no mathematical code.
Usage: python3 verify_q57_transport.py PACKET.txt [OUTPUT.json]
Python 3.9+ standard library only. Does not execute any embedded source.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

SHA = '9325fefed57bfae1b3431c6cce374044d487e14c269176571017185dcffbb047'
SIZE, LF = 151894, 2493
NAME = 'PROSHKA_CCM_CONSTRUCTIVE_SIGNED_ARITHMETIC_Q57_2026-10-28.txt'
HEADER = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify(raw: bytes) -> dict:
    require(len(raw) == SIZE, 'outer size')
    require(raw.count(b'\n') == LF, 'outer LF')
    require(hashlib.sha256(raw).hexdigest() == SHA, 'outer SHA256')
    raw.decode('utf-8')
    require(b'\r' not in raw, 'unexpected CR')
    require(raw.startswith(b'REQUEST_ID: Q57_CONSTRUCTIVE_SIGNED_ARITHMETIC_BEFORE_CAUCHY\n'), 'request ID')
    pos = raw.index(b'BEGIN S1 ')
    headers = list(HEADER.finditer(raw[:pos]))
    require(len(headers) == 14, 'source count')
    rows = []
    for number, match in enumerate(headers, 1):
        sid, name, size, lf, sha = match.groups()
        require(int(sid) == number, 'source order')
        opening = b'BEGIN S' + sid + b' ' + name + b'\n'
        require(raw[pos:pos+len(opening)] == opening, 'source opening')
        start = pos + len(opening)
        end = start + int(size)
        body = raw[start:end]
        body.decode('utf-8')
        require(len(body) == int(size), 'source size')
        require(body.count(b'\n') == int(lf), 'source LF')
        require(hashlib.sha256(body).hexdigest().encode() == sha, 'source SHA256')
        closing = b'\nEND S' + sid + b'\n'
        require(raw[end:end+len(closing)] == closing, 'source closing')
        rows.append(dict(id='S'+sid.decode(), name=name.decode(), bytes=len(body),
                         lf=int(lf), sha256=sha.decode(),
                         start_line=raw[:start].count(b'\n')+1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(closing)
        if number < len(headers):
            require(raw[pos:pos+1] == b'\n', 'inter-frame separator')
            pos += 1
    require(pos == len(raw), 'trailing bytes')
    return dict(packet=NAME, bytes=SIZE, lf=LF, sha256=SHA,
                source_count=len(rows), all_frames_verified=True, sources=rows,
                historical_programs_executed=False,
                mathematical_computation=False, independent_audit=False,
                lean=False, arb_interval=False, production_spectrum=False)


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit('usage: python3 verify_q57_transport.py PACKET.txt [OUTPUT.json]')
    packet = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2] if len(sys.argv) == 3 else 'q57_transport.json').resolve()
    require(packet != output, 'refusing to overwrite the input')
    result = verify(packet.read_bytes())
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
