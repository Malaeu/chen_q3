"""Verify exact-byte SHA256SUMS; run from any working directory."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
count = 0
for line in (root / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f'SHA256 mismatch: {name}')
    count += 1
print(f'PASS: {count} exact-byte SHA256 checks')
