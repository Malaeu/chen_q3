#!/usr/bin/env python3
"""Replay the frozen local search; failed attempts never become accepted theorems."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--out', required=True, type=Path)
args = parser.parse_args()
args.out.mkdir(parents=True, exist_ok=False)
here = Path(__file__).resolve().parent
project = here.parents[1] / 'q3.lean.aristotle'
rows = []
with tempfile.TemporaryDirectory(prefix='ccm-quarter-') as scratch:
    for name in ['target_and_control', '01_exact_search', '02_aesop', '03_simp',
                 '04_unfold_full_entry_then_aesop']:
        source = Path(scratch) / (name + '.lean')
        source.write_bytes((here / (name + '.lean.txt')).read_bytes())
        with (args.out / (name + '.log.txt')).open('w') as log:
            try:
                result = subprocess.run(['lake', 'env', 'lean', str(source)],
                    cwd=project, stdout=log, stderr=subprocess.STDOUT, timeout=45)
                row = {'name': name, 'returncode': result.returncode, 'timed_out': False}
            except subprocess.TimeoutExpired:
                row = {'name': name, 'returncode': None, 'timed_out': True}
        rows.append(row)
        if name == 'target_and_control' and row['returncode'] != 0:
            break
(args.out / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
print(json.dumps(rows, indent=2))
