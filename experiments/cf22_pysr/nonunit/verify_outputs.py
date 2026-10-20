#!/usr/bin/env python3
"""Audit saved outputs; count disk elements independently via ideal norms."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def norm_disk_count(bound):
    # Number of ideals of norm n is sum_(d|n) chi_-3(d).
    # Prefix sum chi_-3(1..t) equals 1 exactly for t = 1 mod 3.
    total, start = 0, 1
    while start <= bound:
        quotient = bound // start
        end = bound // quotient
        total += quotient * (int(end % 3 == 1) - int((start - 1) % 3 == 1))
        start = end + 1
    return 6 * total


def overlaps(a, b):
    return max(Fraction(a['lower']), Fraction(b['lower'])) <= min(Fraction(a['upper']), Fraction(b['upper']))


def main():
    hashes, count_cache, all_rows = {}, {}, []
    freeze = json.loads((ROOT / 'heldout_freeze.json').read_text())
    for filename, digest in freeze['sha256'].items():
        assert hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() == digest
    for filename in ('main.json', 'heldout.json'):
        raw = (ROOT / filename).read_bytes()
        hashes[filename] = hashlib.sha256(raw).hexdigest()
        data = json.loads(raw)
        for row in data['rows']:
            all_rows.append(row)
            B = int(row['parameters']['raw_disk_B'])
            if B not in count_cache:
                count_cache[B] = norm_disk_count(B)
            assert count_cache[B] == int(row['parameters']['raw_disk_N'])
            matrix = row['raw_periodic_sum']['pair_2re']
            assert all(matrix[i][j] == matrix[j][i] for i in range(len(matrix)) for j in range(len(matrix)))
            for key, value in row['formula_checks'].items():
                if isinstance(value, bool):
                    assert value, (row['id'], key)
            assert Fraction(row['absolute_C_interval_width']) <= Fraction('1e-30')
            for key in ('formula_1_C','formula_2_C','formula_4_C'):
                assert overlaps(row['full_C'], row['formula_checks'][key])
    by_id = {row['id']:row for row in all_rows}
    for row in all_rows:
        if row['configuration']['orientation'] == 1:
            other = by_id[row['id'][:-1] + '-1']
            assert overlaps(row['full_C'], other['full_C'])
            assert row['raw_periodic_sum']['pair_2re'] == other['raw_periodic_sum']['pair_2re']
    result = {'status':'PASS', 'input_sha256':hashes, 'rows':len(all_rows),
              'independent_disk_counts':{str(k):v for k,v in count_cache.items()},
              'method':'6 sum_d chi_-3(d) floor(B/d), quotient grouping',
              'checks':['frozen input hashes','all exact norm disk counts','matrix symmetry',
                        'three C reconstructions','C width tolerance','orientation conjugacy'],
              'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with (ROOT / 'verification.json').open('x') as h:
        json.dump(result,h,indent=2);h.write('\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
