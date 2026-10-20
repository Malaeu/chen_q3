#!/usr/bin/env python3
"""Summarize frozen interval outputs without fitting or modifying candidates."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sign(interval):
    lo, hi = Fraction(interval['lower']), Fraction(interval['upper'])
    assert lo <= hi
    return 'POSITIVE' if lo > 0 else 'NEGATIVE' if hi < 0 else 'UNRESOLVED_CONTAINS_ZERO'


def midpoint(interval):
    return float((Fraction(interval['lower']) + Fraction(interval['upper'])) / 2)


def main():
    rows, hashes = [], {}
    provenance = None
    max_width = Fraction(0)
    for filename in ('main.json', 'heldout.json'):
        path = ROOT / filename
        raw = path.read_bytes()
        hashes[filename] = hashlib.sha256(raw).hexdigest()
        payload = json.loads(raw)
        current = {k: payload['provenance'][k] for k in (
            'source_commit', 'new_evaluator_sha256', 'old_evaluator_sha256',
            'periodic_python_sha256', 'periodic_cpp_sha256', 'plan_sha256')}
        if provenance is None:
            provenance = current
        assert provenance == current, 'Main and heldout code/plan differ'
        for row in payload['rows']:
            assert all(v for k, v in row['formula_checks'].items() if k.endswith('_C') and isinstance(v, bool))
            full = row['full_C']
            max_width = max(max_width, Fraction(full['upper']) - Fraction(full['lower']))
            mixed = row['baselines']['additive_singleton_h']['omitted_mixed_h']
            zero = row['baselines']['zero_response']['weighted_omitted_h_residual']
            add = row['baselines']['additive_singleton_h']['weighted_omitted_h_residual']
            zero_status = ('STRUCTURAL_EXACT' if row['counts']['amp'] == 1
                           else 'REFUTED' if sign(zero) != 'UNRESOLVED_CONTAINS_ZERO'
                           else 'UNRESOLVED')
            add_status = ('STRUCTURAL_EXACT' if not mixed
                          else 'REFUTED' if sign(add) != 'UNRESOLVED_CONTAINS_ZERO'
                          else 'UNRESOLVED')
            rows.append(dict(id=row['id'], stage=row['stage'], **row['configuration'],
                A=row['counts']['amp'], C_midpoint=midpoint(full),
                response_midpoint=midpoint(row['components']['A_response']),
                response_sign=sign(row['components']['A_response']),
                G_midpoint=midpoint(row['components']['G_H']),
                zero_residual_midpoint=midpoint(zero), zero_baseline_status=zero_status,
                additive_residual_midpoint=midpoint(add), additive_baseline_status=add_status,
                raw_N=row['parameters']['raw_disk_N']))
    result = dict(scope='OFF_SCHEDULE_MASK_DIAGNOSTIC', input_sha256=hashes,
                  common_provenance=provenance, max_C_interval_width=str(max_width), rows=rows,
                  CF22='UNCHANGED_CONDITIONAL', RH='NOT_PROVED', new_fits=0)
    output = ROOT / 'summary.json'
    with output.open('x') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    for row in rows:
        if row['orientation'] == 1:
            print(row['id'], 'A=',row['A'], 'C=',row['C_midpoint'],
                  'response=',row['response_midpoint'], 'zero_err=',row['zero_residual_midpoint'],
                  'add_err=',row['additive_residual_midpoint'], 'G=',row['G_midpoint'], 'N=',row['raw_N'])
    print('max C width:', float(max_width))


if __name__ == '__main__':
    main()
