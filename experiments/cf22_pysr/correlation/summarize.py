#!/usr/bin/env python3
"""Compact exact-interval summary of the saved pair decomposition; no fitting."""
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GROUPS = ('rough_rough', 'cross', 'affected_affected')


def mid(x):
    return float((Fraction(x['lower']) + Fraction(x['upper'])) / 2)


def width(x):
    return Fraction(x['upper']) - Fraction(x['lower'])


def main():
    path = ROOT / 'decomposition.json.gz'
    with gzip.open(path, 'rt') as h:
        data = json.load(h)
    rows = []
    for row in data['rows']:
        rows.append({
            'id': row['id'], 'configuration': row['configuration'], 'counts': row['counts'],
            'groups': row['groups'], 'C_pair_sum': row['C_pair_sum'], 'saved_C': row['full_C'],
            'reassembly_residual': row['three_groups_minus_full_C_residual'],
            'mask_correction_vs_same_P_A_copies': row['mask_correction_vs_same_P_A_copies'],
            'absolute_pair_diagnostic_only': row['absolute_pair_diagnostic_only'],
            'period_diagnostics': row['period_diagnostics'],
            'pairs_with_shared_zero_factor': sum(p['shared_zero_mask_gcd']['norm'] > 1 for p in row['pairs']),
        })
    payload = {
        'scope':data['scope'], 'source_commit':data['provenance']['pinned_input_commit'],
        'decomposition_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'summarizer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'panel_checks':data['panel_checks'],
        'total_unordered_pairs_across_all_configurations':sum(r['counts']['pair_count'] for r in rows),
        'max_saved_reassembly_residual_width':str(max(width(r['reassembly_residual']) for r in rows)),
        'rows':rows,
    }
    with (ROOT / 'summary.json').open('x') as h:
        json.dump(payload,h,indent=2);h.write('\n')
    for row in rows:
        if row['configuration']['orientation'] != 1: continue
        print(row['id'], 'groups', *(f'{mid(row["groups"][g]["C_contribution"]):+.12f}' for g in GROUPS),
              'C',f'{mid(row["C_pair_sum"]):+.12f}', 'mask',
              *(f'{mid(row["groups"][g]["mask_correction"]):+.12f}' for g in GROUPS),
              'H/Q', *(f'{mid(row["period_diagnostics"][k]):.7g}' for k in ('H_over_Q_min','H_over_Q_max')),
              'absPairs', f'{mid(row["absolute_pair_diagnostic_only"]["value"]):.6f}')
    print('pairs', payload['total_unordered_pairs_across_all_configurations'],
          'max residual width',float(Fraction(payload['max_saved_reassembly_residual_width'])))


if __name__ == '__main__':
    main()
