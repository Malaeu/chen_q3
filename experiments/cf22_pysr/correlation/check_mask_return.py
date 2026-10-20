#!/usr/bin/env python3
"""Cross-check old mask corrections and structural unit cancellation."""
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import evaluate as source


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def factors(column):
    return tuple((tuple(f['prime_generator']), f['exponent']) for f in column['ideal']['factors'])


def main():
    inputs = [HERE/'decomposition.json.gz', HERE.parent/'nonunit/main.json',
              HERE.parent/'nonunit/heldout.json', HERE.parent/'evaluate.py']
    hashes = {str(p.relative_to(HERE.parent)):sha(p) for p in inputs}
    with gzip.open(inputs[0], 'rt') as h: data=json.load(h)
    old={r['id']:r for path in inputs[1:3] for r in json.loads(path.read_text())['rows']}
    matches=[]
    unit_checks=[]
    for row in data['rows']:
        a=row['mask_correction_vs_same_P_A_copies']
        b=old[row['id']]['baselines']['zero_response']['weighted_omitted_h_residual']
        assert max(Fraction(a['lower']),Fraction(b['lower'])) <= min(Fraction(a['upper']),Fraction(b['upper']))
        matches.append(row['id'])
        if row['configuration']['U']==48 and row['configuration']['P'] in (7,13):
            cross=[p for p in row['pairs'] if p['group']=='cross']
            eps=row['configuration']['orientation']
            for pair in cross:
                assert source.phase_index(factors(pair['left_column']),(1,1),eps) != source.phase_index(factors(pair['right_column']),(1,1),eps)
                assert pair['raw_pair_2re_exact']==0
            unit_checks.append({'id':row['id'],'cross_pairs':len(cross),
                                'all_unit_quotient_characters_nontrivial':True,
                                'all_saved_raw_pairs_exact_zero':True,
                                'structural_zero':'Full six-unit orbits with radial weights, sixthfree support and unit-invariant masks.'})
    assert hashes=={str(p.relative_to(HERE.parent)):sha(p) for p in inputs}
    result={'status':'PASS','input_sha256':hashes,'checker_sha256':sha(Path(__file__)),
            'old_mask_correction_matches':matches,'unit_cross_zero_checks':unit_checks}
    with (HERE/'mask_return_checks.json').open('x') as h:json.dump(result,h,indent=2);h.write('\n')
    print('PASS:',len(matches),'mask-return comparisons;',len(unit_checks),'structural cross-zero checks')


if __name__=='__main__':main()
