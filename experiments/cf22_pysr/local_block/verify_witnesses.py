#!/usr/bin/env python3
"""Replay two fixed same-feature, disjoint-output witnesses without the auditor."""
from fractions import Fraction as F
import gzip, hashlib, json, argparse
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
PIN='74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d'


def key(p):
    columns=[]
    for side in ('left_column','right_column'):
        c=p[side]
        columns.append((c['ideal']['norm'],c['mu'],tuple(sorted((f['prime_ideal_norm'],f['exponent']) for f in c['ideal']['factors']))))
    return (tuple(sorted(columns)),p['group'],p['shared_zero_mask_gcd']['norm'],
            p['primitive_quotient_conductor']['norm'],p['full_period_lcm_norm_Q'],p['A_exact'],p['A_P_exact'])


def build():
    raw=(ROOT/'experiments/cf22_pysr/correlation/decomposition.json.gz').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PIN:raise ValueError('source hash mismatch')
    rows={r['id']:r for r in json.loads(gzip.decompress(raw))['rows']}; out=[]
    for rid,ids in [('U96_P13_o1',((28,37),(28,38))),('U48_P49_o1',((3,15),(3,16)))]:
        row=rows[rid]; pairs={(p['i'],p['j']):p for p in row['pairs']};a,b=(pairs[i] for i in ids)
        if key(a)!=key(b):raise ValueError('features differ')
        al,au=(F(a['C_signed_contribution'][k]) for k in ('lower','upper'))
        bl,bu=(F(b['C_signed_contribution'][k]) for k in ('lower','upper'))
        if not al<=au or not bl<=bu or not al>bu:raise ValueError('not disjoint ordered intervals')
        out.append({'configuration':rid,'pair_ids':ids,'same_row_scales_and_profile':True,
                    'same_enhanced_features':key(a),'higher_output':{'lower':str(al),'upper':str(au)},
                    'lower_output':{'lower':str(bl),'upper':str(bu)},'gap_lower':str(al-bu),
                    'unavoidable_max_absolute_error_lower':str((al-bu)/2)})
    return {'status':'PASS_FEATURE_COLLISIONS_CONFIRMED','source_sha256':PIN,'witnesses':out,
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    result=build()
    with args.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'])
