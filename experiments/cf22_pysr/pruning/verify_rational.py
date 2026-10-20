#!/usr/bin/env python3
"""Independent rational certificate for two fixed finite-panel boxes; no Arb."""
from fractions import Fraction as Q
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SOURCE = 'f9c298bbcd7aa4ac4a1be3e689baf1bd0554a65d'


def root_upper(value, degree=6, scale=10**6):
    """Return rational upper bound by exact integer binary search."""
    assert value > 0
    target = value * scale**degree
    lo, hi = 0, 1
    while hi**degree < target:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**degree >= target:
            hi = mid
        else:
            lo = mid
    upper = Q(hi, scale)
    assert upper**degree >= value
    return upper


def build():
    import subprocess
    paths = ['experiments/cf22_pysr/nonunit/main.json',
             'experiments/cf22_pysr/nonunit/heldout.json',
             'experiments/cf22_pysr/correlation/summary.json']
    docs, hashes = [], {}
    for name in paths:
        raw = (ROOT/name).read_bytes()
        if raw != subprocess.check_output(['git','show',SOURCE+':'+name],cwd=ROOT):
            raise ValueError('source changed: '+name)
        hashes[name] = hashlib.sha256(raw).hexdigest()
        docs.append(json.loads(raw))
    rows = docs[0]['rows']+docs[1]['rows']
    groups = {row['id']:row for row in docs[2]['rows']}
    assert len(rows) == len(groups) == len({row['id'] for row in rows}) == 20
    checks = []
    for row in rows:
        rid=row['id']; g=groups[rid]
        assert row['configuration'] == g['configuration']
        assert Q(g['saved_C']['lower']) <= Q(row['C']['lower'])
        assert Q(g['saved_C']['upper']) >= Q(row['C']['upper'])
        terms=[g['groups'][key]['C_contribution'] for key in ('rough_rough','cross','affected_affected')]
        lower=sum(Q(t['lower']) for t in terms)
        upper=sum(Q(t['upper']) for t in terms)
        assert lower <= Q(row['C']['upper']) and upper >= Q(row['C']['lower'])
        checks.append(rid)
    results=[]
    for label,kappa,witness in [('whole_panel',Q(19,1000),'U64_Pproduction_o1'),
                                ('nonunit_mixed',Q(3,1000),'U64_P13_o1')]:
        row=next(x for x in rows if x['id']==witness)
        U=Q(row['configuration']['U']); P=Q(row['parameters']['P']['upper']); L=Q(row['parameters']['L']['upper'])
        assert U>1 and P>0 and L>0
        S_upper=P*root_upper(U*L**5)
        envelope_upper=Q(1,100)*P*U+kappa*S_upper
        # delta>=0 implies U^-delta<=1; alpha,kappa monotone on positive scales.
        C_lower=Q(row['C']['lower'])
        margin=C_lower-envelope_upper
        assert margin>0
        g=groups[witness]['groups']
        without_cross_upper=sum(Q(g[k]['C_contribution']['upper']) for k in ('rough_rough','affected_affected'))
        results.append({'name':label,'alpha':['0','1/100'],'kappa':['0',str(kappa)],
          'delta':['0','1/100'],'status':'EXCLUDED_ON_FINITE_PANEL','witness':witness,
          'C_lower':str(C_lower),'S_upper':str(S_upper),'envelope_upper':str(envelope_upper),
          'strict_margin_lower':str(margin),'margin_decimal_for_display_only':float(margin),
          'without_cross_upper_diagnostic_only':str(without_cross_upper)})
    return {'scope':'FINITE_SAVED_PANEL_ONLY_NOT_CF22','source_commit':SOURCE,
            'source_sha256':hashes,'all_20_full_C_group_checks':checks,'boxes':results,
            'method':'Exact Fraction arithmetic; rational sixth-root upper bound; U^-delta<=1',
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=build()
    with args.output.open('x') as stream:
        json.dump(result,stream,indent=2);stream.write('\n')
    print(json.dumps(result['boxes'],indent=2))
