#!/usr/bin/env python3
"""Independent shell accumulation of the pinned complete pair ledger."""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
EXPECTED='74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d'
THRESHOLDS=(1,7,13,19,31)
GROUPS=('rough_rough','cross','affected_affected')


def interval(x):
    a,b=F(x['lower']),F(x['upper'])
    if a>b: raise ValueError('reversed interval')
    return a,b


def add(a,b): return a[0]+b[0],a[1]+b[1]
def overlap(a,b): return a[0]<=b[1] and b[0]<=a[1]
def rec(a): return {'lower':str(a[0]),'upper':str(a[1])}


def build():
    raw=(ROOT/'experiments/cf22_pysr/correlation/decomposition.json.gz').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=EXPECTED: raise ValueError('source hash')
    source=json.loads(gzip.decompress(raw)); output=[]; pair_count=0
    for row in source['rows']:
        shells=defaultdict(lambda:(F(0),F(0)))
        counts=defaultdict(int)
        for p in row['pairs']:
            # Recover gcd from ideal-generator intersection, not saved gcd norm.
            left={tuple(f['prime_generator']):f for f in p['left_column']['ideal']['factors']}
            right={tuple(f['prime_generator']):f for f in p['right_column']['ideal']['factors']}
            g=1
            for key in left.keys() & right.keys():
                if left[key]['prime_ideal_norm']!=right[key]['prime_ideal_norm']: raise ValueError('prime norm mismatch')
                g*=left[key]['prime_ideal_norm']**min(left[key]['exponent'],right[key]['exponent'])
            if g!=p['shared_zero_mask_gcd']['norm']:raise ValueError('gcd mismatch')
            group=p['group']
            if group not in GROUPS:raise ValueError('unknown group')
            val=interval(p['C_signed_contribution'])
            physical,raw_term=interval(p['physical_signed_contribution']),interval(p['raw_signed_contribution'])
            if not overlap(val,(physical[0]-raw_term[1],physical[1]-raw_term[0])):raise ValueError('physical minus raw mismatch')
            shells[g,group]=add(shells[g,group],val);counts[g,group]+=1;pair_count+=1
        total=(F(0),F(0))
        for val in shells.values():total=add(total,val)
        if not overlap(total,interval(row['full_C'])):raise ValueError('full C mismatch')
        partitions=[]
        for G in THRESHOLDS:
            main=rest=(F(0),F(0)); nmain=nrest=0
            for (g,group),val in shells.items():
                if g<=G:main=add(main,val);nmain+=counts[g,group]
                else:rest=add(rest,val);nrest+=counts[g,group]
            if add(main,rest)!=total:raise ValueError('partition not exact')
            partitions.append({'G':G,'main':rec(main),'remainder':rec(rest),'main_count':nmain,'remainder_count':nrest})
        output.append({'id':row['id'],'partitions':partitions})
    if len(output)!=20 or pair_count!=13434:raise ValueError('coverage mismatch')
    return {'scope':'FINITE_PANEL_ONLY','status':'PASS','source_sha256':EXPECTED,
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'pairs':pair_count,'partitions':100,'rows':output}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(); result=build()
    with args.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS: 13434 pairs, 100 partitions, all20 full C retained')
