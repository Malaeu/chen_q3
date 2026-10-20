#!/usr/bin/env python3
"""One bounded PySR search followed by interval refutation of literal candidates."""
import argparse
from fractions import Fraction
import hashlib
import gzip
import importlib.metadata
import json
import os
from pathlib import Path
import sys

CONFIG=dict(niterations=12,populations=2,population_size=20,ncycles_per_iteration=30,
            maxsize=12,timeout_in_seconds=60,binary_operators=['+','-','*','/'],
            unary_operators=[],precision=64,random_state=20261020,deterministic=True,
            parallelism='serial',batching=False,warm_start=False,parsimony=0.001,
            verbosity=0,progress=False)


def write(path,data):
    with path.open('x') as f:json.dump(data,f,indent=2,ensure_ascii=False);f.write('\n')


def run(data_path,out):
    import numpy as np
    import sympy as sp
    from flint import arb, fmpq, ctx
    raw=data_path.read_bytes(); data=json.loads(gzip.decompress(raw) if data_path.suffix=='.gz' else raw); rows=data['rows']; names=data['feature_names']
    # Independently gate the actual float feature matrix, not another metadata key.
    if len(rows)!=13434 or len({r['id'] for r in rows})!=13434:
        raise ValueError('expected 13434 unique complete pairs')
    groups={}
    for r in rows:
        if r['split'] not in ('train','test'):
            raise ValueError('unknown split')
        if len(r['feature_intervals'])!=len(names):
            raise ValueError('feature interval dimension')
        for value,bounds in zip(r['features'],r['feature_intervals']):
            lo,hi=Fraction(bounds['lower']),Fraction(bounds['upper'])
            if lo>hi or not float(lo)<=float(value)<=float(hi):
                raise ValueError('invalid feature interval or rounded feature')
        values=tuple(float(v) for v in r['features'])
        if len(values)!=len(names) or not np.isfinite(values).all():raise ValueError('invalid features')
        lo,hi=Fraction(r['target']['lower']),Fraction(r['target']['upper'])
        if lo>hi:raise ValueError('reversed target')
        a,b=groups.get(values,(lo,hi));a,b=max(a,lo),min(b,hi)
        if a>b:raise ValueError('actual numeric matrix collision')
        groups[values]=(a,b)
    train=[r for r in rows if r['split']=='train'];test=[r for r in rows if r['split']=='test']
    if not train or not test or {r['configuration_id'] for r in train}&{r['configuration_id'] for r in test}:raise ValueError('invalid split')
    out.mkdir(parents=True,exist_ok=False)
    manifest={'dataset_sha256':hashlib.sha256(raw).hexdigest(),'config':CONFIG,
              'feature_names':names,'train_rows':len(train),'test_rows':len(test),
              'feature_selection_used_full_panel':True,'holdout_is_blind':False,
              'target':'complete signed pair D_ij, squared error for conjecture only',
              'actual_numeric_feature_keys':len(groups),'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    write(out/'manifest.json',manifest)
    from pysr import PySRRegressor
    model=PySRRegressor(**CONFIG,output_directory=str(out/'pysr'))
    X=np.asarray([r['features'] for r in train],dtype=float)
    y=np.asarray([float((Fraction(r['target']['lower'])+Fraction(r['target']['upper']))/2) for r in train])
    model.fit(X,y,variable_names=names)
    equations=model.equations_
    # Audit every returned Pareto candidate; do not silently discard bad equations.
    ctx.prec=192
    def q(v):
        f=Fraction(str(v));return arb(fmpq(f.numerator,f.denominator))
    def ball(rec):return q(rec['lower']).union(q(rec['upper']))
    def eval_node(node,env):
        if node.is_Symbol:return env[str(node)]
        if node.is_Number:return q(str(node))
        if node.is_Add:return sum((eval_node(a,env) for a in node.args),arb(0))
        if node.is_Mul:
            value=arb(1)
            for a in node.args:value*=eval_node(a,env)
            return value
        if node.is_Pow and node.args[1].is_Integer:
            base=eval_node(node.args[0],env);power=int(node.args[1])
            if power<0 and base.contains(0):raise ValueError('denominator interval includes zero')
            return base**power
        raise ValueError('unsupported expression '+str(node))
    results=[]
    for index,eq in equations.iterrows():
        expr=model.sympy(index=index)
        record={'index':int(index),'complexity':int(eq['complexity']),'training_loss':float(eq['loss']),
                'expression':str(expr),'literal_constants_policy':'SymPy printed decimal constants fixed as exact rational literals',
                'splits':{}}
        for split,subset in [('train',train),('test',test)]:
            refuted=overlap=undefined=0; witness=None; max_error_upper=0.0
            for r in subset:
                env={n:ball(v) for n,v in zip(names,r['feature_intervals'])}
                try:
                    prediction=eval_node(expr,env)
                    if not prediction.is_finite():raise ValueError('nonfinite prediction')
                    target=ball(r['target']);error=prediction-target
                    max_error_upper=max(max_error_upper,float(abs(error).upper()))
                    if prediction.overlaps(target):overlap+=1
                    else:
                        refuted+=1
                        if witness is None:witness={'id':r['id'],'target':r['target'],
                            'prediction_interval':str(prediction),'error_interval':str(error)}
                except (ValueError,ZeroDivisionError,KeyError):undefined+=1
            record['splits'][split]={'refuted_points':refuted,'overlapping_intervals':overlap,
                'undefined_points':undefined,'max_absolute_error_upper_display':max_error_upper,'first_refutation':witness}
        record['status']='REFUTED_AS_LITERAL_IDENTITY' if any(v['refuted_points'] for v in record['splits'].values()) else 'NOT_PROVED'
        results.append(record)
    result={'scope':'FINITE_PANEL_CONJECTURE_SEARCH_NOT_CF22','model_fits':1,'candidates':results,
            'versions':{k:importlib.metadata.version(k) for k in ['pysr','sympy','numpy','python-flint']},
            'manifest_sha256':hashlib.sha256((out/'manifest.json').read_bytes()).hexdigest()}
    write(out/'result.json',result)
    print(json.dumps({'model_fits':1,'candidates':len(results),'statuses':[r['status'] for r in results]}))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--dataset',type=Path,required=True);parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args();run(args.dataset,args.output_dir)
