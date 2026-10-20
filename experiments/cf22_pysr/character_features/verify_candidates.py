#!/usr/bin/env python3
"""Independent rational-interval replay of one held-out refutation per candidate."""
import ast,gzip,hashlib,json,argparse
from fractions import Fraction as F
from pathlib import Path


def run(folder):
    data_path=folder/'dataset.json.gz'; raw=data_path.read_bytes()
    manifest=json.loads((folder/'search_run/manifest.json').read_text())
    if hashlib.sha256(raw).hexdigest()!=manifest['dataset_sha256']:raise ValueError('data hash')
    data=json.loads(gzip.decompress(raw));rows={r['id']:r for r in data['rows']}
    results=json.loads((folder/'search_run/result.json').read_text());checks=[]
    for c in results['candidates']:
        w=c['splits']['test']['first_refutation']
        if w is None:raise ValueError('no test refutation')
        row=rows[w['id']]
        if row['split']!='test':raise ValueError('not held out')
        env={n:(F(b['lower']),F(b['upper'])) for n,b in zip(data['feature_names'],row['feature_intervals'])}
        expr=c['expression']
        def mul(a,b):
            values=[x*y for x in a for y in b];return min(values),max(values)
        def evaluate(n):
            if isinstance(n,ast.Expression):return evaluate(n.body)
            if isinstance(n,ast.Name):return env[n.id]
            if isinstance(n,ast.Constant):
                x=F(ast.get_source_segment(expr,n));return x,x
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
                a=evaluate(n.operand);return -a[1],-a[0]
            if isinstance(n,ast.BinOp):
                a,b=evaluate(n.left),evaluate(n.right)
                if isinstance(n.op,ast.Add):return a[0]+b[0],a[1]+b[1]
                if isinstance(n.op,ast.Sub):return a[0]-b[1],a[1]-b[0]
                if isinstance(n.op,ast.Mult):return mul(a,b)
                if isinstance(n.op,ast.Div):
                    if b[0]<=0<=b[1]:raise ValueError('uncertain denominator')
                    return mul(a,(1/b[1],1/b[0]))
            raise ValueError('unsupported expression')
        pred=evaluate(ast.parse(expr,mode='eval'));target=(F(row['target']['lower']),F(row['target']['upper']))
        gap=max(pred[0]-target[1],target[0]-pred[1])
        if gap<=0:raise ValueError('refutation not certified')
        checks.append({'candidate_index':c['index'],'expression':expr,'row':row['id'],
                       'prediction':list(map(str,pred)),'target':list(map(str,target)),
                       'strict_separation_lower':str(gap),'status':'REFUTED_EXACT_LITERAL'})
    return {'status':'PASS','checks':checks,'dataset_sha256':hashlib.sha256(raw).hexdigest(),
            'candidate_result_sha256':hashlib.sha256((folder/'search_run/result.json').read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--folder',type=Path,default=Path(__file__).resolve().parent);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    result=run(args.folder)
    with args.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS:',len(result['checks']),'exact heldout refutations')
