import csv,sys,collections
S=sys.argv[1]
def load(p):
    with open(p,encoding='utf-8') as f:
        return {r['key'].strip():r for r in csv.DictReader(f,delimiter='\t')}
P=load(f'{S}/pred.tsv'); O=load(f'{S}/outcome.tsv')
keys=sorted(set(P)|set(O))
miss=[k for k in keys if k not in P or k not in O]
print('rows pred',len(P),'out',len(O),'missing',miss)
ct=collections.Counter(); conf=collections.Counter()
for k in keys:
    if k in miss: continue
    p=P[k]['PRED'].strip(); o=O[k]['OUTCOME'].strip(); po=P[k]['PREDICTED_OUTCOME'].strip()
    ct[(p,o)]+=1; conf[(po,o)]+=1
outs=['MAIN_GAIN','EXACT_RETURN','REMAINDER_ONLY','SHAPE_KILL','UNKNOWN']
print('\nPRED x OUTCOME'); print('     ',' '.join(f'{o[:10]:>10}' for o in outs))
for p in ['P1','P0']: print(f'{p:5}',' '.join(f'{ct[(p,o)]:>10}' for o in outs))
print('\nPREDICTED_OUTCOME x OUTCOME')
for po in outs[:4]: print(f'{po[:10]:10}',' '.join(f'{conf[(po,o)]:>10}' for o in outs))
known=[k for k in keys if k not in miss and O[k]['OUTCOME'].strip()!='UNKNOWN']
acc=sum(P[k]['PREDICTED_OUTCOME'].strip()==O[k]['OUTCOME'].strip() for k in known)
print(f'\nexact-outcome accuracy {acc}/{len(known)}')
print('\nMAIN_GAIN rows:')
for k in keys:
    if k in miss: continue
    if O[k]['OUTCOME'].strip()=='MAIN_GAIN' or P[k]['PRED'].strip()=='P1':
        print(f"{k:40} pred={P[k]['PRED']} A={P[k]['A']} B={P[k]['B']} out={O[k]['OUTCOME']} | {O[k].get('GAIN_TARGET','')[:90]}")
