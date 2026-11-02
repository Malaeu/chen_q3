"""Summarize first local-ratio exceedances without assuming monotonicity."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.dps=180
def fmt(x):return mp.nstr(x,120)
def save(name,rows):
    with (P/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def main():
    allrows=[];thresholds=[];summaries=[]
    for m in (16,20,24):
        rows=list(csv.DictReader((P/f'samples_m{m}.csv').open()));allrows+=rows
        for i in list(range(8))+[m//2,m-2]:
            rr=sorted([x for x in rows if int(x['i'])==i],key=lambda x:int(x['k']))
            rho=[mp.mpf(x['rho']) for x in rr];imax=max(range(len(rr)),key=lambda k:rho[k])
            summaries.append(dict(m=m,i=i,role=rr[0]['role'],first_zero_rho=rr[0]['rho'],last_zero_rho=rr[-1]['rho'],
                maximum_rho=fmt(rho[imax]),maximum_rho_k=rr[imax]['k'],maximum_rho_gamma=rr[imax]['gamma'],
                last_numerator=rr[-1]['numerator'],last_denominator=rr[-1]['denominator']))
            for threshold in (mp.mpf('1e-6'),mp.mpf('1e-2')):
                hits=[k for k,r in enumerate(rho) if r>threshold];j=hits[0] if hits else None
                T=mp.mpf(rr[j]['gamma']) if j is not None else None
                prev=rr[j-1] if j is not None and j>0 else None
                thresholds.append(dict(m=m,i=i,role=rr[0]['role'],threshold=fmt(threshold),first_k=rr[j]['k'] if j is not None else '',
                    first_T=fmt(T) if T is not None else '',first_rho=rr[j]['rho'] if j is not None else '',
                    previous_k=prev['k'] if prev else '',previous_T=prev['gamma'] if prev else '',previous_rho=prev['rho'] if prev else '',
                    censored_through_300=j is None,number_exceeding=len(hits),later_below_count=sum(r<=threshold for r in rho[j+1:]) if j is not None else '',
                    T_over_2pi_m=fmt(T/(2*mp.pi*m)) if T is not None else '',T_over_band=fmt(T*mp.log(m)/(2*mp.pi*m)) if T is not None else '',
                    E_CC=fmt(2*mp.pi*m),T_band=fmt(2*mp.pi*m/mp.log(m))))
    save('thresholds.csv',thresholds);save('profile_summary.csv',summaries)
    sourcepaths=[P/'scan.py']+[P/f'core_m{m}_dps{dps}_gl{order}.json' for m in(16,20,24) for dps,order in[(180,160),(220,192)]]
    (P/'source_hashes.json').write_text(json.dumps(dict(parent_commit='21d63ff6aa3a1bd31115b2c651a670c9818a90b7',
        inputs={x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in sourcepaths}),indent=2)+'\n')
    for m in (16,20,24):
        print('m',m)
        for i in list(range(8))+[m//2,m-2]:
            r=[x for x in thresholds if x['m']==m and x['i']==i]
            print(i,[(mp.nstr(mp.mpf(x['first_T']),12),mp.nstr(mp.mpf(x['T_over_band']),8)) if x['first_T'] else 'censored' for x in r])
if __name__=='__main__':main()
