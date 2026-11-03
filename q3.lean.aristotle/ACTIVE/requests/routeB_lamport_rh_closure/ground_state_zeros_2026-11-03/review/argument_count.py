"""NUMERICAL sampled argument counts; no between-node enclosure certificate."""
from pathlib import Path
import sys,json,math,time,hashlib,argparse
sys.path.insert(0,'/workspace/conditioning_deps')
from flint import arb,acb,acb_poly,ctx

P=Path(__file__).resolve().parent;BASE=P.parent
START=time.process_time()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def guard(budget):
    if time.process_time()-START>budget:raise TimeoutError('CPU budget exhausted')

def independent_numerator(v,parity,m):
    """Barycentric recurrence, independent of census.py's quotient assembly."""
    s=arb(2).sqrt()
    if parity=='even':N=acb_poly([arb(v[0])]);D=acb_poly([0,1])
    else:N=acb_poly([0]);D=acb_poly([1])
    for n in range(1,m+1):
        node=arb(n*n)/arb(m*m);factor=acb_poly([-node,1])
        weight=arb(v[n])*s if parity=='even' else arb(v[n-1])*n
        N=N*factor+D*weight;D=D*factor
    return N

def winding(phases):
    jumps=[math.remainder(b-a,2*math.pi) for a,b in zip(phases,phases[1:])]
    raw=math.fsum(jumps)/(2*math.pi)
    return dict(winding=raw,nearest_integer=round(raw),integer_residual=abs(raw-round(raw)),max_phase_increment=max(map(abs,jumps)))

def contour(poly,Om,T,left,halfheight,h,budget):
    corners=[acb(left,-halfheight),acb(T,-halfheight),acb(T,halfheight),acb(left,halfheight),acb(left,-halfheight)]
    lengths=[float(T-left),2*halfheight,float(T-left),2*halfheight]
    fine=[];coarse=[];radii=[];max_radius_ball=arb(0);samples=0
    for edge,(a,b,length) in enumerate(zip(corners,corners[1:],lengths)):
        n=2*math.ceil(length/(2*h))
        for j in range(n+1):
            if edge and j==0:continue
            if samples%100==0:guard(budget)
            z=a+(b-a)*arb(j)/n;value=poly((z/Om)**2)
            if value.contains(0):raise ValueError('A sampled polynomial ball contains zero')
            arg=value.arg();rad=float(arg.rad())
            if arg.rad()>max_radius_ball:max_radius_ball=arg.rad()
            if not math.isfinite(rad) or rad>1e-12:raise ValueError('A sampled argument is insufficiently resolved')
            phase=float(arg.mid());fine.append(phase);radii.append(rad)
            if j%2==0:coarse.append(phase)
            samples+=1
    fs=winding(fine);cs=winding(coarse)
    return dict(fine=fs,coarse=cs,fine_max_step=h,coarse_max_step=2*h,samples=samples,max_argument_radius_float=max(radii),max_argument_radius=str(max_radius_ball),
                step_halving_agrees=fs['nearest_integer']==cs['nearest_integer'],
                phase_guard_pass=max(fs['max_phase_increment'],cs['max_phase_increment'])<math.pi/2,
                fine_pi_over_2_guard_pass=fs['max_phase_increment']<math.pi/2,
                both_pi_guard_pass=max(fs['max_phase_increment'],cs['max_phase_increment'])<math.pi)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--budget',type=float,default=120);ap.add_argument('--bits',type=int,default=4096);ap.add_argument('--step',type=float,default=.125);ap.add_argument('--pilot-only',action='store_true');ap.add_argument('--omit-zeta',action='store_true');ap.add_argument('--low-only',action='store_true');ap.add_argument('--output',default='argument_count.json');a=ap.parse_args();ctx.prec=a.bits
    rows=[];error=None
    cases=[('zeta','even'),('dh','even'),('plant','even'),('dh','odd'),('plant','odd')]
    if a.pilot_only:cases=cases[:1]
    if a.omit_zeta:cases=cases[1:]
    try:
        for w,parity in cases:
            vp=BASE/f'spectra/vectors/{w}_m300.json';rp=BASE/f'roots/results/{w}_{parity}_m300.json'
            d=json.loads(vp.read_text());r=json.loads(rp.read_text());m=300;T=arb(r['cutoffs']['fixed_c1_4']['T']);left=arb('0.000001')
            highroots=[z for z in r['roots'] if z['kind'].startswith('polynomial')]
            positive=[float(z['z_re']) for z in highroots if float(z['z_re'])>0 and abs(float(z['z_im']))<.5]
            high_census=sum(float(left)<float(z['z_re'])<float(T) and abs(float(z['z_im']))<.5 for z in highroots)
            tiny=sum(0<float(z['z_re'])<=float(left) and abs(float(z['z_im']))<.5 for z in highroots)
            for level in (['low'] if a.low_only else ['low','high']):
                guard(a.budget);begin=time.process_time()
                v=d[f'v_{parity}0'+('_low' if level=='low' else '')];L=arb(d['L_low'] if level=='low' else d['L']);omega=2*arb.pi()/L;Om=m*omega
                poly=independent_numerator(v,parity,m);build=time.process_time()-begin
                res=contour(poly,Om,T,left,.5,a.step,a.budget)
                nsin=int(float(T/omega));correction=nsin-m;NP=res['fine']['nearest_integer'];NF=NP+correction
                replay=r.get('precision_replay',{}).get('cutoffs',{}).get('fixed_c1_4',{})
                row=dict(world=w,parity=parity,level=level,m=m,bits=a.bits,degree=poly.degree(),left='1e-6',right=r['cutoffs']['fixed_c1_4']['T'],imaginary_bounds=['-.5','.5'],
                         polynomial_count=NP,sine_count=nsin,denominator_count=m,physical_count=NF,
                         high_complete_polynomial_count_in_same_rectangle=high_census,high_complete_physical_count=r['cutoffs']['fixed_c1_4']['fourier_strip_count'],
                         agrees_high_complete_polynomial_count=NP==high_census,
                         low_newton_measured_strip_count=replay.get('low_replayed_strip_root_count'),
                         high_min_positive_real_in_strip=min(positive) if positive else None,high_roots_in_excluded_tiny_axis_strip=tiny,
                         contour=res,polynomial_build_cpu_seconds=build,cpu_seconds=time.process_time()-begin,
                         vector_sha256=sha(vp),high_census_sha256=sha(rp))
                rows.append(row);print(json.dumps({k:row[k] for k in ['world','parity','level','polynomial_count','physical_count','agrees_high_complete_polynomial_count','cpu_seconds']}),flush=True)
    except (TimeoutError,ValueError) as ex:error=str(ex)
    result=dict(status='NUMERICAL_SAMPLED_ARGUMENT_COUNTS_COMPLETE' if len(rows)==len(cases)*(1 if a.low_only else 2) and error is None else 'BOUNDED_ARGUMENT_COUNT_INCOMPLETE',
                error=error,total_cpu_seconds=time.process_time()-START,budget_cpu_seconds=a.budget,rows=rows,
                scope='Numerical sampled argument principle at step and halfstep with sampled nonzero balls and phase guards; no between-node contour enclosure, no certified count. Counts exclude 0<Re(z)<=1e-6; complete HIGH roots checked separately there. LOW tiny-axis strip not certified. No roots/eigenvectors recomputed.',
                correction='physical F count = numerator P count + sin(zL/2) count - denominator D count; origin and 1/z outside rectangle; sine/denominator roots cancel at internal harmonics. Odd origin also outside rectangle.')
    (P/a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}),flush=True)

if __name__=='__main__':main()
