"""Least-overlapping LOW-CLUSTER direction and its physical-space diagnostics.

Input: parent core_m{m}_dps100_gl128.json, m=12,16,20,24.
The chosen vector is C6 times the smallest RIGHT singularvector of Q_ladder.T C6.
It is not the ladder-side singularvector. All transforms use exp(-itx).
Zero extension is explicit; no global H1 or Fourier second moment is claimed.
"""
from pathlib import Path
import json,csv
import mpmath as mp

OUT=Path(__file__).resolve().parent

def matrix_rows(rows):
    return mp.matrix([[mp.mpf(x) for x in row] for row in rows])

def extract_shape(data):
    m=int(data['m']);L=mp.log(m);b=L/2
    V=matrix_rows(data['V']);C=V[:,:6]
    A=matrix_rows(data['ladder']['projected_profile_coefficients'])
    norms=[mp.norm(A[:,j]) for j in range(A.cols)]
    An=mp.matrix([[A[i,j]/norms[j] for j in range(A.cols)] for i in range(A.rows)])
    U,sv,W=mp.svd_r(An,full_matrices=False);Q=U[:,:6]
    left,s,right=mp.svd_r(Q.T*C,full_matrices=False)
    z=right.T[:,5];coef=C*z;coef/=mp.norm(coef)
    physical=mp.matrix([(1 if n==0 else mp.sqrt(2))*(-1)**n*coef[n]/mp.sqrt(L) for n in range(m+1)])
    if mp.fsum(physical)<0:z=-z;coef=-coef;physical=-physical
    residual=coef-Q*(Q.T*coef)
    overlap=mp.norm(Q.T*coef)
    return dict(m=m,L=L,b=b,coef=coef,physical=physical,cluster_coefficients=z,
                singular_values=list(s),ladder_profile_singular_values=list(sv),
                overlap=overlap,orthogonal_residual=mp.norm(residual),
                angle_radians=mp.atan2(mp.norm(residual),overlap),
                norm=mp.norm(coef),cluster_projection_error=mp.norm(coef-C*(C.T*coef)),
                Q_orth_error=max(abs(x) for x in Q.T*Q-mp.eye(6)))

def value(shape,x):
    if abs(x)>shape['b']:return mp.mpf(0)
    L=shape['L']
    return mp.fsum(a*mp.cos(2*mp.pi*n*x/L) for n,a in enumerate(shape['physical']))

def fourier(shape,t):
    b=shape['b'];L=shape['L']
    return mp.fsum(a*b*(mp.sinc((t-2*mp.pi*n/L)*b)+mp.sinc((t+2*mp.pi*n/L)*b))
                   for n,a in enumerate(shape['physical']))

def cosine_moment(q,k,a):
    """Integral_{-a}^a x^q*cos(kx) dx, q=0,2,4."""
    if k==0:return 2*a**(q+1)/(q+1)
    si=mp.sin(k*a);co=mp.cos(k*a)
    if q==0:return 2*si/k
    if q==2:return 2*(a*a*si/k+2*a*co/k**2-2*si/k**3)
    if q==4:return 2*(a**4*si/k+4*a**3*co/k**2-12*a*a*si/k**3-24*a*co/k**4+24*si/k**5)
    raise ValueError('q must be0,2,4')

def spatial_moment(shape,q=0,cutoff_fraction=1):
    aa=shape['b']*mp.mpf(cutoff_fraction);om=2*mp.pi/shape['L'];v=shape['physical']
    return mp.fsum(v[i]*v[j]*(cosine_moment(q,om*(i-j),aa)+cosine_moment(q,om*(i+j),aa))/2
                   for i in range(len(v)) for j in range(len(v)))

def frequency_bands(shape,order=64):
    gn,gw=mp.gauss_quadrature(order,'legendre')
    bands=[]
    for lo,hi in((0,5),(5,10),(10,20),(20,40),(40,80)):
        pieces=[]
        # Fixed physical panel width2.5; entire sinc formula has removable values.
        for p in range(int((hi-lo)*2/5)):
            a=mp.mpf(lo)+mp.mpf('2.5')*p;b=a+mp.mpf('2.5')
            pieces.append((b-a)/2*mp.fsum(w*fourier(shape,(a+b)/2+(b-a)*x/2)**2 for x,w in zip(gn,gw)))
        bands.append(dict(lower=lo,upper=hi,mass=mp.fsum(pieces)/mp.pi))
    bands.append(dict(lower=80,upper=None,mass=1-mp.fsum(r['mass'] for r in bands)))
    return bands

def write_csv(path,rows):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

def augment_summary(summary,shape):
    fmt=lambda x:mp.nstr(x,100)
    for radius in ('0.75','1.0','1.25'):
        frac=min(mp.mpf(1),mp.mpf(radius)/shape['b'])
        summary['bulk_abs_x_le_'+radius]=fmt(spatial_moment(shape,0,frac))
    b=shape['b'];L=shape['L'];v=shape['physical']
    step=b/2000
    grid=[step*j for j in range(2001)]
    best=max(grid,key=lambda x:abs(value(shape,x)))
    candidates=[mp.mpf(0),b,best]
    def derivative(x):
        return -mp.fsum(a*(2*mp.pi*n/L)*mp.sin(2*mp.pi*n*x/L) for n,a in enumerate(v))
    if step<best<b-step:
        stationary=mp.findroot(derivative,(best-step,best+step))
        if 0<=stationary<=b:candidates.append(stationary)
    peak=max(candidates,key=lambda x:abs(value(shape,x)))
    summary['peak_abs_x']=fmt(peak)
    summary['peak_density']=fmt(value(shape,peak)**2)
    summary['peak_location_method']='2001 samples on[0,b], followed by local derivative root'
    summary['parity']='even; x*f and x*|f|^2 are odd; mean x=0'
    summary['zero_extension']=True
    return summary


def augment_existing():
    mp.mp.dps=100
    results=json.loads((OUT/'shape_results.json').read_text())
    for row in results:
        m=row['summary']['m']
        data=json.loads((OUT.parent/f'core_m{m}_dps100_gl128.json').read_text())
        augment_summary(row['summary'],extract_shape(data))
    (OUT/'shape_results.json').write_text(json.dumps(results,indent=2)+'\n')
    write_csv(OUT/'shape_summary.csv',[r['summary'] for r in results])
    # Density uses the already exported physical samples and the same fixed x scale.
    samples=list(csv.DictReader((OUT/'shape_samples.csv').open()))
    colors={12:'#167d9a',16:'#d66b46',20:'#487d39',24:'#8a559e'}
    top=max(float(r['density']) for r in samples)
    sx=lambda x:60+(float(x)+2)*195
    sy=lambda y:375-float(y)*320/top
    lines=['<svg xmlns="http://www.w3.org/2000/svg" width="900" height="460" viewBox="0 0 900 460">','<rect width="900" height="460" fill="white"/>','<text x="60" y="25" font-family="sans-serif" font-size="18">Physical density |f(x)|² of least-overlapping cluster direction</text>','<line x1="60" y1="375" x2="840" y2="375" stroke="#777"/>']
    for m in (12,16,20,24):
        pts=' '.join(f'{sx(r["x"]):.3f},{sy(r["density"]):.3f}' for r in samples if int(r['m'])==m)
        lines.append(f'<polyline points="{pts}" fill="none" stroke="{colors[m]}" stroke-width="1.8"/>')
        lines.append(f'<text x="{80+190*((m-12)//4)}" y="430" font-family="sans-serif" fill="{colors[m]}">m={m}</text>')
    for x in(-2,-1,0,1,2):lines.append(f'<text x="{sx(x)-5}" y="400" font-family="sans-serif">{x}</text>')
    lines.append('<text x="810" y="450" font-family="sans-serif">physical x</text></svg>')
    (OUT/'shape_density.svg').write_text('\n'.join(lines))


def main():
    mp.mp.dps=100
    fmt=lambda x:mp.nstr(x,100)
    summaries=[];coefrows=[];samples=[];freqrows=[];raw=[]
    for m in(12,16,20,24):
        data=json.loads((OUT.parent/f'core_m{m}_dps100_gl128.json').read_text())
        sh=extract_shape(data);bands=frequency_bands(sh,64);check=frequency_bands(sh,96)
        s=dict(m=m,L=fmt(sh['L']),half_window=fmt(sh['b']),norm_squared=fmt(sh['norm']**2),
               smallest_cosine=fmt(sh['singular_values'][-1]),second_smallest_cosine=fmt(sh['singular_values'][-2]),
               least_overlap_squared=fmt(sh['overlap']**2),angle_degrees=fmt(sh['angle_radians']*180/mp.pi),
               center_value=fmt(value(sh,mp.mpf(0))),endpoint_inside_value=fmt(value(sh,sh['b'])),
               endpoint_squared=fmt(value(sh,sh['b'])**2),mean_x='0',
               moment_x2=fmt(spatial_moment(sh,2)),moment_x4=fmt(spatial_moment(sh,4)),
               cluster_projection_error=fmt(sh['cluster_projection_error']),ladder_orth_error=fmt(sh['Q_orth_error']),
               frequency_quadrature_max_absolute_change=fmt(max(abs(a['mass']-b['mass']) for a,b in zip(bands,check))))
        for frac in('0.5','0.8','0.9'):
            mass=spatial_moment(sh,0,frac)
            s['bulk_abs_x_le_'+frac+'b']=fmt(mass);s['edge_abs_x_gt_'+frac+'b']=fmt(1-mass)
        s['modal_frequency_mean_abs']=fmt(mp.fsum(sh['coef'][n]**2*(2*mp.pi*n/sh['L']) for n in range(m+1)))
        s['modal_frequency_rms']=fmt(mp.sqrt(mp.fsum(sh['coef'][n]**2*(2*mp.pi*n/sh['L'])**2 for n in range(m+1))))
        s['modal_frequency_rms_scope']='finite periodic modal statistic only; not zero-extended Fourier second moment'
        augment_summary(s,sh)
        summaries.append(s)
        for n in range(m+1):coefrows.append(dict(m=m,n=n,physical_omega=fmt(2*mp.pi*n/sh['L']),even_coefficient=fmt(sh['coef'][n]),modal_power=fmt(sh['coef'][n]**2),cosine_amplitude=fmt(sh['physical'][n])))
        grid=sorted(set([mp.mpf(j)/100 for j in range(-200,201)]+[-sh['b'],sh['b']]))
        for x in grid:
            f=value(sh,x)
            samples.append(dict(m=m,x=fmt(x),x_over_half_window=fmt(x/sh['b']),f=fmt(f),density=fmt(f*f),x_f=fmt(x*f),x_density=fmt(x*f*f),inside_window=abs(x)<=sh['b']))
        for a,b in zip(bands,check):freqrows.append(dict(m=m,abs_frequency_lower=a['lower'],abs_frequency_upper=a['upper'] if a['upper'] is not None else 'infinity',symmetric_L2_mass=fmt(b['mass']),GL64_mass=fmt(a['mass']),GL96_minus_GL64=fmt(b['mass']-a['mass']),tail_method='Parseval residual' if a['upper'] is None else 'analytic sinc Fourier transform, symmetric integral divided by2pi'))
        raw.append(dict(summary=s,cluster_coefficients=[fmt(x) for x in sh['cluster_coefficients']],canonical_cosines=[fmt(x) for x in sh['singular_values']],physical_modal_coefficients=[fmt(x) for x in sh['coef']],ladder_profile_singular_values=[fmt(x) for x in sh['ladder_profile_singular_values']]))
        (OUT/'shape_results.json').write_text(json.dumps(raw,indent=2)+'\n')
        print(json.dumps(s),flush=True)
    write_csv(OUT/'shape_summary.csv',summaries);write_csv(OUT/'shape_coefficients.csv',coefrows);write_csv(OUT/'shape_samples.csv',samples);write_csv(OUT/'shape_frequency.csv',freqrows)
    # Minimal standalone SVG of physical shapes on a common x scale.
    colors={12:'#167d9a',16:'#d66b46',20:'#487d39',24:'#8a559e'}
    maxy=max(abs(float(r['f'])) for r in samples);W=900;H=460
    sx=lambda x:60+(float(x)+2)*195
    sy=lambda y:210-float(y)*165/maxy
    lines=['<svg xmlns="http://www.w3.org/2000/svg" width="900" height="460" viewBox="0 0 900 460">','<rect width="900" height="460" fill="white"/>','<text x="60" y="25" font-family="sans-serif" font-size="18">Least-overlapping direction in span(v0,...,v5), norm=1</text>',f'<line x1="60" y1="210" x2="840" y2="210" stroke="#777"/>',f'<line x1="450" y1="40" x2="450" y2="380" stroke="#aaa"/>']
    for m in(12,16,20,24):
        pts=' '.join(f'{sx(r["x"]):.3f},{sy(r["f"]):.3f}' for r in samples if r['m']==m)
        lines.append(f'<polyline points="{pts}" fill="none" stroke="{colors[m]}" stroke-width="1.7"/>')
        lines.append(f'<text x="{80+190*((m-12)//4)}" y="420" font-family="sans-serif" fill="{colors[m]}">m={m}</text>')
    for x in(-2,-1,0,1,2):lines.append(f'<text x="{sx(x)-5}" y="400" font-family="sans-serif">{x}</text>')
    lines.append('<text x="810" y="445" font-family="sans-serif">physical x</text></svg>')
    (OUT/'shape.svg').write_text('\n'.join(lines))

if __name__=='__main__':
    import sys
    if '--augment' in sys.argv:augment_existing()
    else:
        main()
        augment_existing()
