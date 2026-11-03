"""Complete finite-carrier Fourier zero census for supplied numerical eigenvectors.
No source-zero seeds are used. Flint isolates every root of the rescaled numerator.
Balls certify the rounded vector polynomial, not the unknown exact eigenvector.
"""
from pathlib import Path
import os,sys,json,csv,time,hashlib,argparse,math
from functools import lru_cache
sys.path.insert(0,'/workspace/conditioning_deps')
import mpmath as mp
from flint import arb,acb,acb_poly,ctx
import numpy as np
from scipy.optimize import linear_sum_assignment
BASE=Path(__file__).resolve().parents[1]; OUT=Path(__file__).resolve().parent

def decimal(x,digits=180):
    return x.mid().str(digits, radius=False)

def numerator(c,parity,m,bits):
    ctx.prec=bits
    a=[arb(n)**2/arb(m)**2 for n in range(1,m+1)]
    D=acb_poly.from_roots(a)
    P=D*arb(c[0]) if parity=='even' else acb_poly([0])
    u=acb_poly([0,1]);s=arb(2).sqrt()
    for n,an in enumerate(a,1):
        weight=s*arb(c[n]) if parity=='even' else arb(c[n-1])*n
        if not weight.is_zero():
            P+=(D//acb_poly([-an,1]))*(u if parity=='even' else acb_poly([1]))*weight
    return P

def direct(c,z,L,parity):
    """Stable entire sinc continuation, including all internal harmonic poles."""
    b=L/2;om=2*mp.pi/L
    def sinc(x):return mp.sin(x)/x if x else mp.mpf(1)
    if parity=='even':
        return c[0]*mp.sqrt(L)*sinc(z*b)+mp.sqrt(2/L)*b*mp.fsum(c[n]*(-1)**n*(sinc((z-n*om)*b)+sinc((z+n*om)*b)) for n in range(1,len(c)))
    return 1j*mp.sqrt(2/L)*b*mp.fsum(c[n-1]*(-1)**n*(sinc((z-n*om)*b)-sinc((z+n*om)*b)) for n in range(1,len(c)+1))

def rational_fourier(c,z,L,parity,derivative=False):
    om=2*mp.pi/L;b=L/2
    if z==0 or min(abs(z-n*om) for n in range(1,len(c) if parity=='even' else len(c)+1))<mp.mpf('1e-20'):
        f=direct(c,z,L,parity)
        return (f,mp.diff(lambda t:direct(c,t,L,parity),z)) if derivative else f
    zz=z*z
    if parity=='even':
        rr=[(c[n],(n*om)**2,zz-(n*om)**2) for n in range(1,len(c))]
        r=c[0]+mp.sqrt(2)*mp.fsum(cn*zz/den for cn,aa,den in rr)
        h=2*mp.sin(z*b)/(mp.sqrt(L)*z);f=h*r
        if derivative:
            rp=mp.sqrt(2)*mp.fsum(-2*z*cn*aa/den**2 for cn,aa,den in rr)
            hp=2/mp.sqrt(L)*(b*mp.cos(z*b)/z-mp.sin(z*b)/zz)
            return f,hp*r+h*rp
        return f
    rr=[(c[n-1]*n*om,zz-(n*om)**2) for n in range(1,len(c)+1)]
    r=mp.fsum(cn/den for cn,den in rr);h=2j*mp.sqrt(2/L)*mp.sin(z*b);f=h*r
    if derivative:
        rp=mp.fsum(-2*z*cn/den**2 for cn,den in rr);hp=2j*mp.sqrt(2/L)*b*mp.cos(z*b)
        return f,hp*r+h*rp
    return f

def isolate(c,m,parity,bits=None,tolerance='1e-165'):
    bits=bits or max(700,5*m+500)
    errors=[]
    for attempt in range(5):
        start=time.monotonic()
        if m>=200:print(json.dumps(dict(event='isolation_start',m=m,parity=parity,bits=bits,attempt=attempt)),file=sys.stderr,flush=True)
        P=numerator(c,parity,m,bits)
        try:
            rr=P.roots(tol=arb(tolerance),maxprec=max(bits*3,10000))
            if len(rr)!=P.degree():raise ValueError('Incomplete polynomial degree census')
            for i,r in enumerate(rr):
                if r.imag.contains(0):
                    overlaps=[j for j,t in enumerate(rr) if t.overlaps(r.conjugate())]
                    if overlaps!=[i]:raise ValueError('Real-axis classification lacks unique conjugate enclosure')
            if m>=200:print(json.dumps(dict(event='isolation_finished',m=m,parity=parity,bits=bits,seconds=time.monotonic()-start)),file=sys.stderr,flush=True)
            return rr,dict(bits=bits,degree=P.degree(),isolated_count=len(rr),seconds=time.monotonic()-start,prior_failures=errors)
        except ValueError as e:
            errors.append(dict(bits=bits,error=str(e)));print(json.dumps(dict(event='isolation_retry',m=m,parity=parity,bits=bits,error=str(e))),file=sys.stderr,flush=True);bits*=2
    raise ValueError(errors)

@lru_cache(maxsize=8)
def references(world):
    if world.startswith('synthetic_'):return []
    if world in ('zeta','plant','planted'):
        p=BASE/'inputs/zeta_zeros.csv';rows=list(csv.DictReader(p.open()))
        out=[dict(index=int(r.get('k',r.get('index'))),re=mp.mpf(r.get('gamma',r.get('ordinate'))),im=mp.mpf(0),kind='critical_line') for r in rows]
        if world!='zeta':
            w=2*mp.pi/mp.log(2)
            out.extend([dict(index='plant_plus',re=w,im=mp.mpf('0.25'),kind='planted_off_line'),dict(index='plant_minus',re=w,im=mp.mpf('-0.25'),kind='planted_off_line')])
        return sorted(out,key=lambda r:(r['re'],r['im']))
    p=BASE/'inputs/dh_zeros_900_200dps.json';src=json.loads(p.read_text())
    return [dict(index=k+1,re=mp.mpf(r['gamma']),im=mp.mpf('0.5')-mp.mpf(r['sigma']),kind=r['kind']) for k,r in enumerate(src['upper_half_plane_zeros'])]

def reference_binding(world):
    if world.startswith('synthetic_'):return {}
    f=BASE/'inputs'/('zeta_zeros.csv' if world in ('zeta','plant','planted') else 'dh_zeros_900_200dps.json')
    return dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),decimal_reference_floor=160 if world in ('zeta','plant','planted') else 200,plant_pair='2*pi/log(2) +/- i/4' if world in ('plant','planted') else None)

def match(rows,src,T):
    actual=[r for r in rows if r['z_re_mp']>0 and r['z_re_mp']<T and abs(r['z_im_mp'])<mp.mpf('.5')]
    target=[r for r in src if r['re']<T and r['re']>0 and abs(r['im'])<mp.mpf('.5')]
    az=np.asarray([complex(float(a['z_re_mp']),float(a['z_im_mp'])) for a in actual]);bz=np.asarray([complex(float(b['re']),float(b['im'])) for b in target]);A=np.abs(az[:,None]-bz[None,:])
    pairs=[];ia=[];ib=[]
    if actual and target:ia,ib=linear_sum_assignment(A)
    if src and 'local_spacing' not in src[0]:
        zz=np.asarray([complex(float(r['re']),float(r['im'])) for r in src]);dd=np.abs(zz[:,None]-zz[None,:]);np.fill_diagonal(dd,np.inf)
        for i,r in enumerate(src):
            j=int(np.argmin(dd[i]));r['local_spacing']=abs(mp.mpc(r['re'],r['im'])-mp.mpc(src[j]['re'],src[j]['im'])) if len(src)>1 else mp.inf
    source_spacings=[r['local_spacing'] for r in target]
    for i,j in zip(ia,ib):
        a,b=actual[i],target[j];de=mp.mpc(a['z_re_mp'],a['z_im_mp'])-mp.mpc(b['re'],b['im']);dist=abs(de)
        pairs.append(dict(root_id=a['root_id'],kind=a['kind'],source_index=b['index'],source_kind=b['kind'],source_re=mp.nstr(b['re'],180),source_im=mp.nstr(b['im'],180),root_re=mp.nstr(a['z_re_mp'],180),root_im=mp.nstr(a['z_im_mp'],180),delta_re=mp.nstr(mp.re(de),40),delta_im=mp.nstr(mp.im(de),40),abs_deviation=mp.nstr(dist,40),local_spacing=mp.nstr(source_spacings[j],35),spacing_scaled_deviation=mp.nstr(dist/source_spacings[j],35)))
    unmatched_actual=[r['root_id'] for i,r in enumerate(actual) if i not in set(ia)]
    unmatched_source=[r['index'] for j,r in enumerate(target) if j not in set(ib)]
    ds=[mp.mpf(r['abs_deviation']) for r in pairs];ss=[mp.mpf(r['spacing_scaled_deviation']) for r in pairs]
    summary=dict(source_count=len(target),source_real_count=sum(r['im']==0 for r in target),source_nonreal_count=sum(r['im']!=0 for r in target),fourier_strip_count=len(actual),fourier_real_count=sum(r['z_im_mp']==0 for r in actual),fourier_nonreal_count=sum(r['z_im_mp']!=0 for r in actual),structural_external_count=sum(r['kind']=='forced_external' for r in actual),matched_count=len(pairs),matched_forced_external_count=sum(r['kind']=='forced_external' for r in pairs),unmatched_forced_external_count=sum(r['kind']=='forced_external' for r in actual)-sum(r['kind']=='forced_external' for r in pairs),unmatched_actual=unmatched_actual,unmatched_source=unmatched_source,max_abs_deviation=mp.nstr(max(ds),40) if ds else None,max_spacing_scaled_deviation=mp.nstr(max(ss),40) if ss else None,matched_under_1e_2=sum(d<mp.mpf('1e-2') for d in ds),matched_under_1e_6=sum(d<mp.mpf('1e-6') for d in ds),matched_under_1e_12=sum(d<mp.mpf('1e-12') for d in ds),matching='minimum total Euclidean distance, one-to-one, no source seeding; unmatched means count surplus, not a tolerance claim')
    nonreal_accepted=sum(mp.mpf(r['source_im'])!=0 and mp.mpf(r['abs_deviation'])<mp.mpf('1e-6') for r in pairs)
    summary['source_nonreal_recovered_at_1e_6']=nonreal_accepted;summary['source_nonreal_missing_at_1e_6']=summary['source_nonreal_count']-nonreal_accepted
    for label,tol in [('1e_2','1e-2'),('1e_6','1e-6'),('1e_12','1e-12')]:
        accepted=sum(d<mp.mpf(tol) for d in ds)
        summary['source_unrecovered_at_'+label]=len(target)-accepted
        summary['fourier_unmatched_at_'+label]=len(actual)-accepted
    return pairs,summary

def low_vector_replay(data,parity,highroots,m,L,Ts):
    low=data.get('v_'+parity+'0_low')
    if not low:return dict(status='NOT_AVAILABLE',scope='No independently recomputed lower-precision vector coordinates saved'),{}
    lowL=mp.mpf(data.get('L_low',data['L']));lowOm=2*mp.pi*m/lowL;highOm=2*mp.pi*m/L
    allhigh=[r for r in highroots if r['kind'].startswith('polynomial')]
    full=m in {16,24,40,80,160};maxT=max(Ts.values())
    high=allhigh if full else [r for r in allhigh if (0<r['z_re_mp']<maxT and abs(r['z_im_mp'])<mp.mpf('.5')) or (r['kind']=='polynomial_pure_imaginary' and abs(r['z_im_mp'])<maxT)]
    hz=[mp.mpc(r['z_re_mp'],r['z_im_mp']) for r in high];lowroots=[];failures=[];mapping={};pairs=[]
    if full:
        rr,info=isolate(low,m,parity);info.update(method='complete independent low-polynomial Flint isolation',certified_low_isolation=True)
        for u in rr:
            re=mp.mpf(decimal(u.real));im=mp.mpf(0) if u.imag.contains(0) else mp.mpf(decimal(u.imag));lowroots.append(mp.sqrt(mp.mpc(re,im))*lowOm)
        ia,ib=linear_sum_assignment(np.abs(np.asarray([complex(z) for z in hz])[:,None]-np.asarray([complex(z) for z in lowroots])[None,:]));paired=list(zip(ia,ib))
    else:
        coeff=list(map(mp.mpf,low));start=time.monotonic();steps=[];paired=[]
        for k,seed in enumerate(hz):
            z=seed;converged=False
            for it in range(12):
                f,fp=rational_fourier(coeff,z,lowL,parity,True)
                if not fp:break
                dz=f/fp;z-=dz
                if abs(dz)<mp.mpf('1e-165')*max(1,abs(z)):converged=True;break
            if not converged:failures.append(dict(root_id=high[k]['root_id'],status='NEWTON_DID_NOT_CONVERGE'));continue
            if any(abs(z-w)<mp.mpf('1e-100')*max(1,abs(z)) for w in lowroots):failures.append(dict(root_id=high[k]['root_id'],status='NEWTON_DUPLICATE_ROOT'));continue
            paired.append((k,len(lowroots)));lowroots.append(z);steps.append(it+1)
        info=dict(method='all physical-strip high roots plus bounded pure-imaginary roots seeded into low-vector rational Newton, no source seeds',degree=m if parity=='even' else m-1,refined_count=len(lowroots),attempted_count=len(high),max_steps=max(steps) if steps else None,seconds=time.monotonic()-start,certified_low_isolation=False,newton_failures=failures)
    for i,j in paired:
        dist=abs(hz[i]-lowroots[j]);resolution=10*(highOm**2/max(abs(hz[i]),mp.mpf('1e-80'))+lowOm**2/max(abs(lowroots[j]),mp.mpf('1e-80')))*mp.mpf('1e-165')+mp.mpf('1e-175')*max(1,abs(hz[i]),abs(lowroots[j]))
        row=dict(root_id=high[i]['root_id'],low_z_re=mp.nstr(mp.re(lowroots[j]),180),low_z_im=mp.nstr(mp.im(lowroots[j]),180),root_shift=mp.nstr(dist,40),nominal_resolution_allowance=mp.nstr(resolution,35),root_shift_plus_resolution=mp.nstr(dist+resolution,40),resolved_above_nominal_floor=bool(dist>resolution));pairs.append(row);mapping[high[i]['root_id']]=row
    cuts={}
    for key,T in Ts.items():
        selected=[r for r in allhigh if 0<r['z_re_mp']<T and abs(r['z_im_mp'])<mp.mpf('.5')];good=[r for r in selected if r['root_id'] in mapping]
        shifts=[mp.mpf(mapping[r['root_id']]['root_shift_plus_resolution']) for r in good];observed=[mp.mpf(mapping[r['root_id']]['root_shift']) for r in good]
        lowstrip=[z for z in lowroots if 0<mp.re(z)<T and abs(mp.im(z))<mp.mpf('.5')]
        cuts[key]=dict(high_polynomial_strip_count=len(selected),low_polynomial_strip_count=len(lowstrip) if full else None,low_replayed_strip_root_count=len(lowstrip),replay_attempted_strip_root_count=len(selected),replay_missing_strip_root_ids=[r['root_id'] for r in selected if r['root_id'] not in mapping],low_nonreal_strip_count=sum(mp.im(z)!=0 for z in lowstrip),max_root_shift=mp.nstr(max(shifts),40) if shifts else None,max_observed_root_shift=mp.nstr(max(observed),40) if observed else None,root_shift_reporting='max_root_shift includes conservative nominal allowance from the 1e-165 u isolation target and 180-digit output; values below that allowance are not resolved',root_shifts_under_1e_6=sum(x<mp.mpf('1e-6') for x in shifts),root_shifts_under_1e_12=sum(x<mp.mpf('1e-12') for x in shifts),root_shifts_under_1e_30=sum(x<mp.mpf('1e-30') for x in shifts))
    status='COMPLETE_LOW_HIGH_POLYNOMIAL_ROOT_REPLAY' if full else ('PHYSICAL_STRIP_NEWTON_LOW_HIGH_REPLAY' if not failures else 'PARTIAL_ROOT_REPLAY_FAILED')
    return dict(status=status,low_precision_dps=data.get('low_precision_dps'),low_L=mp.nstr(lowL,180),low_polynomial=info,low_degree=info['degree'],high_degree=len(allhigh),cutoffs=cuts,pairs=pairs,scope='Roots from two independently rebuilt source/eigenvector precisions. Low-polynomials fully isolated at m16,24,40,80,160; other low-vectors replay every high physical-strip root plus bounded pure-imaginary roots by rational Newton with convergence/distinctness checks. Newton counts are replayed roots, not low-polynomial completeness certificates. No source-zero seeds. Empirical replay, not an exact-ground interval certificate.'),mapping

def run(path,parity='even',repeat=False):
    source_blob=Path(path).read_bytes();data=json.loads(source_blob);m=int(data['m']);world=data['world'];digits=int(data.get('precision_dps',150));mp.mp.dps=max(220,digits)
    c=data.get('v_even0',data.get('c')) if parity=='even' else data['v_odd0']
    if not c:raise ValueError('Missing vector')
    if len(c)!=(m+1 if parity=='even' else m):raise ValueError('Coefficient count inconsistent with carrier/parity')
    L=mp.mpf(data['L']);om=2*mp.pi/L;Om=m*om;kap=1+(1+mp.log(mp.log(m)))/(4*mp.log(m));Ts={'fixed_c1_4':kap*Om,'Omega':Om,'0.8Omega':mp.mpf('.8')*Om};maxT=max(Ts.values())
    rr,info=isolate(c,m,parity);roots=[];cv=list(map(mp.mpf,c));block=next((q for q in data.get('blocks',[]) if q['parity']==parity),{});vdelta=mp.mpf(block.get('vector_replay_infinity',['0'])[0]);replay_l2=mp.sqrt(len(c))*vdelta;transform_floor=mp.sqrt(L)*replay_l2;maxres=mp.mpf(0);max_sinc_res=mp.mpf(0);max_sinc_difference=mp.mpf(0);sinc_checks=0
    for i,u in enumerate(rr):
        # For a real input polynomial, an isolated disk invariant under conjugation encloses a real root.
        real_u=u.imag.contains(0)
        ur=mp.mpf(decimal(u.real));ui=mp.mpf(0) if real_u else mp.mpf(decimal(u.imag))
        z=mp.sqrt(mp.mpc(ur,ui))*Om
        if real_u and ur>0:z=mp.mpc(mp.re(z),0);kind='polynomial_real'
        elif real_u and ur<0:z=mp.mpc(0,abs(mp.im(z)));kind='polynomial_pure_imaginary'
        elif real_u and ur==0:z=mp.mpc(0);kind='polynomial_origin'
        else:kind='polynomial_complex'
        fv,fp=rational_fourier(cv,z,L,parity,True);res=abs(fv);rootshift=transform_floor/abs(fp) if fp else mp.inf;maxres=max(maxres,res)
        if i%max(1,len(rr)//12)==0 or i==len(rr)-1:
            fs=direct(cv,z,L,parity);max_sinc_res=max(max_sinc_res,abs(fs));max_sinc_difference=max(max_sinc_difference,abs(fs-fv));sinc_checks+=1
        roots.append(dict(root_id=f'p{i:03d}',kind=kind,u_re=mp.nstr(ur,180),u_im=mp.nstr(ui,180),z_re=mp.nstr(mp.re(z),180),z_im=mp.nstr(mp.im(z),180),u_ball_radius_re=decimal(u.real.rad(),15),u_ball_radius_im=decimal(u.imag.rad(),15),direct_F_residual=mp.nstr(res,35),direct_F_derivative_abs=mp.nstr(abs(fp),35),replay_rootshift_diagnostic=mp.nstr(rootshift,35),z_re_mp=mp.re(z),z_im_mp=mp.im(z)))
    for n in range(m+1,int(mp.floor(maxT/om))+1):
        z=n*om;roots.append(dict(root_id=f'e{n:03d}',kind='forced_external',harmonic=n,z_re=mp.nstr(z,180),z_im='0',z_re_mp=z,z_im_mp=mp.mpf(0)))
    # Origin multiplicity in odd parity is recorded separately, never counted as positive height.
    checks=dict(**info,max_direct_F_residual=mp.nstr(maxres,40),direct_F_method='rational Fourier sum all roots, stable sinc at harmonic proximity; independent sinc sample',independent_sinc_check_count=sinc_checks,max_independent_sinc_residual=mp.nstr(max_sinc_res,40),max_rational_sinc_difference=mp.nstr(max_sinc_difference,40),polynomial_real_positive_count=sum(r['kind']=='polynomial_real' for r in roots),polynomial_pure_imaginary_count=sum(r['kind']=='polynomial_pure_imaginary' for r in roots),polynomial_nonreal_count=sum(r['kind']=='polynomial_complex' for r in roots),odd_origin_forced=parity=='odd',spectral_replay_vector_infinity=mp.nstr(vdelta,40),spectral_replay_l2_upper=mp.nstr(replay_l2,40),spectral_replay_transform_floor=mp.nstr(transform_floor,40),replay_floor_scope='Cauchy-Schwarz upper bound on the observed between-precision transform difference, using sqrt(n) times the observed vector infinity difference. Dividing by |F derivative| is a first-order root-shift diagnostic, not an enclosure for exact-ground error.')
    if repeat:
        rr2,ii=isolate(c,m,parity,bits=info['bits']+max(200,m))
        z1=[mp.mpc(r['u_re'],r['u_im']) for r in roots if r['kind'].startswith('polynomial')];z2=[mp.mpc(decimal(x.real),decimal(x.imag)) for x in rr2]
        a,b=linear_sum_assignment(np.array([[float(abs(x-y)) for y in z2] for x in z1]));checks['repeat_bits']=ii['bits'];checks['repeat_max_u_distance']=mp.nstr(max(abs(z1[i]-z2[j]) for i,j in zip(a,b)),35);checks['repeat_scope']='polynomial arithmetic replay for the same supplied decimal vector; output floor ~180 digits'
    precision_replay,replay_mapping=low_vector_replay(data,parity,roots,m,L,Ts)
    for r in roots:
        if r['root_id'] in replay_mapping:r['observed_low_high_root_shift']=replay_mapping[r['root_id']]['root_shift'];r['low_high_root_shift_plus_resolution']=replay_mapping[r['root_id']]['root_shift_plus_resolution']
    src=references(world);results={};allmatches=[]
    for key,T in Ts.items():
        pairs,sm=match(roots,src,T);poly_pairs,poly_sm=match([r for r in roots if r['kind']!='forced_external'],src,T);sm['polynomial_only']=poly_sm;replay_shifts=[mp.mpf(r['replay_rootshift_diagnostic']) for r in roots if r['kind']!='forced_external' and 0<r['z_re_mp']<T and abs(r['z_im_mp'])<mp.mpf('.5')];sm['max_replay_rootshift_diagnostic']=mp.nstr(max(replay_shifts),35) if replay_shifts else None;sm.update(T=mp.nstr(T,50),T_over_Omega=mp.nstr(T/Om,40));sm['observed_precision_replay']=precision_replay.get('cutoffs',{}).get(key);sm['polynomial_nonreal_outside_strip_below_T']=sum(r['kind']=='polynomial_complex' and 0<r['z_re_mp']<T and abs(r['z_im_mp'])>=mp.mpf('.5') for r in roots);sm['pure_imaginary_positive_below_abs_T']=sum(r['kind']=='polynomial_pure_imaginary' and abs(r['z_im_mp'])<T for r in roots);sm['source_nonreal_quartet_count']=sm['source_nonreal_count']//2;sm['fourier_nonreal_quartet_count']=sm['fourier_nonreal_count']//2;results[key]=sm
        for pair in pairs:pair['cutoff']=key;pair['matching_scope']='all_fourier';allmatches.append(pair)
        for pair in poly_pairs:pair['cutoff']=key;pair['matching_scope']='polynomial_only';allmatches.append(pair)
    result=dict(census_schema_version=4,m=m,world=world,parity=parity,L=mp.nstr(L,180),Omega=mp.nstr(Om,180),kappa=mp.nstr(kap,45),source_vector_path=str(path),source_vector_sha256=hashlib.sha256(source_blob).hexdigest(),vector_coefficient_sha256=hashlib.sha256(json.dumps(c,separators=(',',':')).encode()).hexdigest(),source_coefficient_l2_norm=mp.nstr(mp.sqrt(mp.fsum(v*v for v in cv)),50),source_precision_dps=digits,vector_precision_dps=digits,matrix_source_precision_dps=data.get('source_precision_dps',digits),source_precision_field_scope='legacy source_precision_dps denotes supplied-vector solver precision; matrix source precision recorded separately',source_reference=reference_binding(world),root_output_digits=180,root_isolation_absolute_u_tolerance='1e-165',ground_resolved=data.get('ground_resolved'),solver_status=data.get('status'),global_parity=data.get('global_ground_parity',data.get('global_parity')),parity_ground_resolved=data.get(parity+'_ground_resolved'),lambda_even0=data.get('lambda_even0'),lambda_odd0=data.get('lambda_odd0'),parity_gap=data.get('parity_gap'),checks=checks,precision_replay=precision_replay,cutoffs=results,roots=[{k:v for k,v in r.items() if not k.endswith('_mp')} for r in roots],matches=allmatches,status='NUMERICAL_ROUNDED_VECTOR_POLYNOMIAL_CENSUS',scope='Complete isolated roots of the supplied decimal-vector numerator, plus exact external-carrier zeros; eigenvector error and source reference error are not enclosed. 160-digit zeta input is a reference floor; no RH/positivity/proof claim.')
    target=OUT/'results'/f'{world}_{parity}_m{m}.json';target.parent.mkdir(exist_ok=True);tmp=target.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(target)
    print(json.dumps(dict(file=str(target),m=m,world=world,parity=parity,degree=checks['degree'],seconds=checks['seconds'],source=results['fixed_c1_4']['source_count'],fourier=results['fixed_c1_4']['fourier_strip_count'],nonreal=results['fixed_c1_4']['fourier_nonreal_count'],external=results['fixed_c1_4']['structural_external_count'],max_error=results['fixed_c1_4']['max_abs_deviation'])),flush=True)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('vectors',nargs='+');ap.add_argument('--parity',choices=['even','odd','both','global'],default='even');ap.add_argument('--repeat',action='store_true');ns=ap.parse_args()
    for p in ns.vectors:
        if ns.parity=='both':ps=['even','odd']
        elif ns.parity=='global':
            d=json.loads(Path(p).read_text())
            if not d.get('ground_resolved'):raise ValueError('Cannot select global ground for unresolved spectral input')
            ps=[d.get('global_ground_parity',d.get('global_parity'))]
            if ps[0] not in ('even','odd'):raise ValueError('Missing resolved global parity')
        else:ps=[ns.parity]
        for parity in ps:run(p,parity,ns.repeat)
