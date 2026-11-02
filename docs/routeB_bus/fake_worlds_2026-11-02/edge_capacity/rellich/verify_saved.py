"""Saved-vector fixed-N Rellich check; no large source eigenproblem.

Run only after preregistration. Inputs are saved cell JSONs with A,E,U,Q,c.
"""
from pathlib import Path
import argparse,json,time,os,hashlib
import mpmath as mp
from rellich_helpers import Erow_and_dot,projector_velocity,direct_I,correlation_coefficients
from fixed_source import source_scalar,panels,weights
P=Path(__file__).resolve().parent
INPUT_ROOT=Path(os.environ.get('EDGE_CAPACITY_INPUT_ROOT',str(P.parent/'inputs')))
def fmt(x):return mp.nstr(x,80)

def run(path,dps=200,order=128,hstr='1e-20',fd_levels=1,do_fd=True):
    mp.mp.dps=dps;start=time.monotonic();d=json.loads(Path(path).read_text());m=int(d['m']);N=m;L=mp.log(m);world=d['world'];h=mp.mpf(hstr)
    c=mp.matrix(list(map(mp.mpf,d['complement_f'])));A=mp.matrix(d['A']);c=c/mp.norm(c);labels=d['row_labels']
    dhpath=Path(os.environ.get('DH_ZEROS',str(INPUT_ROOT/'edge_law/dh/dh_zeros_extended.json')))
    zd=json.loads(dhpath.read_text()) if world=='dh' else {}
    def node(label):
        g=mp.mpf(label['gamma']);kind=label.get('kind','line')
        if kind=='line':return g,kind
        if 'delta' in label:return g+mp.j*mp.mpf(label['delta']),kind
        q=min(zd['off_line_pairs'],key=lambda a:abs(mp.mpf(a['gamma'])-g))
        return g+mp.j*(mp.mpf(q['sigma_right'])-mp.mpf('.5')),kind
    nodes=[node(a) for a in labels]
    def evalmat(ell,der=False):
        rows=[]
        for z,kind in nodes:
            e,ed=Erow_and_dot(z,N,ell);row=ed if der else e
            if kind!='line':row=[mp.sqrt(2)*(mp.re(x) if kind=='real' else mp.im(x)) for x in row]
            rows.append(row)
        return mp.matrix(rows)
    E=evalmat(L);Ed=evalmat(L,True);U=mp.matrix(d['U']);pv=projector_velocity(E,Ed,c,A,U=U);project=pv['project'];pc=pv['dPi_c'];corr=pv['correction']
    quad=panels(order);base=source_scalar(list(c),N,L,world,quad=quad)
    bns=weights(world,m);kick=-2*bns[m]/mp.sqrt(m)*L*base['edge']**2
    lam=(c.T*A*c)[0];FD=[]
    for hh in ([h/mp.mpf(10)**k for k in range(fd_levels)] if do_fd else []):
        vals={}
        for sign in [-1,1]:
            ell=L*mp.exp(sign*hh);Et=evalmat(ell);ct=Et.T*mp.lu_solve(Et*Et.T,Et*c);ct=ct/mp.norm(ct)
            vals[sign]=source_scalar(list(ct),N,ell,world,quad=quad,all_terms=False)['energy']
        left=(base['energy']-vals[-1])/hh;right=(vals[1]-base['energy'])/hh
        FD.append(dict(h=fmt(hh),left=fmt(left),right=fmt(right),pred_left=fmt(base['virial']+corr),pred_right=fmt(base['virial']+corr+kick),left_abs_error=fmt(abs(left-base['virial']-corr)),right_abs_error=fmt(abs(right-base['virial']-corr-kick))))
    Q,Qp,edge,e=correlation_coefficients(list(c),L)
    leib=[]
    for ss in [L/7,mp.log(2),L*mp.mpf('.95')]:
        ii=direct_I(list(c),L,ss);leib.append(abs(Qp(ss)-(2*ii-2*e*edge(ss))))
    scale=e*e*mp.log(mp.mpf(d['T']))/mp.mpf(d['T'])
    # Formula for evaluation derivative checked independently at fixed nodes.
    eps=mp.mpf('1e-35');Ed_fd=(evalmat(L*mp.exp(eps))-evalmat(L*mp.exp(-eps)))/(2*eps)
    out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',input=str(path),input_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),m=m,q=E.rows,world=world,dps=dps,GL_order=order,seconds=time.monotonic()-start,
      local_path='L_tau=L*exp(tau), N fixed, same active actual zero coordinates',FD_scope='transported saved-vector Rayleigh; actual eigenbranch FD only in independent m8 control',
      source_energy=fmt(base['energy']),saved_rayleigh=fmt(lam),source_energy_discrepancy=fmt(abs(base['energy']-lam)),
      source_left_virial=fmt(base['virial']),source_archdot=fmt(base['archdot']),source_atomdot=fmt(base['atomdot']),source_poledot=fmt(base['poledot']),
      edge=fmt(e),relative_scale_e2_logT_over_T=fmt(scale),boundary_flux=fmt(base['boundary']),source_volume=fmt(base['volume']),boundary_volume_identity_error=fmt(abs(base['virial']-base['boundary']-base['volume'])),
      projector_correction=fmt(corr),projector_velocity_norm=fmt(mp.norm(pc)),projector_correction_relative=fmt(corr/scale),r_norm=fmt(mp.norm(pv['r'])),endpoint_atom_kick=fmt(kick),
      Pi_c_error=fmt(mp.norm(project(c)-c)),compressed_stationarity_error=fmt(mp.norm(project(A*c)-lam*c)),Pi_idempotence_bound_from_saved_U_orthogonality=d.get('U_orthogonality_residual'),E_saved_discrepancy=fmt(mp.norm(E-mp.matrix(d['E']))),Ed_central_difference_error=fmt(mp.norm(Ed-Ed_fd)),
      Leibniz_direct_max_error=fmt(max(leib)),FD=FD)
    eig=list(map(mp.mpf,d['complement_eigenvalues']));gap=eig[1]-eig[0] if len(eig)>1 else None;gap_source='saved full reduced spectrum'
    cap=P.parent/'capacity'/(Path(path).stem+'_capacity_dps80.json')
    if gap is None and cap.exists():
        ce=json.loads(cap.read_text())['compressed_spectrum'];gap=mp.mpf(ce[1])-mp.mpf(ce[0]);gap_source=str(cap)
    if gap is None and d.get('source_path'):
        raw=json.loads(Path(d['source_path']).read_text());g=raw.get('complement_gap',raw.get('minimum_controls',{}).get('float_minimum_gap'))
        if g is not None:gap=mp.mpf(g);gap_source='source saved minimum-isolation gap (floating diagnostic)'
    if gap is None:gap=mp.inf;gap_source='NOT_AVAILABLE; transported-vector derivative only'
    out.update(saved_compressed_gap=fmt(gap),stationarity_error_over_saved_gap=fmt(mp.norm(project(A*c)-lam*c)/gap),
      gap_source=gap_source,no_new_large_source_eigenproblem=True,active_row_count_constant=True)
    gammas=[mp.re(z) for z,kind in nodes];T=mp.mpf(d['T']);out['cutoff_lower_active_margin']=fmt(min(T-g for g in gammas))
    out['FD_step_below_lower_cutoff_event_margin']=bool(h*T<min(T-g for g in gammas))
    external=[]
    for z,kind in nodes:
        if mp.im(z):continue
        nn=mp.nint(z*L/(2*mp.pi))
        if nn>N:external.append(abs((2*mp.pi*nn/z-L)/L))
    out['automatic_external_sinc_rank_event_relative_margin']=fmt(min(external)) if external else 'no nearby external modal integer'
    name=f'{world}_m{m}_q{E.rows}_dps{dps}_gl{order}.json';(P/name).write_text(json.dumps(out,indent=2)+'\n');print(name,json.dumps({k:out[k] for k in ['source_left_virial','projector_correction','endpoint_atom_kick','source_energy_discrepancy','Leibniz_direct_max_error','seconds']}),flush=True)
    return out
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('path');a.add_argument('--dps',type=int,default=200);a.add_argument('--order',type=int,default=128);a.add_argument('--h',default='1e-20');a.add_argument('--analytic-only',action='store_true');a.add_argument('--fd-levels',type=int,default=1);q=a.parse_args();run(q.path,q.dps,q.order,q.h,q.fd_levels,not q.analytic_only)
