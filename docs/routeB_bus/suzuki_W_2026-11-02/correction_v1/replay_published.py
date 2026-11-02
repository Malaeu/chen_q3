"""Bounded readback of the concurrently published full-parity W packet.

Input: exact files from a8b5d995.../suzuki_W_2026-11-02/W.
No source files or old reports are changed. No continuum W is certified.
"""
from pathlib import Path
import argparse,importlib.util,csv,json,hashlib
import numpy as np

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def main():
    p=argparse.ArgumentParser();p.add_argument('--input-root',type=Path,required=True);a=p.parse_args();r=a.input_root
    pinned=json.loads(Path(__file__).with_name('PINNED_W_INPUTS.json').read_text())
    for item in pinned['files']:
        assert hashlib.sha256((r/item['name']).read_bytes()).hexdigest()==item['sha256'],item['name']
    proto=load('pinned_prototype',r/'prototype.py');diag=load('pinned_diagnostics',r/'diagnostics.py')
    scalars=list(csv.DictReader((r/'all_m_scalars.csv').open()))
    assert len(scalars)==442
    for world in ['zeta','dh']:
        assert sorted(int(d['m']) for d in scalars if d['world']==world)==list(range(20,241))
    assert all(d['vminus_rule']=='same even coefficients; negate odd coefficients' for d in scalars)
    assert all(float(d['finite_T_gap'])>0 for d in scalars)
    rows=[]
    for world in ['zeta','dh']:
        d=json.loads((r/f'profile_{world}_m20.json').read_text());m=d['m'];L=d['L'];lam=d['lambda_shift']
        Ae,Ao,_=proto.build(world,m);ce=np.array(d['even_coefficients']);co=np.array(d['odd_coefficients'])
        n=np.arange(m+1);omega=2*np.pi*n/L;ds=np.r_[1.,np.repeat(np.sqrt(2),m)];norm=d['raw_T_norm']
        be=2*ds*np.sinh(L/2)/(np.sqrt(L)*(1+omega**2))
        bo=-2*np.sqrt(2)*omega[1:]*np.sinh(L/2)/(np.sqrt(L)*(1+omega[1:]**2))
        re=np.linalg.norm((Ae-lam*np.eye(m+1))@ce-be/norm)
        ro=np.linalg.norm((Ao-lam*np.eye(m))@co-bo/norm)
        assert re<1e-10 and ro<1e-10 and np.linalg.norm(co)>0
        nodes,weights=np.polynomial.legendre.leggauss(256);xs=d['a']*nodes;weights*=d['a']
        even=(np.cos(xs[:,None]*omega)*(ds*(-1.)**n/np.sqrt(L)))@ce
        odd=(np.sin(xs[:,None]*omega[1:])*(ds[1:]*(-1.)**n[1:]/np.sqrt(L)))@co
        errors=[];omissions=[]
        for z in [0,.5j,1j,2j,1+.25j,-2+.5j]:
            phase=np.exp(1j*z*xs);U=weights@(even*phase);O=weights@(odd*phase)
            C,S=diag.pieces(d,z)
            fourier_error=max(abs(C-U),abs(1j*S-O))/max(1.,abs(U),abs(O))
            W=diag.W(d,z,np.pi);expected=-2j*U+2*z*O
            w_error=abs(W-expected)/max(1.,abs(expected))
            assert fourier_error<1e-10 and w_error<1e-10
            errors.append(dict(z=str(z),direct_FT_relative_error=float(fourier_error),theta_pi_relative_error=float(w_error)))
            omissions.append(float(abs(expected+2j*U)))
        assert max(omissions)>1e-6
        rows.append(dict(world=world,m=20,normalized_even_RHS_residual=float(re),normalized_odd_RHS_residual=float(ro),odd_solution_norm=float(np.linalg.norm(co)),maximum_omitted_odd_contribution=max(omissions),point_checks=errors))
    out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',published_commit='a8b5d995b86522cfcda5ab1f5be3500a1ed7e008',scalar_rows_checked=442,all_m_reflection_conventions_match=True,real_source_replays=rows,scope='Code inspection and bounded m20 two-world numerical replay; not a full independent 442-cell rerun',recalculation_for_old_formula_required=False,reason='Published solver already uses both parity blocks, same lambda, same-sign exponential loads and complete W assembly',input_sha256={name:hashlib.sha256((r/name).read_bytes()).hexdigest() for name in ['prototype.py','diagnostics.py','all_m_scalars.csv','profile_zeta_m20.json','profile_dh_m20.json']})
    Path(__file__).with_name('PUBLISHED_REPLAY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
