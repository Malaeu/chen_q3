#!/usr/bin/env python3
"""Fixed-Gaussian detection formula. DIAG, no finite matrix extrapolation.

Uses a magnitude envelope for on-line terms, not their phase-dependent sum.
Without an explicit global return bound, output is a necessary lower benchmark
for the requested envelope threshold, and m_star is deliberately null.
"""
import argparse
import hashlib
import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / 'docs/routeB_bus/arithmetic_coupling_2026-11-03/source_inputs/dh_zeros_900_200dps.json'

def log_pair_envelope(delta, gamma):
    u = mp.mpc(delta, gamma)
    return mp.log(2) + 4*mp.log(abs(u)) + 2*mp.log(abs(u*u-mp.mpf(1)/4)) + mp.re(u*u)/2

def online_envelope(gammas):
    return mp.fsum(mp.exp(log_pair_envelope(mp.mpf(0), gamma)) for gamma in gammas)

def fmt(x):
    return mp.nstr(x, 65)

def log_return_bound(L, planted=False):
    # Task B's explicit weighted piecewise-H1 continuity estimate.
    # The quartet increases 27 to 32 by Cauchy-Schwarz at a=1/3.
    e1=27*mp.log(10)+mp.log1p(L)+3*L/4-L*L/256
    e2=27*mp.log(10)+4*mp.log1p(L)-5*L/4
    le=max(e1,e2)+mp.log1p(mp.exp(-abs(e1-e2)))
    lf=mp.log(400000)+L/4
    return mp.log(32 if planted else 27)+le+max(lf,le)+mp.log1p(mp.exp(-abs(lf-le)))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps', type=int, default=80)
    parser.add_argument('--bound', choices=['unavailable','explicit'], default='explicit')
    args=parser.parse_args()
    mp.mp.dps=args.dps
    census=json.loads(CENSUS.read_text())
    dh_census_online=online_envelope([mp.mpf(z['gamma']) for z in census['critical_line_zeros']])
    dh_tail=8*mp.mpf(901)**10*mp.exp(-mp.mpf(900)**2/2)
    dh_online=dh_census_online+dh_tail
    zeta_gammas=[]
    for k in range(1,100):
        gamma=mp.im(mp.zetazero(k))
        if gamma>60: break
        zeta_gammas.append(gamma)
    zeta_census_online=online_envelope(zeta_gammas)
    zeta_tail=8*mp.mpf(61)**10*mp.exp(-mp.mpf(60)**2/2)
    zeta_online=zeta_census_online+zeta_tail
    data=dict(status='DIAG_ONLY', dps=args.dps,
        census_sha256=hashlib.sha256(CENSUS.read_bytes()).hexdigest(),
        census_status=census['status'],
        online_convention='Magnitude envelope 2*sum_positive_gamma |F(i*gamma)|^2; no cancellation credit. DH uses listed census line zeros; planted world uses zeta gamma<=60.',
        online_envelope=dict(dh=fmt(dh_online),zeta=fmt(zeta_online)),
        online_tail_upper=dict(dh=fmt(dh_tail), zeta=fmt(zeta_tail)),
        auxiliary_count_bound='For omitted tails use N_world(T)<=T^2 at integer T>=T0. Zeta: Task A. DH: theta-Mellin/Jensen argument documented in task_c_notes.md, valid T>=900; all nontrivial zeros counted, no RH assumption.',
        return_bound='E=1e27*(1+L)*exp(3L/4-L^2/256)+1e27*(1+L)^4*exp(-5L/4); B=27*E*(4e5*exp(L/4)+E), L>=1. For plant coefficient 32 replaces 27.',
        source_scope='DH rows compare the listed DH online envelope to the specified Task B zeta return bound. They are a formula regime map, not a verified DH-source return theorem.',
        omitted_online_tail_status='In each integer bin [k,k+1), 2|F(i*gamma)|^2 <= 4*(k+1)^8*exp(-k^2/2); summing with N(k+1)<=(k+1)^2 gives tail <=8*(T0+1)^10*exp(-T0^2/2). DH count inequality follows from documented theta/Jensen argument. Census completeness remains numerical, not interval certified.',
        bound_status=args.bound, rows=[])
    inputs=[('dh', i+1,mp.mpf(z['sigma_right'])-mp.mpf('.5'),mp.mpf(z['gamma']),dh_online) for i,z in enumerate(census['off_line_pairs'])]
    inputs.append(('planted_quartet',1,mp.mpf(1)/3,mp.mpf(7),zeta_online))
    for world,i,delta,gamma,baseline in inputs:
        le=log_pair_envelope(delta,gamma)
        raw_L=2*(mp.log(baseline)-le)/delta
        row=dict(world=world,index=i,sigma_right=fmt(mp.mpf('.5')+delta),gamma=fmt(gamma),
            log_pair_amplitude=fmt(le), log_m_online_only_crossing=fmt(raw_L),
            log_m_online_only_at_least_3=fmt(max(mp.log(3),raw_L)),
            log_m_star=None,
            status='RETURN_BOUND_UNAVAILABLE: online-only crossing is a necessary lower benchmark, not the requested m_star')
        if args.bound=='explicit':
            # Contract with task_b: natural-log upper bound valid for all L>=log(3).
            def find_crossing(online):
                def gap(L):
                    lb=log_return_bound(L, planted=(world=='planted_quartet'))
                    la=mp.log(online)
                    rhs=max(la,lb)+mp.log1p(mp.exp(-abs(la-lb)))
                    return le+delta*L/2-rhs
                lo=mp.log(3);hi=max(lo+1,2*(mp.log(online)-le)/delta+1)
                while gap(hi)<=0: hi*=2
                if gap(lo)>0:
                    return lo
                for _ in range(300):
                    mid=(lo+hi)/2
                    if gap(mid)>0: hi=mid
                    else: lo=mid
                return (lo+hi)/2
            crossing=find_crossing(baseline)
            q_crossing=find_crossing(4*baseline)
            row.update(log_m_star=fmt(crossing),
                log_m_star_q_target_online_envelope=fmt(q_crossing),
                q_target_alternative='Same prescribed 2|F|^2 growing amplitude, but charge 4A for online part of 2W[g]+2h(L/2), A=2*sum|F(i gamma)|^2.',
                status=('DIAG_DH_CENSUS_COMPLETENESS_UNCERTIFIED' if world=='dh' else 'DIAG_ZETA_PLANT_TOTAL')+'; continuous envelope crossing; smallest integer m = floor(exp(L_cross))+1 unless already m=3',
                integer_log_correction_upper=fmt(mp.exp(-crossing)))
        data['rows'].append(row)
    (OUT/'task_c.json').write_text(json.dumps(data,indent=2)+'\n')
    for z in data['rows']:
        print(z['world'],z['index'],mp.nstr(mp.mpf(z['gamma']),10),z['log_m_star'] or z['log_m_online_only_at_least_3'])

if __name__=='__main__': main()
