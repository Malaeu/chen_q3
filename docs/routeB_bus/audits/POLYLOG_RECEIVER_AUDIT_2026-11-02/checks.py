#!/usr/bin/env python3
"""Bounded exact audit controls. No zero assignment, spectra, Lean or Arb.

python checks.py --sources /path/to/snapshots
python checks.py --repo /path/to/repository
Without either option only the exact algebra controls run. Source snapshots
are not duplicated in this commit: fetch the immutable refs in SOURCES.json.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sympy as s

P = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
g = ap.add_mutually_exclusive_group()
g.add_argument('--sources', type=Path)
g.add_argument('--repo', type=Path)
args = ap.parse_args()
passed = []
sources = []
if args.sources or args.repo:
    for row in json.loads((P/'SOURCES.json').read_text())['sources']:
        if args.sources:
            b = (args.sources/row['local_name']).read_bytes()
        else:
            b = subprocess.check_output(['git', '-C', str(args.repo), 'show',
                                         row['ref']+':'+row['path']])
        assert len(b) == row['bytes']
        assert hashlib.sha256(b).hexdigest() == row['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() == row['git_blob']
        sources.append(row['local_name'])

def check(name, statement):
    assert bool(statement), name
    passed.append(name)

# The full reflected quartet, rather than a modulus-square surrogate.
A, nu = s.symbols('A nu', positive=True)
vals = [s.I*A, s.I*A, -s.I*A, -s.I*A]
partners = [2, 3, 0, 1]
quartet = s.expand(nu*sum(s.conjugate(vals[partners[j]])*vals[j]
                         for j in range(4)))
check('quartet_sign_and_four_multiplicities', quartet == -4*nu*A**2)
check('two_translation_normalization',
      s.expand(quartet.subs(A, 2*s.Symbol('C', real=True)))
      == -16*nu*s.Symbol('C', real=True)**2)
check('planted_positive_quartet_rejected', quartet != 4*nu*A**2)

# Real coefficients a,b interpolate a complex target at a non-real z0².
x, y, hr, hi = s.symbols('x y hr hi', real=True, nonzero=True)
aa, bb = hr-hi*x/y, hi/y
check('real_polynomial_separator_interpolation',
      s.simplify(aa+bb*(x+s.I*y)-(hr+s.I*hi)) == 0)

# Simultaneous contact correction, not successive untracked projections.
r = s.symbols('r', real=True)
Gram = s.Matrix([[1,r],[r,1]])
check('two_contact_gram_inverse',
      s.simplify(Gram.inv()-s.Matrix([[1,-r],[-r,1]])/(1-r*r)) == s.zeros(2))
z = s.symbols('z')
check('two_contact_characteristic_polynomial',
      s.expand((Gram-z*s.eye(2)).det()-((1-z)**2-r*r)) == 0)

# Exact physical pole norm and its cosine coefficients.
L = s.symbols('L', positive=True)
t = s.symbols('t', real=True)
pole_norm = s.integrate(2*s.cosh(t/2)**2, (t,-L/2,L/2))
check('physical_pole_norm', s.simplify(pole_norm-L-2*s.sinh(L/2)) == 0)
check('arch_constant_margin', s.Rational(1,4)+4*s.exp(-s.Rational(1,2)) < 3)
check('multiplier_constant_margin', 4*s.sqrt(2)+2 < 8)
tt = s.symbols('tt', nonnegative=True)
check('Euler_Maclaurin_abs_s_bound',
      s.expand((1+tt)**2-(s.Rational(1,4)+tt**2)) == 2*tt+s.Rational(3,4))

# Full binomial valuation for the psi dyadic increment; finite controls only.
for n in range(1,33):
    fac = s.factorint(s.binomial(2*n,n))
    for p in s.primerange(2,2*n+1):
        power, needed = p, 0
        while power <= 2*n:
            needed += int(power > n)
            power *= p
        assert fac.get(p,0) >= needed, (n,p)
passed.append('32_binomial_prime_power_increment_controls')

# Proper-power and continuum terms returned with their signs.
Hp, P12, P3, IL, R0, cs, norm = s.symbols('Hp P12 P3 IL R0 cs norm')
K = Hp+4*norm-R0-cs*norm-P12-P3+IL+R0
q = Hp-P12+IL
check('complete_q_to_K_return', s.expand(q-K-(cs-4)*norm-P3) == 0)
B = Hp+4*norm-R0-cs*norm
check('pole_free_K_equals_B_minus_all_powers',
      s.expand(K.subs(IL,-R0)-B+P12+P3) == 0)

# A controlled auxiliary Gram supplies no lower bound for a signed source.
X = s.symbols('X', positive=True)
check('planted_auxiliary_budget_implies_source_lower_rejected', -X < 0)
out = {'status':'BOUNDED_EXACT_CONTROLS_PASS',
       'target_sha256':'dad2cf2f9c2bdfe61a722ebf4f0ac0e3fc9fb6b0afed07c528a4d0de1fc929e1',
       'source_files_verified':sources, 'exact_controls':passed,
       'sympy_version':s.__version__, 'new_spectral_scans':0,
       'interval_certification':False, 'universal_bounds_verifier':'PAPER, not finite controls',
       'RH_proved':False, 'route_state_changed':False}
print(json.dumps(out,indent=2)+'\n',end='')
