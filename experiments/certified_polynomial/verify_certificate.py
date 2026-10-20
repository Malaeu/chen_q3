#!/usr/bin/env python3
"""Replay this fixed polynomial contract using only exact standard-library arithmetic."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(isinstance(value, str), 'certificate rationals must be strings')
    return Q(value)


def gap(a, b, c, x):
    return a + b*x*x + c*x**4 - 1/(1+x*x)


def coefficients(item):
    a, b, c = (rational(item['coefficients'][k]) for k in ('a', 'b', 'c'))
    require(a == 1 and a+b+c == Q(1, 2), 'contacts fail')
    return a, b, c


def verify(report):
    require(report['contract'] == {
        'family': 'even_quartic', 'domain': ['-1', '1'],
        'target': '1/(1+x^2)', 'contacts': {'0':'1', '-1':'1/2', '1':'1/2'},
        'objective': 'integral_-1^1_p'}, 'unsupported contract')
    # Coefficient identity in t=x^2, checked for arbitrary c by coefficients in c.
    # (1+t)(1+(-1/2-c)t+ct^2)-1 = t(1-t)(1/2-c-ct).
    # Both sides have coefficients [0, 1/2-c, -1/2, c].
    for c in (Q(0), Q(1)):  # both expressions are affine in c
        left = [Q(0), Q(1,2)-c, Q(-1,2), c]
        h0, h1 = Q(1,2)-c, -c
        right = [Q(0), h0, h1-h0, -h1]
        require(left == right, 'factor identity fails')
    # The last linear factor is nonnegative on [0,1] iff c<=1/4.
    # Necessity: for c>1/4, t=1/(4c) lies in (0,1) and gives 1/4-c<0.
    a,b,c = coefficients(report['candidate'])
    v = report['candidate']['verification']
    require(c <= Q(1,4), 'candidate violates universal bound')
    objective = 2*a+Q(2,3)*b+Q(2,5)*c
    require(objective-Q(8,5) == (1-4*c)/15 == 0, 'candidate is not optimal')
    require(v['status'] == 'VERIFIED' and v['upper_bound'] is True, 'candidate status')
    require(rational(v['objective']) == objective, 'candidate objective')
    require(list(map(rational,v['bernstein_coefficients'])) == [Q(1,2)-c,Q(1,2)-2*c], 'candidate Bernstein coefficients')
    require(v['optimality']['candidate_is_optimal'] is True, 'optimality status')
    require(rational(v['optimality']['objective_lower_bound']) == objective, 'optimality bound')
    a,b,c = coefficients(report['bad_candidate'])
    v = report['bad_candidate']['verification']
    x = rational(v['counterexample']['x'])
    require(-1 <= x <= 1, 'counterexample outside domain')
    value = gap(a,b,c,x)
    require(value < 0 and rational(v['counterexample']['gap_p_minus_target']) == value, 'bad candidate not refuted')
    require(v['status'] == 'REFUTED', 'bad status')
    statuses = []
    for family in report['families']:
        require(family['parameter'] == 'c', 'unsupported parameter')
        lo, hi = rational(family['lower']), rational(family['upper'])
        require(lo <= hi, 'reversed family')
        cert, status = family['certificate'], family['status']
        if status == 'INFEASIBLE':
            x = rational(cert['uniform_x'])
            require(-1 <= x <= 1, 'family witness outside domain')
            value = gap(Q(1),-Q(1,2)-lo,lo,x)
            slope = x**4-x*x
            require(value < 0 and slope <= 0, 'family not uniformly refuted')
            require(rational(cert['gap_at_lower']) == value and rational(cert['gap_slope_in_c']) == slope, 'family gap mismatch')
        elif status == 'CANNOT_IMPROVE':
            require(hi <= Q(1,4), 'family feasibility not established')
            bound = Q(5,3)-Q(4,15)*hi
            require(bound > objective, 'family can improve incumbent')
            require(rational(cert['objective_lower_bound']) == bound and rational(cert['incumbent_objective']) == objective, 'family objective mismatch')
            require(rational(cert['objective_slope']) == -Q(4,15), 'objective slope')
            require(list(map(rational,cert['bernstein_coefficients_at_upper'])) == [Q(1,2)-hi,Q(1,2)-2*hi], 'family Bernstein coefficients')
        else:
            raise ValueError('uncertified family status')
        statuses.append(status)
    require(sorted(statuses) == ['CANNOT_IMPROVE','INFEASIBLE'], 'expected two pruning demonstrations')
    return {'status':'PASS', 'candidate':'VERIFIED_OPTIMAL', 'bad_candidate':'REFUTED',
            'families':statuses, 'scope':'fixed even-quartic contract on [-1,1]; no CF22 claim'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    result = verify(json.loads(raw))
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
