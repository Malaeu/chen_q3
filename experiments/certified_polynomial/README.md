# Minimal polynomial constructor with certified pruning

This is a narrow, reproducible demonstration, not a general function-synthesis
library and not a CF22 result. The admissible family is

```
p(x) = a + b*x^2 + c*x^4,
x in [-1,1], p(0)=1, p(-1)=p(1)=1/2,
p(x) >= 1/(1+x^2) everywhere on the interval.
```

The objective is the exact integral of p on [-1,1]. A numerical linear program
proposes coefficients; rational reconstruction produces a new exact candidate.
A separate exact checker decides its mathematical status. A solver success
flag, sample grid or reconstruction tolerance is never a universal certificate.

## Algebraic certificate for the whole family

Contacts force a=1, b=-1/2-c. Set t=x^2, so t runs over [0,1]. Then

```
(1+t)*p(sqrt(t))-1 = t*(1-t)*(1/2-c-c*t).
```

The denominator 1+t is positive. The last linear factor has Bernstein
coefficients 1/2-c and 1/2-2c. Nonnegative coefficients prove the inequality
on the entire interval, including the endpoints: c<=1/4 suffices.

This condition is also necessary in this special family. If c>1/4, choose
t=1/(4c), which lies strictly between 0 and 1. The last factor becomes
1/4-c<0. Hence there is a point x=sqrt(t) in the stated domain where the
upper-bound requirement fails. Thus the exact feasible set is c<=1/4.
Bernstein positivity is not claimed to be necessary for arbitrary polynomials.

The integral is I(c)=5/3-4c/15. On the full feasible family,

```
I(c)-8/5 = (1-4c)/15 >= 0.
```

Equality holds exactly at c=1/4. Thus the certified optimum in this family is
p=1-3x^2/4+x^4/4, with I=8/5. This is a known elementary result reproduced by
the program; the algebraic reduction is supplied, not discovered by SciPy.

## Two different reasons to prune

1. INFEASIBLE: c in [13/50,1/2]. At x=49/50, the gap decreases with c and is
   already -288328887/1531562500000 at c=13/50. This one point refutes every
   member of the continuous family, not just a finite sample.
2. CANNOT_IMPROVE: c in [0,1/5]. Every member is feasible, but its integral is
   at least 121/75, strictly greater than the verified incumbent 8/5.
   Discarding this branch in minimization does not mean it has no solutions.

The bad candidate a=1,b=-19/25,c=13/50 satisfies the contacts and has a smaller
integral 599/375, yet fails the universal inequality at the exact point above.
The branch crossing c=1/4 must not be declared infeasible: it contains the
optimal feasible candidate. Endpoint and tampering tests protect these limits.

## Numerical engine

The implementation uses SciPy `linprog` with explicit free coefficient bounds;
its default nonnegative-variable bounds would incorrectly exclude negative b.
See the [official linprog documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.linprog.html).
The recorded environment already contains Python 3.12, SciPy 1.18.1 and SymPy
1.14.0. No dependencies were installed for this demonstration.

The exact certificate applies only to the stated family, contacts, target and
domain. It does not certify arbitrary rational functions, detect all possible
poles, or establish any arithmetic estimate for the CF22 source.

## Replay

Recorded run: Python 3.12.15, SciPy 1.18.1, SymPy 1.14.0. The existing local
interpreter was `/tmp/cf22-pysr-venv/bin/python`. For another machine, use a
Python environment with those package versions. No solver dependencies are
needed for the standalone certificate replay (`verify_certificate.py`).

From the repository root (output paths must not already exist):

```sh
/tmp/cf22-pysr-venv/bin/python -m unittest discover -s experiments/certified_polynomial -v
/tmp/cf22-pysr-venv/bin/python experiments/certified_polynomial/constructor.py --output /tmp/polynomial-new-result.json
python3 experiments/certified_polynomial/verify_certificate.py --input /tmp/polynomial-new-result.json --output /tmp/polynomial-new-verification.json
```

`result.json` records the actual run; `verification.json` binds the standalone
replay to its input and checker SHA256 hashes. The checker independently
recomputes exact statements; it does not trust the numerical solver, import
the constructor, or use floating-point arithmetic. Its fixed algebraic rules
and Python runtime are part of the trusted base; this is not a Lean proof.
Eight tests pass, including seven certificate-tampering cases. Intervals
crossing the optimum remain unresolved by the simple pruning rules.
