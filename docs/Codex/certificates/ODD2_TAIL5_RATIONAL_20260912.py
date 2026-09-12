from fractions import Fraction as Q
import math, json
checks=[]
def lt(name,a,b):
    assert a<b, name
    checks.append({'name':name,'left':str(a),'right':str(b),'strict':True})
lt('sqrt_e_lower',Q(41,25)**2,Q(19,7))
lt('q_quarter_lower',Q(5),Q(25,8)*Q(41,25))
lt('derivative_polynomial',4+Q(1,5)+Q(3,200)+Q(3,10)+Q(3,4000),5)
lt('n_ge3_ratio',Q(4,3)**8*Q(7,19)**35,Q(1,2))
lt('E_remainder',Q(82584,5)*Q(7,19)**15+1640250*Q(7,19)**40,Q(1,128))
lt('quotient_first',Q(130,49*128),Q(1,48))
lt('quotient_second',Q(2890,343*128),Q(1,15))
lt('log_second',Q(1,15)+Q(1,48)**2,Q(1,14))
lt('exp_3quarter',sum((Q(3,4)**n/math.factorial(n) for n in range(5)),Q(0))+Q(3,4)**5/math.factorial(5)/(1-Q(1,8)),Q(17,8))
J1=Q(110,21)-Q(9,2)-Q(84,145)-Q(7854,21025)+Q(1,21)
assert J1==-Q(49201,294350)
lt('J_first',J1,-Q(27,512))
lt('J_second',Q(187,56)-Q(9,2)+Q(1,28)+Q(1,48),-Q(1,8))
lt('J_third',-Q(9,2)+Q(1,14)+Q(1,48),-Q(1))
lt('q_17over16',Q(22,7)*Q(11,4)**2*Q(8,7),28)
lt('slope_lower',-32,(Q(9,2)-56-Q(1,3))/(2*Q(17,16)))
lt('diagonal_domain',Q(33,32),Q(17,16)**2)
mu=(1-3*Q(7,19)**2)/8192
assert mu==Q(107,1478656)
lt('small_diag_budget',Q(1,14000),mu)
lt('alpha4',Q(4096),3*Q(8,3)**8)
lt('gamma_bound',Q(137,2),Q(4096,10))
local=Q(28,13)*(Q(6400,361*1024)+Q(256000,6859*4096**2)+Q(10,19))
assert local==Q(213822315,182614016)
lt('local_mixed',local,Q(6,5))
lt('remote_prefactor',38*3**20,3**24)
lt('remote_exponential',3**61,2**98)
lt('mixed_budget',Q(6,5)+Q(1,2**30),Q(5,4))
assert 12*Q(25,16)*14000==262500
lt('determinant_half_budget',262500,15*Q(19,7)**10)
print(json.dumps({'status':'PASS','count':len(checks),'checks':checks,'source_evaluations':0,'global_ODD2':False,'RH_claim':False},indent=2))
