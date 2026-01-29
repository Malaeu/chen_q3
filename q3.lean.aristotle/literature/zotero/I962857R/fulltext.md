---
title: "The positivity of a sequence of numbers and the Riemann hypothesis"
authors:
  - "Xian-Jin Li"
date: "1997-00-00 1997"
publication: "Journal of Number Theory"
doi: "10.1006/jnth.1997.2137"
url: null
zotero:
  attachment_key: "N85SXDDK"
  parent_key: "I962857R"
  item_id: 1966
  attachment_item_id: 2065
---

journal of number theory 65, 325 333 (1997)
The Positivity of a Sequence of Numbers and the Riemann Hypothesis
Xian-Jin Li
The University of Texas at Austin, Austin, Texas 78712
Communicated by A. Granville
Received September 10, 1996; revised December 16, 1996
In this note, we prove that the Riemann hypothesis for the Dedekind zeta function is equivalent to the nonnegativity of a sequence of real numbers. 1997 Academic Press
1. THE RIEMANN ZETA FUNCTION
Let [*n] be a sequence of numbers given by
(n&1)! *n= d n
dsn [sn&1 log !(s)]s=1 (1.1)
for all positive integers n, where
!(s)=s(s&1) ?&s 21 \ s
2+ `(s)
with `(s) being the Riemann zeta function.
Theorem 1. A necessary and sufficient condition for the nontrivial zeros of the Riemann zeta function to lie on the critical line is that *n is nonnegative for every positive integer n.
Proof. Define
.(z)=! \ 1
1&z+=4 |1
[x3 2 $(x)]$ (x&1 2x1 2(1&z)+x&1 2(1&z)) dx (1.2)
article no. NT972137
325 0022-314X 97 25.00
Copyright 1997 by Academic Press All rights of reproduction in any form reserved.


 for z in the unit disk, where
(x)= :
n=1
e&?n 2x.
Write
!(s)=`
\ \1&s
\+ (1.3)
where the product is taken over all nontrivial zeros of the Riemann zeta function with \ and 1&\ being paired together. It follows that
.(z)=`
\
1&(1&(1 \))z
1&z .
A necessary and sufficient condition for the nontrivial zeros of the Riemann zeta function to lie on the critical line is that .$(z) .(z) is analytic in the unit disk. Put
.$(z)
.(z) = :
n=0
*n+1 zn
for |z| < 1
4 , where
*n=:
\ _1&\1&1
\+n& (1.4)
for every positive integer n. On the other hand, by (1.3) we have
1
(n&1)!
dn
dsn [sn&1 log !(s)]s=1=&:
\
:
n&1
k=0 \n
k+ (\&1)k&n
=:
\ _1&\1&1
\+n& ,
and hence *n is also given by the expression (1.1). Let
.(z)=1+ :
j=1
aj z j. (1.5)
We find that
*n=n :
n
l=1
( &1 ) l & 1
l:
k1+ } } } +kl=n
1 k1 , ..., kl n
ak1 } } } akl
326 XIAN-JIN LI


 for every positive integer n. Expanding the right side of (1.2) in power series (1.5), we find that
aj=2 :
n=0
( j+n) } } } ( j+1)
n! (n+1)! 2n |1
[x3 2 $(x)]$ (x&1 2+(&1)n+1)(log x)n+1 dx
(1.6)
for every positive integer j. By (1.6) we can write
aj=4 :
n=0
(n+j ) } } } (n+1)
j! (n+1)! 2n+1 |1
[x3 2 $(x)]$ (x&1 2+(&1)n+1)(log x)n+1 dx
=4
j!
dj
dt j {t j&1 :
n=0
(t 2)n+1
(n+1)! |1
[x3 2 $(x)]$
_(x&1 2+(&1)n+1)(log x)n+1 dx=t=1
=4
j!
dj
dt j {t j&1 |1
[x3 2 $(x)]$ (x&1 2[e(t 2) ln x&1]+[e&(t 2) ln x&1])=t=1
=4
j!
dj
dt j {t j&1 |1
[x3 2 $(x)]$ (x&1 2e(t 2) ln x+e&(t 2) ln x)=t=1
=4 :
j
l=1 \j&1
j&l+ 1
l! |1
[x3 2 $(x)]$ \1
2 log x+l
[1+(&1)l x&1 2] dx.
This expression implies that aj is a positive real number for every positive integer j. Since the identity
:
n=1
nan zn&1=\ :
i=0
aizi+\ :
j=0
*j+1z j +
holds, we have the recurrence relation
*n=nan& :
n&1
j=1
*j an&j
for every positive integer n. By (1.1), *n is a real number for every positive integer n. If the nontrivial zeros of `(s) lie on the critical line, then |1&(1 \)| =1 for every nontrivial
THE RIEMANN HYPOTHESIS 327


 zero \ of `(s). Put 1&(1 \)=exp(i%\) for some real number %\ . Then by (1.4) we have
*n=:
\
( 1 & e in%\ ) = :
\
(1&cos n%\).
This implies that the number *n is nonnegative for every positive integer n. Conversely, if the number *n is nonnegative for every positive integer n, then
*n nan
for every positive integer n. It follows that
:
n=1
|*nzn&1 | :
n=1
nan |z| n&1=.$( |z| )<
for z in the unit disk. This implies that .$(z) .(z) is analytic in the unit disk. This completes the proof of the theorem.
2. THE DEDEKIND ZETA FUNCTION
Let k be an algebraic number field with r1 real places and r2 imaginary places. The Dedekind zeta function `k(s) of k is defined by
`k( s ) = `
p
( 1 & Np &s ) &1
for Re s>1, where the product is taken over all the finite prime divisors of k. Put G1(s)=?&s 2 1(s 2) and G2(s)=(2?)1&s 1(s). Define
Zk(s)=G1(s)r1 G2(s)r2 `k(s).
By Theorem 3 of Chapter VII, Section 6, of [4], the function Zk(s) is analytic in the complex plane except for simple poles at s=0 and s=1, and satisfies the functional identity
Zk(s)= |d| (1 2)&s Zk(1&s)
where d is the discriminant of k. Its residues at s=0 and s=1 are respectively &ck and |d| &1 2 ck with ck=2r1 (2?)r2 hR e, where h, R, and e are respectively the number of ideal classes of k, the regulator of k, and the number of roots of unity in k. Let !k(s)=c&1
k s(s&1) |d| s 2 Zk(s). Then !k(s) is an entire function and !k(0)=1.
328 XIAN-JIN LI


 Let [*n] be a sequence of numbers given by
(n&1)! *n= d n
dsn [sn&1 log !k(s)]s=1
for all positive integers n. The aim now is to prove the following theorem.
Theorem 2. A necessary and sufficient condition for the nontrivial zeros of the Dedekind zeta function `k(s) to lie on the critical line is that *n is nonnegative for every positive integer n.
3. PROOF OF THE THEOREM 2
Lemma 3.1. The identity
*n=:
\ \1&\1&1
\+n+
holds for every positive integer n, where summation is taken over all nontrivial zeros of the Dedekind zeta function `k(s) with \ and 1&\ being paired together.
Proof. By Theorem 2 of Barner [1], we have the formula (cf. Chapter 2 of [2])
!k( s ) = `
\ \1&s
\+ , (3.1)
where the product is taken over all zeros of !k(s) with \ and 1&\ being always paired together. An argument similar to that made for the Riemann zeta function in Chapter 2 of [2] shows that the convergence of the product (3.1) is uniform on compact subsets of the complex plane. Since !k(s)=!k(1&s), we have
dn
dsn [sn&1 log !k(s)]s=1=(&1)n d n
dsn [(1&s)n&1 log !k(s)]s=0 . (3.2)
Since `k(s) does not vanish at s=0, we can write
log !k(s)=&:
\
:
m=1
\&m
m sm (3.3)
where |s| <= for a sufficiently small positive number =, where \ and 1&\ are paired together in the summation over \. Since the product (3.1)
THE RIEMANN HYPOTHESIS 329


 converges uniformly, the series (3.3) converges uniformly for |s| <=. It follows that
1
(n&1)!
dn
dsn [(1&s)n&1 log !k(s)]s=0=&:
\
:
n
m=1
(&1)n&m \ n
m+ \&m.
This formula together with (3.2) implies the stated identity. K
Define
.(z)=!k \ 1
1&z+
for z in the unit disk. Since the function !k(s) is analytic in the complex plane of s, the function .(z) is analytic in the unit disk.
Lemma 3.2. Let
.(z)=1+ :
j=1
aj z j.
Then the coefficient aj is a positive real number for every positive integer j.
Proof. Define =v to be one when v is a real place of k and to be two when v is an imaginary place of k. Let x=> xv be the variable in the half space Rr1+r2
+ . Denote by |x| the product > x=vv , which is taken over all infinite places of k. If N=r1+2r2 , then the Hecke theta function 3k(x) is defined by
3 k( x ) = :
b
exp \&? |d| &1 N (Nb)2 N :
v
=vxv+
where the summation over b is taken over all nonzero integral ideals of k and where the summation over v is taken over all infinite places of k. Put dx=> dxv . It follows from Theorem 3 of Chapter XIII, Section 3, in [3] that
! k( s ) = 1 + c &1
k s(s&1) ||x| 1
3k(x)( |x| s 2+ |x| (1&s) 2) dx
x . (3.4)
Let
|
|x| 1
3k(x)( |x| 1 2(1&z)+ |x| 1 2 |x| &1 2(1&z)) dx
x= :
m=0
bm zm. (3.5)
330 XIAN-JIN LI


 It is clear that b0 is a positive number. We have
bm= :
n=0
(m+n) } } } (m+1)
n! (n+1)! 2n+1 ||x| 1
3k(x)(1+ |x| 1 2 (&1)n+1)(log |x| )n+1 dx
x
for every positive integer m. By computation, we find that
bm= 1
m! :
n=0
(n+m) } } } (n+1) (n+1)! 2n+1
_||x| 1
3k(x)(1+ |x| 1 2 (&1)n+1)(log |x| )n+1 dx
x
=1
m!
dm
dtm \tm&1 ||x| 1
3k(x)(e(t 2) log |x| + |x| 1 2 e&(t 2) log |x| ) dx
x +t=1
.
It follows that
bm= :
m
l=1 \m&1
m&l+ 1
l! ||x| 1
3k(x) \1
2 log |x|+l
( |x| 1 2+(&1)l ) dx
x (3.6)
for every positive integer m. Since 3k(x) is positive for every x in Rr1+r2
+, it follows from (3.6) that the coefficients bm are positive real numbers for all nonnegative integers m. The identity
z
(1&z)2= :
q=1
qzq
holds for z in the unit disk. It follows from (3.4) and (3.5) that
ckaj= :
j&1
m=0
( j&m) bm (3.7)
for every positive integer j. Since bm are positive numbers for all nonnegative integers m, we see that aj is a positive real number for every positive integer j. K
Proof of the Theorem. Since !k(1)=1 and !k(s)=!k(1&s), it follows from the product formula (3.1) that
.(z)=`
\
1&(1&(1 \))z
1&z . (3.8)
THE RIEMANN HYPOTHESIS 331


 Since !k(s) does not vanish at s=1, we can write
.$(z) .(z)= :
n=0
*n+1 zn (3.9)
by using the formula (3.8) when |z| <= for a sufficiently small positive number =. Since
:
n=1
nan zn&1=\ :
i=0
aizi+\ :
j=0
*j+1z j +,
we have
*n=nan& :
n&1
j=1
*j an&j (3.10)
for n=2, 3, ..., where *1=a1 and a0=1. If the nontrivial zeros of `k(s) lie on the critical line, it follows from Lemma 3.1 that the numbers *n are nonnegative for all positive integers n. Conversely, assume that the number *n is nonnegative for every positive integer n. It follows from (3.10) and Lemma 3.2 that
*n nan
for every positive integer n. This inequality together with Lemma 3.2 implies that
:
n=1
|*nzn&1 | :
n=1
nan |z| n&1=.$( |z| ) (3.11)
for z in the unit disk. Since .$(z) is analytic in the unit disk, .$(|z| ) is finite for z in the unit disk. It follows from (3.9) and (3.11) that .$(z) .(z) is analytic in the unit disk. It is clear that a necessary and sufficient condition for the nontrivial zeros of the Dedekind zeta function `k(s) to lie on the critical line is that .$(z) .(z) is analytic in the unit disk. Therefore, the nontrivial zeros of the Dedekind zeta function `k(s) lie on the critical line. This completes the proof of the theorem. K
Remark. We know from the proof of Theorem 2 that *1=a1 , which is a positive number by Lemma 3.2. An explicit expression for *n is implicit in the recurrence relation (3.10) together with formulas (3.6) and (3.7).
332 XIAN-JIN LI


 ACKNOWLEDGMENT
The author thanks the referee for valuable suggestions on improving the presentation of the original version of this paper.
REFERENCES
1. K. Barner, On A. Weil's explicit formula, J. Reine Angew. Math. 323 (1981), 139 152. 2. H. M. Edwards, ``Riemann's Zeta Function,'' Academic Press, New York, 1974. 3. S. Lang, ``Algebraic Number Theory,'' Addison Wesley, Reading, MA, 1970. 4. A. Weil, ``Basic Number Theory,'' Springer-Verlag, Heidelberg, 1967.
THE RIEMANN HYPOTHESIS 333