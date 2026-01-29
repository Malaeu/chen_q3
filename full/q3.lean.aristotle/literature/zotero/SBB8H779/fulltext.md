---
title: "The pair correlation of zeros of the zeta function"
authors:
  - "Hugh L. Montgomery"
date: "1973-00-00 1973"
publication: null
doi: null
url: "https://public.websites.umich.edu/~hlm/paircor1.pdf"
zotero:
  attachment_key: "WSLDM3MR"
  parent_key: "SBB8H779"
  item_id: 1953
  attachment_item_id: 1982
---

THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION
H. L. MONTGOMERY
I. Statement of results. We assume the Riemann Hypothesis (RH) through out this paper; e=!+iy denotes a nontrivial zero of the Riemann zeta function. Our object is to investigate the distribution of the differences y - y' between the zeros. It would thus be desirable to know the Fourier transform ofthe distribution function of the numbers y - y'; with this in mind we take
T )-1 T il1
(1) F(o:)=F(o:, T)= ( 2~ log T L (Y-Y') w(y-y'),
" O<y~T;O<y'~T
where 0: and T~2 are real. Here w(u) is a suitable weighting function, w(u)=4j(4+u2 ), so w(O)= 1. Our results concerning F(o:) are stated in the fol lowing
THEOREM. (Assume RH.) For real 0:, T~2, let F(o:) be defined by (1). Then
F(o:) is real, and F(o:) = F( - 0:). If T> To (.s) then F(o:) ~ -.s for all 0:. For fixed 0: satisfying 0 ~ 0: < I we have
(2) F(o:)=(1 +0(1)) T- 211 10g T +0:+0(1)
as T tends to infinity .. this holds uniformly for 0 ~ 0: ~ 1- e.
The first term on the right-hand side of the above behaves in the limit as a Dirac b-function; it reflects the fact that if 0: = 0 then all the terms in (1) are positive. With more effort we could show that (2) holds uniformly throughout 0 ~ 0: ~ 1. To investigate sums involving y-y' we have only to convolve F(o:) with an
AMS 1970 subject classifications. Primary IOH05.
© 1973, American Matbematical Society
181


 182 H. L. MONTGOMERY
appropriate kernel ?(a); from (1) alone it is immediate that
+00
gT
(3) L r((y-yl) 102 ) W(y-yl)=(~ 10gT) f F(a) ?(a) da.
0< Y~ T; 0 < y' ~ T n 2n
-00
Here? is the Fourier transform of r,
+00
(4) ?(a)= f r(u) e( -au) du
-00
Our ~heoremgives us little information about F(a) for a ~ I, so for the most part we restrIct our attention to kernels? which vanish outside [ -1 +6, 1-6]. Particular choices of ?(a) give us
COROLLARY 1. (Assume RH.) IjO<a< I isfixed then
'\' (sina(y - y') log T) ( , (I a) T
(5) L, W y-y) '" -+- -logT
O<y~T;O<y'~T a(y-y') 10gT 2a 2 2n '
and
'\' (sin (aI2) (y_y') IOgT)2 ( , (1 a) T
(6) L, W y-y) '" -+- -logT
O<y~T;O<y'~T (aI2) (y-y') 10gT a 3 2n .
In the latter assertion one can delete the factor w(y - y') if one wishes. We use
(6) to derive
COROLLARY 2. (Assume RH.) As T tends to infinity
T
(7) o<y~tesimPle 1~(~+O(I)~ log T.
The number of zeros of ((s) with O<y~T is ",(TI2n) 10gT, so the above asserts that at least ~ of the zeros are simple. It is known (see [6J) that the first 3,500,000 zeros are simple and lie on the critical line (j=~. Although one expects that all the zeros of ((s) are simple, the only other result in this direction is due to A. Selberg [7]. His result holds unconditionally; it states that a positive density of the zeros of ((s) are of odd order and lie 0 n the critical line. Let 0 < Y1 ~ yz ~ ... denote the imaginary parts of the zeros of S(s) in the upper


 THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION 183
half-plane. The average of Yn+ 1 - Yn is 2n/logYn; our Theorem enables us to show that Yn +1 - Yn is not always near its average.
COROLLARY 3. (Assume RH.) We can compute a constant A so that
(8) lim)nf(Yn+l -Yn) (logYnI2n)~il<1.
A complicated argument would permit one to show that in fact Yn +1 - Yn ~ 2n.?c/logYn for a positive density of n. This, with the fact that the average value is 2n/logYn' enables one to assert that
(9) lim sup (Yn +1 - Yn) (logYn/2n) ~).' > I.
n
We note that if ((s) has infinitely many multiple zeros then we may take A=O
in (8). Our proof allows us to take .?c = 0.68. It would be of interest to have .?c < t, as P. J. Weinberger and I have established the following: Let d>O be square-free, and put K=Q(( _d)1/2). Let h( -d) be the class number of K, and let (K(S)=((S) . L(s, X) be the Dedekind zeta function of K. For each positive A, 8 there is an effec tively computable constant do=do(A, 8) such that if h( -d)~A, d>do, then all
zeros of (K(S) which are in the rectangle 0<0'< 1, 0~t~d1/2-. lie on the line
a =1; if 1+ iYn, 1+ iYn+ 1 are consecutive zeros of (K(S) in this range then
2n 2n
(10) (1- 8) log d(Yn + 2)2 ~Yn+ 1- Yn ~(1 + 8) ~lo-g-d-(Y-n-+-2)""""2 .
One may inquire about the behaviour of F(ex) for ex ~ 1. Our first observation is that (2) cannot hold uniformly for O~ex~C if C is large. For if it did then (6)
would hold for O<ex~C. Write (6) as G(ex)~H(ex). On one hand Isin2xl~2Isinxl,
so G(2ex)~G(ex) for all ex. On the other hand H(2ex»iH(ex) for ex~2. This suggests that F(ex) makes some change in its behaviour for a~ 1. Further considerations of the above sort lead one to believe that certain averages of F(a) over large a are close to 1. At the end of §3 we describe two heuristic arguments which suggest that
(11 ) F(a)= 1+0(1)
for ex ~ 1, uniformly in bounded intervals. This, with the Theorem, completely determines F, so an appropriate use of (3) leads immediately to a
CONJECTURE. For fixed a < /3,


 184 H. L. MONTGOMERY
fJ
(Sin nU)2 ) T
(12) I 1 ~ (I 1- ----;;;- du+(j(a,f3) 2n logT
O<y~ T
O<y'';T a
2ltajlog T ~ y - 7 ~ 2ltfJjlog T
as T tends to infinity. Here (j(a, f3)= 1 ifOE[O:, f3J, (j(o:, f3)=O otherwise.
The Dirac (j-function occurs naturally in the above, for if OE [0:, f3J then the
sum includes terms y = 1". The assertions (II) and (12) are essentially equivalent. From either it immediately follows that almost all zeros are simple. From (11) it is easy to see how Corollary 1 ought to be extended: If (11) is true then for 0:;;:; I,
,,(sinO:(Y-y')IOgT) T
(13) 1... w(y-y')~-logT
O<y~T;O<y'~T o:(y-y')logT 2 n '
and
" (sin (0:/2) (y-y') IOgT)2 ( 1 ) T
(14) 1... w(y-y')~ 1 + - -logT
O<y~T;O<y'H (a/2) (y-y') 10gT 3a 2 2n .
In a certain standard terminology the Conjecture may be formulated as the assertion that l-((sin nu)/nu)2 is the pair correlation function of the zeros of the zeta function. F. 1. Dyson has drawn my attention to the fact that the eigenvalues of a random complex Hermitian or unitary matrix of large order have precisely the same pair correlation function (see [3, equations (6.13), (9.61)J). This means that the Conjecture fits well with the view that there is a linear operator (not yet discovered) whose eigenvalues characterize the zeros of the zeta function. The eigenvalues of a random real symmetric matrix of large order have a different pair correlation, and the eigenvalues of a random symplectic matrix of large order have yet another pair correlation. In fact the "form factors" Fr(a), Fs(O:) of these latter pair correlations are nonlinear for 0 < a < 1, so our Theorem enables us to distinguish the behaviour of the zeros of' (s) from the eigenvalues of such matrices. Hence, if there is a linear operator whose eigenvalues characterize the zeros of the zeta function, we might expect that it is complex Hermitian or unitary. One might extend the present work to investigate the k-tuple correlation of the zeros of the zeta function. If the analogy with random complex Hermitian matrices appears to continue, then one might conjecture that the k-tuple correla tion function F(u 1 , U2, ..., Uk) is given by
(15)


 THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION 185
where A = [aiJ is the k x k matrix with entries aii = 1, ajj = (sin n(uj - uJ)/n(uj - uJ
for i i=j. Here the normalization is the same as in the Conjecture, which is the case k = 2 of the above. If one continues to draw on the analogy with random complex Hermitian matrices then one may formulate a conjecture concerning the distribution of the numbers Yn+ 1 -Yn' The precise conjecture involves a complicated (but calculable) spheroidal function. Thus, or otherwise, one may conjecture that
(16) lim inf(Yn+ 1 -Yn) 10gYn=O,
n
and
(17) lim sUP(Yn+l-Yn) 10gYn= +co;
n
so Corollary 3 is probably far from the truth. It would be interesting to see how numerical evidence compares with the above conjectures. The first several thousand zeros have been computed, so it would not be difficult to assemble relevant statistics. However, data on the failures of "Gram's law" indicate that the asymptotic behaviour is approached very slowly. Thus the numerical evidence may not be particularly illuminating.
2. An explicit formula. In proving our Theorem we require the following formula, which relates zeros of ((s) to prime numbers.
LEMMA. If 1< (J <2 and x ~ 1 then
where 't = Itl + 2. The implicit constants depend only on (J.
PROOF. It is well known (see [2, p. 353]) that if x> 1, xi=~, then
(' x1-s xe-s CX) x-2n-s
L A(n) n- S = ---; (s)+-- L - + L 
n;;; x i, 1- s e (} - S n = 1 2n + S
provided s i= 1, s i= (}, s i= - 2n. This does not depend on RH, but if we assume RH then the above may be expressed as


 186 H. L. MONTGOMERY
(19)
If we replace s by 1- a +it in the above then we have
X1/2 _" (-"(I-a+it)+ L A(n)n,,-I-i'
, n~x
(20) X,,-it C() x-2n-I+,,-il)
- a-it- n~1 2n+ l-a+it .
We subtract respective sides of(20) from (19), and use the relation
(21)
which holds for a> 1. We find that
x iy
_X- 1/2 ( L A(n) (~)I-"+i' + L A(n) (~)"+il)
(2a - 1) ~ -(a---t=-)2=-+-t(-_-y--=-)2 n~x n n>..:c n
I/2
" ' x (2a-l)
(22) -- (1- a + it) X l/2 -,,+It + -:------'------'-
, (a - I + it)(a - it)
2n
-1/2 ~ (2a-l) x
-x L.
n= I (a-l- it-2n) (a+ it + 2n)'
Both sides of the above are continuous for all x ~ 1, so we no longer exclude the values x = 1, x = pn. If 1< a < 2, then from the logarithmic derivative of the func tional equation of the zeta function (see [1, pp. 75, 82-83J) we have
(~',1- a + it) = --,"(a - it) -log! + 0,,(1) ;
from (21) we see that this is = -log! + 0 <J (1). Hence the right-hand side of (22) is
X)I-"+i' (X)"+i')
= _X- 1/2 I A(n) - + I A(n)
((
n~x n n>X n
which gives the result.


 THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION 187
3. Proof of the Theorem. The first assertion of the Theorem follows from the observation that we may interchange y and yf in (1). To prove the remaining
assertions, take (J =t in the Lemma, and write (18) briefly as L(x, t)= R (x, t). We
evaluate the integrals g\L(x, tW dt, S6"IR(x, tW dt. I We treat the left-hand side first. We have
IT T
1(23) 2 " ' ( ' ) J dt
L x t dt -4 L. Xl y-y
J
I ( ,)1 - y, y' {1 +(t_y)2) (1 +(t_ yf)2)"
o0
We wish to exclude those numbers ')11[0, T]. It suffices to show that
" JT
(24) L. 2 dt 2 «log 3 T,
y,y';Y¢[O, T] (I +(t-y) ) (1 +(t-y') )
o
for then (23) is
T
(25) =4 L xi(Y-i) J 2 dt 2 +0 (log3 T).
O<y;'iT;O<y'~T (1 +(t-y) ) (1 +(t-y') )
o
To prove (24) we use the fact (Theorem 9.2 of [8]) that if T ~ 2 then there are
«log Tzeros for which T ~y ~ T + 1. From this it is immediate that ifO~ t ~ Tthen
1 ( 1 1)
I: 2« - + 10gT,
y;y¢[O,TJ l+(t-y) t+l T-t+l
and
L 1 2«]ogT.
i 1+(t- yf)
On the left-hand side of (24) we take the sums inside and use the above estimates, I he integration is then trivial, and we obtain (24). Arguing similarly we may also show that


 188 H. L. MONTGOMERY
The estimation of Lo < y~ T; 0 < y' ~ T Je: 00 ••• is the same, so we see that (25) is
From the calculus of residues we deduce that the definite integral is = (nI2) w (y - y'), so the above is
=2n L xi(y-y')w(y-y')+o (log3 T).
o < y ~ T; 0 < y' ~ T
If we put x = T" then we have
T
(26) fIL(T", tWdt =F(et) TlogT +0 (log3 T).
o
Here the left-hand side is clearly nonnegative, so we have the second assertion of the Theorem. To complete the proof of the Theorem we prove (2); to this end we evaluate
g IR(x, tW dt. In the first place
T
(27) f1x - 1 +it log,1 2 dt = ~ (log2 T +O(log T))
o
for all x ~ 1, T ~ 2. To compute the mean square of the Dirichlet series on the right-hand side of(18) we use the following quantitative form (see [5J) of Parseval's identity for Dirichlet series:
T
2
(28) JI~ ann-if dt = ~ lanI (T+0(n)).
o
We could instead use the weaker relation
T
fln~N ann-if dt =(T +O(N)) n~N la ln2
;
o


 THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION 189
this is Theorem 1.6 of [4]. However, the latter is restricted to Dirichlet polynomials, so we simplify our treatment by arguing from (28). We have
T
1 II (X)-1/2+il (X)3 /2+il/2
~ n~x A(n) ~ + nE A(n) ~ dt o
1 (x) -1 l (x) 3
=~ n~ .1 (n)2 ~ (T+O(n))+~ n~ A(n)2 ~ (T+O(n)).
By the prime number theorem with error term this is
(29) =T(logx+O(1))+O(x logx).
As for the error terms in (18), we see that
(30)
and
T
2
(31 ) IXT- dt ~x.
o
We now combine our estimates (27), (29), (30), (31); we employ the following consequence of the Cauchy-Schwarz inequality: If M k= fb"IAk(tW dt and M 1 ?;. M 2 ?;. M 3?;. M4' then
T
Ilktl Adtf dt =M1 +O((M1M2)1/2).
o
We consider three cases.
Case 1. 1~ x ~ (log T)3 /4. Then our M 1 term is given by (27). Our other terms
are uniformly 0(M1), so our expression is =(1 +0(1)) (T/x 2) log2 T. Case 2. (logT)3/4<X~(logT)3/2. In this case all our estimates are uniformly o(Tlog T).
Case 3. (1ogT)3/2<x~T/logT. Then our M 1 term is given by (29). All our


 190 H. L. MONTGOMERY
other terms are uniformly 0(M1), so our expression is =(1 +0(1)) Tlogx. If we put x = T" then we may express our result by saying that
T
IIR(T", tW dt =((1 + 0(1)) T- 2" log T +a +0(1)) Tlog T,
o
uniformly for O~ex ~ I-t:. This and (26) give (2), so the proof is complete. If ex> 1 in the above then x> T, so the second error term in (29) is no longer smaller than the main term. The error term (31) also gives problems; a little con sideration reveals that what we require is to know the size of
T
2 ir 2
. 2 . 2X 1/ - 1
1 2 tl
(32) - L A(n) n / - 11 +x L A(n) n- 3/ - _ l . 3 . " dt.
x n~x n>x (z+tt) b--tt)
II I
o
If we multiply out the integrand and integrate terms individually, we find that there are too many nondiagonal terms to be ignored. We may, however, collect
terms so that the above is expressed in terms of sums ofthe sort Ln~y A(n) A(n + h). There are various indications that this sum is approximately c(h) y, where c(h) is a certain arithmetic constant. If we replace these sums by their conjectured approximations c(h) y, then our new expression is ~ T log T. Moreover, there is a reasonable hypothesis as to the size of the differences
(33) L A(n)A(n+h)-c(h)y
n~y
which iftrue would allow us to carry out our program for 1~ ex < 2. If the differences (33) are not only reasonably small but also behave independently for different h then (32) is ~ T log T for all ex ~ 1. Another indication of the behaviour of the expression (32) can be obtained by considering its "q-analogue." The expression
2 2
(34) L - 1 L 1-1 L A(n)x(n)n1/2 + L A(n)x(n)n- 3/ 1
q~Q q>(q) 1."'1.0 X n~x n>x
may be shown to be ~ Q log x for Q ~ x, in analogy with (29). If x (log x) - A ~ Q ~ x then we may use an established technique [4, Chapter 17J to show that (34) is ~Q logQ. If GRH is true then this latter asymptotic relationship hol~s for
X3 /4 +t <Q;£ x. This corresponds to 1;£ a<t. One does not expect a change III the


 THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION 191
behaviour ror larger a, but a more delicate error-term analysis is needed irthe result is to be extended.
4. The corolJaries. To prove Corollary I we use our Theorem in conjunction with (3). To obtain (5) we take r(u)=(sin2nau)/2nau. The Theorem makes it a simple task to compute
+00 a
f
F(f3)r (13) df3 = 2~ f F(13) df3 .
-00 -a
To obtain (6) we take r(u) = ((sin nau)/nau)2. Again from the Theorem it is easy to compute
+00 +a
f
1~
F(f3)r(f3) df3 = a2 J (a - f3) F(f3) df3.
-a
-00
We now prove Corollary 2. Let mg be the multiplicity of the zero Q. In a sum
over 0 < y ~ T, our convention concerning multiple zeros is that zeros are counted according to their multiplicities. This is accomplished by allowing y to take on the same value mg times. In particular,
L mg = L
O<y;iiT O<y;iiT O<y';iiT y=y'
ror on both sides a given zero Q is counted with weight m~. But
" ,,(sin(a/2)(y-y')IOgT)2 ( ')
1..- 1~ 1..- , w y-y ,
O<y;iiT O<y;iiT;O<y';iiT (aI2) (y-y) 10gT
O<y';iiT y=y'
and ir we take a = 1- () then from (6) the above is
~(1+£) (T/2n) log T.
Hence we have demonstrated that
L me~(1+o(1)) (T/2n) logT.
O<y;iiT


 192 H.L.MONTGOMERY
Now
L 1 ~ L (2-me)~(2-!+o(1))I.-logT,
0< y;§ T; esimple 0 < y;§ T 2n
so we have Corollary 2. The kernel r(u) which we have used does not appear to be optimal for our purpose, so presumably one can improve slightly on the con
stant l We now turn to the first assertion of Corollary 3. We take r(u)= max(l-(luI/A),O) in (3), and choose A later. Now r(er:) is nonnegative, and SO' r{er:) der:< 00, so our Theorem permits us to calculate a lower bound for the right-hand side of (3). We see that
+~ 1
f
F(er:)r(er:)der:~(1+0(1))(A+2A fer:ei:;:er:)der:)~lOgT.
-00 0
We may assume that all but finitely many zeros are simple, so the terms y = v' in (3) contribute an amount ~(Tj2n) log T. Hence
T
L 1~(!+o(l))C(A)2nlogT
o <y;;; T O<y';§T 0< Y- y' < 2"A/log T
where
C(A)=A+(ljn2 A) Cin(2nA)-I.
Here Cin (x) is the "cosine integral,"
f
x
l-COSU
Cinx= u duo
o
Note that the integrand is nonnegative, so that Cin(x»O for x>O. To obtain
(8) we show that C(A»O for some A< 1. This is easy, because C(1)=(ljn2
)
. Cin(2n)> 0, and C(A) is continuous. In fact a little calculation reveals that C(0.68) >0. We have not determined the optimal kernel r(er:), so one should be able to
improve on the constant 0.68.


 193
THE PAIR CORRELATION OF ZEROS OF THE ZETA FUNCTION
REFERENCES
I. H. Davenport, Multiplicative number theory, Lectures in Advanced Math., no. I, Markham, Chicago, 111.,1967 MR 36 # 117.
2. Edmund Landau, Handbuch der Lehre von der Verteilung der Primzahlen, Teubner, Berlin, \909. 3. M. L. Mehta. Random matrices and the statistical theorv or energv levels, Academic Press, New York, 1967. MR 36 # 3554. 4. Hugh L. Montgomery, Topics in multiplicative number theory, Lecture Notes in Math.• vol. 227, Springer- Verlag, Berlin and New York, 197 L. 5. Hugh L. Montgomery and R. C. Vaughan, Hilbert's inequality (to appear). 6. J. B. Rosser, J. M. Yohe and L. Schoenfeld, Rigorous computation and the zeros of" the Riemann zeta~fimction (with discussion), Information Processing 68 (Proc. IFIP Congress, Edinburgh, (968), vol. I. Math., Software. North-Holland. Amsterdam. 1969, pp. 70-76. MR 41 #2892. 7. Atle Selberg, On the zeros o{ Riemann's zeta-function. Skr. Norske Vid. Akad. Oslo I (1942), no. 10.59 pp. M R 6, 58 8. E. C. Titchmarsh, The theory of the Riemann zeta~function, Clarendon Press. Oxford, 1951. MR 13, 74L.
TRINITY COLLEGE
CAMBRIDGE, ENGLAND