# Scalar source reserve: bounded own attempt and alias return

Previous turn: progress (source frame obstruction independently checked and pushed). Current bounded spectral-trimming attempt yielded only the existing Schur lower-sampling condition, with no arithmetic lower bound. It is STALLED as a supplier; the actual Schur/SP remains open. The following is one different source estimate to test, not an RH proof.

## Source-verified alias and consumer

Plain obstruction: positive sampling on the whole carrier is false; on actual E neither the lower bound nor its Schur correction is paid. Suzuki offers a scalar sign condition for the SAME full zeta source. It requires every sufficiently late prime-power interval, not a cofinal subsequence.
Primary source: Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, arXiv:2206.03682v4. Local `docs/routeB_bus/litreview/pdfs/2206.03682.pdf`, SHA256 eabccec3c2bfee2eb12077181b564e508270f80698f4a8c64ccf105b30119f41; https://arxiv.org/abs/2206.03682v4 . Root read equation1.1, §7.2 and Theorem11.1 in the local PDF; causal_algebra_audit independently checked the consumer.
Quote, Theorem11.1: “there exists t0 > 0 such that Ψω(t) is non-negative when t ≥ t0.”
The theorem states equivalence to xi(s) being zero-free for Re(s)>1/2+omega. At omega=0 functional equation gives RH. Its worked proof uses the Laplace transform -z^-2 xi'/xi(1/2-iz), nonnegative-function convergence-abscissa theorem, and absence of real zeros. No RH assumption enters the sufficient implication. This is an EXACT FIT conditional consumer, not positivity evidence. All poles, archimedean terms and prime powers are present in eq1.1.
Dictionaries: convex conjugate/stop-loss transform; weighted Chebyshev first moments; renewal reserve with downward prime-power derivative jumps. Three shelf queries returned ASK_STATUS INCOMPLETE. The source was already on shelf. UNVERIFIED search hints are aggregate jump compensation and convex-order domination, not imported theorems. Newer web checkpoint leads were not fetched and are excluded as evidence.
Negative control: an arbitrary positive atom of weight M at t0 changes Psi by -M(t-t0) for t>t0, and can defeat positivity while preserving smooth inter-event convexity. Arithmetic control of actual Lambda is essential; convexity alone is not a supplier.

## Exact cell minimum

For consecutive prime powers q<q_next define
A_q=sum_(n<=q) Lambda(n)/sqrt(n), D_q=sum_(n<=q) Lambda(n)log(n)/sqrt(n).
Let B(t) be the smooth part of Suzuki(1.1), so Psi(t)=B(t)-A_q t+D_q on the closed cell [logq,logq_next]; the endpoint added term is zero.
B''(t)=2cosh(t/2)-e^(-t/2)/(1-e^(-2t))>=5/(3sqrt2)>0 for t>=log2.
Thus there is exactly one clipped minimizer, solving B'(t)=A_q if interior. Psi is continuous at each event and its derivative jumps by -Lambda(q)/sqrt(q). The all-eventual minimum condition is sufficient for RH by Theorem11.1. A sparse good-cell condition is not.

## Closed elementary sufficient reserve

c=(digamma(1/4)-log pi)/2<0, b=pi²/4+2Catalan-8.
The n=0 Lerch term cancels exactly, giving
B(t)=4exp(t/2)+ct+b-R(t),
R(t)=(1/4)sum_(k>=1) exp(-(2k+1/2)t)/(k+1/4)^2,
0<R(t)<=4 exp(-5t/2)/[25(1-exp(-2t))].
Set y_q=A_q-c>0 and
E_q=D_q-2y_q(log(y_q/2)-1)+b, d_q=4/[25q^(5/2)(1-q^-2)].
Minimizing the elementary smooth part over ALL real t gives
Psi(t)>=E_q-d_q throughout the q cell.
Hence E_q>=d_q for EVERY sufficiently large prime power q would imply RH, and therefore the original full Weil positivity. This is stronger than the clipped exact-cell minimum and is presently OPEN. No matrix error estimate is being discarded: this is an alternative sufficient scalar source lemma for the terminal consumer.

At q=p^k let a=log p/sqrtq, y=A_previous-c. The exact reserve increment is
Delta E = a[logq-2log(y/2)] - 2[(y+a)log(1+a/y)-a].
The last bracket h satisfies h(0)=h'(0)=0, h''(a)=1/(y+a), so 0<=2h<=a²/y. This pays only the convexity loss. The first term is signed and its arithmetic aggregate is NOT bounded here. Treating it as nonnegative would be an extra unproved weighted Chebyshev inequality.

## Summable convexity loss: explicit unconditional tail

Write ell_q=2[(y+a)log(1+a/y)-a]. For every event q=p^k,
y>=-c>2 and a<=log(q)/sqrt(q)<1. Thus x=a/y<1, and
0<=ell_q<=a²/y<=2a log(1+a/y), using log(1+x)>=x/(1+x)>=x/2.
For X>=4, on the event block X<q<=2X we have a<=log(2X)/sqrt(X).
The logarithms telescope to log(y_end/y_start). Summing over all integers gives
y_end<=3+2sqrt(2X)log(2X)<=4sqrt(X)log(2X), whereas y_start>=2.
Consequently log(y_end/y_start)<=2log(2X), and
sum_(X<q<=2X) ell_q <=4log²(2X)/sqrt(X).
Applying this to X=2^j Q, Q>=4, yields the explicit tail
sum_(q>Q) ell_q <300log²(2Q)/sqrt(Q),
because log(2^(j+1)Q)<=(j+1)log(2Q) and
4sum_(j>=0)(j+1)² 2^(-j/2)<300.
The blocks exclude q=Q and include their upper endpoints; every q>Q is counted once.
This proves convergence of the entire nonnegative loss without PNT or zero assumptions.
The signed drift sum a[logq-2log(y/2)] is still uncontrolled: this is not a lower
bound for E_q and does not close RH. Root derivation independently checked once by
causal_algebra_audit: PASS, including telescoping, constants and boundary convention.

## Exact global minima versus the sufficient proxy

Let P(t)=sum_n a_n(t-log n)_+ and L_q(t)=A_q t-D_q, t>=0.
Term by term P(t)>=L_q(t): retained positive parts dominate the affine terms,
and omitted terms are nonnegative. Thus H_q(t)=B(t)-L_q(t)>=Psi(t) globally,
with equality on the closed q-cell. Include the empty q=1 cell for [0,log2].
Suzuki Theorem1.7, read in the same primary PDF, states RH iff Psi is nonnegative
everywhere. Hence RH implies inf_(t>=0) H_q(t)>=0 for EVERY q, and the reverse
implication follows by restricting to the cells. Even the all-eventual version
of these exact global-minimum conditions implies eventual Psi>=0 and hence RH
by Theorem11.1. Global minimization itself is therefore not an excessive condition.
For t*_q=2log(y_q/2)>0, H_q(t*_q)=E_q-R(t*_q), so RH necessarily implies
E_q>=R(t*_q)>0. The original sufficient proxy E_q>=d_q still has additional
slack: d_q can exceed R(t*_q). No unconditional reserve sign follows here.
This distinction prevents rejecting the exact route merely because the proxy
fails; it supplies no missing arithmetic estimate. Root proof independently
checked by causal_algebra_audit: PASS, including the empty cell and endpoints.

## Quantitative removal of excess cell-minimum slack

For q>=2 put I=[logq,logq_next], t*=2log(y_q/2), x=clip_I(t*), h=x-t*.
The explicit value at the clipped elementary minimizer is
V_q=E_q+2y_q[exp(h/2)-1-h/2]-R(x)=Psi(x).
Both the positive clipping correction and the exact archimedean remainder are retained.
On I, H=Psi has
H''(t)=exp(t/2)-exp(-5t/2)/(1-exp(-2t)) >= (5/6)sqrt(q)=mu,
since exp(-3t)/(1-exp(-2t))<=1/[q(q²-1)]<=1/6.
For F0=B0-A_q t+D_q, g0=F0'(x) satisfies g0(t-x)>=0 on I.
Uniform convergence on I permits differentiating R, giving
r=-R'(x)=(1/2)sum_(k>=1)exp(-(2k+1/2)x)/(k+1/4)
 <=(2/5)q^(-5/2)/(1-q^-2).
Strong convexity now gives H(t)>=V_q+(g0+r)(t-x)+mu(t-x)²/2
>=V_q-r²/(2mu). Therefore the completely explicit sandwich is
V_q-epsilon_q <= min_I Psi <= V_q,
epsilon_q=12/[125 q^(11/2)(1-q^-2)²].
If x is the left endpoint, H'(x)=g0+r>0, so min_I Psi=V_q exactly.
Thus V_q>=epsilon_q on every late cell is sufficient, while any negative V_q
exhibits a genuinely negative Psi value. This narrows the approximation error;
it does NOT estimate the arithmetic sign of V_q or close the reserve problem.
Root derivation independently checked by causal_algebra_audit: PASS, including
constants, clipping, derivative signs, and closed-cell endpoints.

## Verification and decision

causal_algebra_audit independently checked B'', endpoints, all-eventual consumer, Lerch cancellation, reserve and increment. Root supplied the integral proof for the sharper total loss <=a²/y. Both independently ran a floating diagnostic through q<=100000 (9700 events): min E approximately .02752057365 at q=3089. This is not an interval certificate, does not include a tail proof and is not used to claim any positivity theorem.
One next bounded question to Pro: estimate the signed arithmetic reserve drift, using actual primes and powers, enough for an eventual E_q>=d_q, or exhibit the precise source obstruction to this sufficient mechanism. Do not replace it with finite data, unsigned PNT errors or the exact scalar criterion itself. Original G1/G3/SP/RH remain OPEN.
