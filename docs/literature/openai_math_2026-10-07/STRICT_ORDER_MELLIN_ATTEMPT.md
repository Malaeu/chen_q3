# Strict-order Mellin attempt after Direct Shift Q1

Own bounded calculation; independent squarefree_conductor_check audit PASS for Gaussian Perron, absolute convergence, half-diagonal, deterministic subtractions and pole normalizations. Target is Q1's actual Cprefix, including strict n<r and BOTH deterministic subtractions. This tests its second proposed representation; no new question has been sent.

Let b=13/16,a=3/16 and F(z)=-zeta'/zeta(z), initially Re z>1. For Re s>a define the absolutely convergent ordered Dirichlet series
D_b(s)=sum_(r>=2)Lambda(r)r^(-s-1) sum_(2<=n<r)Lambda(n)n^-b.
Fix a<c<Re s. Gaussian regularization gives exactly
D_b(s)=lim_(epsilon↓0) [1/(2pi i) int_(Re w=c)
 exp(epsilon w²)F(b+w)F(s+1-w)dw/w]
 -(1/2)sum_r Lambda(r)²r^(-s-1-b).
The last term subtracts the half-diagonal. It cannot be omitted or confused with the later quadratic-energy diagonal.

Proof of the limit: H_epsilon(x)=(1/(2pi i))int_(c)exp(epsilon w²)x^w dw/w is the Gaussian distribution function at log(x)/sqrt(2epsilon). Its derivative with respect to logx is exp(-log²x/(4epsilon))/sqrt(4pi epsilon), and its limit at x->0 is0. Thus H tends to1,1/2,0 for x>1,x=1,x<1. Moreover0<=H<=1 and H<=exp(epsilon c²)x^c. For epsilon<=1 the latter dominates the entire double series by an absolutely summable product, since b+c>1 and Re s+1-c>1. Finite-epsilon exchanges are absolutely justified by the Gaussian decay on the vertical line. No unsmoothed endpoint convention is hidden.

Let Cprefix(X)=sum_(r<=X)Lambda(r)/r[A_eta(r-)-c_eta-r^a/a], with the actual full prefix. Stieltjes integration, initially Re s>a, gives
int_1^infinity Cprefix(X)X^(-s-1)dX
 =[D_b(s)-c_eta F(s+1)-(1/a)F(s+b)]/s.
This is an exact arithmetic map, not a new signed estimate.

## What a contour shift must retain

The first factor has its principal pole at w=a, residue+1, so a valid left shift contributes exp(epsilon a²)F(s+b)/a. Only after epsilon->0 does this match the explicit continuous-main subtraction. The second factor has a MOVING principal pole w=s, residue -F(b+s); after division by w its contribution is -exp(epsilon s²)F(b+s)/s. Continuing s through the new contour cannot ignore this pole. First-factor zero poles w=rho-b likewise cannot be silently crossed; their absence below the imported boundary would be precisely new information. Gaussian control at fixed epsilon is not permission for an uncontrolled epsilon->0 contour interchange.

Therefore the strict-order Perron representation by itself supplies neither a new positivity relation nor the missing all-eventual upper bound. The previously audited actual-source residue in Q1 remains a discriminator against omitted pole cancellation. No claim is made that the ordered-pair route is impossible: it still needs a NEW estimate or source identity on this exact product/contour.

Source/alias return: local shelf query strict ordered prime prefix Perron half diagonal Mellin is incomplete on semantic freshness; not absence. This derivation uses the elementary Gaussian integral and exact Dirichlet series in their absolute half-planes. It does not import a conjectural shifted-correlation theorem. The generic positive-source dual proposal has separately failed in POSITIVE_SOURCE_DUAL_CONTROL.md. Both Q1 suggestions have now received a bounded own test; neither currently supplies signed descent.

Decision: strict-order representation alone STALLED as a sign supplier. Together with POSITIVE_SOURCE_DUAL_CONTROL this completes the two bounded tests suggested by Q1 without a new arithmetic constraint. Defer this direct scalar descent phase; Q2 not sent. Next selected bounded receiver is the original full CCM negative-moment compensation proposed in linux_needle_scan/REPORT.md. It must retain N=m, old-entry motion and new-mode coupling; the moment criterion alone is not progress in SP.
