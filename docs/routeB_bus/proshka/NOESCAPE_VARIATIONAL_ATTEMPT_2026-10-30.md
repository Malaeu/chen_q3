# Variational NOESCAPE attempt: modulus, signed binding, and carrier return

Status: BOUNDED PAPER OWN ATTEMPT, independently reviewed; no material findings. T and RH remain OPEN.
This follows processing ENTROPY and the exact finite F/X status. The family
is still literal m=N, L=logm, even normalized bottoms of A_m. No new carrier
or prime cutoff is substituted. Goal: under fixed-jet escape, produce a
strictly better competitor in the same carrier, or identify a genuine source
estimate that is missing.

## 1. Why stationarity and almost-zero trials do not suffice

Let f be an exact unit bottom with energy lambda. For any w in its carrier
orthogonal to f,

    k[(f+t w)/||f+t w||] - lambda
      = |t|² (k[w]-lambda||w||²)/(1+|t|²||w||²).

All first-order mixed terms vanish by the exact eigenrelation. Small jet
pairing and a jet trial energy tending to zero give no sign to the numerator.
A proof by contradiction must obtain a strict source improvement beyond
these facts. Merely assuming that an escaping bottom admits a lower-energy
competitor would restate the desired contradiction.

## 2. A specific source transformation and its complete gain

Extend f by zero outside I=[-L/2,L/2], allow complex even f, and put u=|f|.
It is even, has the SAME physical support, and ||u||=||f||=1. It is not
in general in the finite Fourier carrier. Define

    d_f(s)=integral_R (|f(x)||f(x+s)|
                         -Re(conj(f(x))f(x+s))) dx >=0,
    A(f)=2 integral_0^L j(s)d_f(s) ds,
    P(f)=2 sum_{2<=n<=m} Lambda(n)/sqrt(n) d_f(log n),
    H(f)=|<p,u>|²-|<p,f>|² >=0,
    G(f)=A(f)+P(f)-H(f),
    p=sqrt(2)cosh(x/2), j(s)=exp(-s/2)/(1-exp(-2s)).

Then, exactly in the ORIGINAL form,

    k[u]-k[f] = -G(f).                                      (V1)

Proof: diagonal terms cancel by equal norms. Correlation differences are
2d_f(s), giving the displayed arch and prime terms with their exact signs.
All prime powers through m are included. Higher prime powers vanish only
because BOTH functions have this same physical support. The arch tail s>L
also cancels by equal norms; it has not been discarded from the source.
Both odd pole pairings vanish by evenness; the positive even pole gives H.
Triangle inequality proves H>=0, so it is a cost, not a gain.

All forms here are finite: finite trigonometric f and its modulus have
bounded variation on I; zero extension introduces only finite endpoint
jumps. Their translation-square differences are O(s) near zero, integrable
against j(s)~1/(2s). The same holds for their finite projections/differences.
Thus the following polarization does not assume an undefined form value.

## 3. Exact return to the ORIGINAL Fourier carrier

Let P_m be its orthogonal projection, e=u-P_m u, and d=||e||². The constant
mode pairs positively with u, so d<1. The explicit admissible candidate is

    g=P_m|f|/sqrt(1-d).

No larger cell or frequency cutoff is used. Polarization and normalization
give the exact identity

    k[g]-lambda = [-G(f)+R(f)]/(1-d),                       (V2)
    R(f)=-2 Re k(u,e)+k[e]+lambda d.

Every k(u,e) and k[e] is the full original form, including its diagonal,
arch tail, all supported prime powers, and poles. The mixed term is essential.
A separately bounded, stronger sufficient certificate is

    A(f)+P(f) > H(f) + E(f),                               (V3)
    E(f)=2|k(u,e)|+|k[e]|+|lambda| d.

(V3) proves strict improvement via (V2). This is the concrete additional
property that would make this transformation useful: jump sign/phase repair
must dominate BOTH the pole increase and the measured cost of Fourier return.
No assertion that (V3) holds for escaping bottoms has been obtained.

Writing G>R alone would merely rename descent. A genuine supplier must
instead prove lower bounds for A+P and upper bounds for H and E from source
structure on the relevant low-energy class, with a positive remaining margin.
For example A+P>=eta_m>0 and H+E<eta_m would suffice on one large cell under
the escape hypothesis. The margin may depend on m; its sign must be proved,
not inferred from a finite sample. No norm-only residual estimate pays E.

## 4. Universal modulus contraction is FALSE for this source

Choose nonzero nonnegative smooth even a supported in [-eps,eps] and smooth
nonnegative even b supported near +/-R, with

    eps=1/100, R=log(13/2),
    supp b subset [R-eps,R+eps] union [-R-eps,-R+eps].

Take any physical window containing these supports. Every cross-distance
between supp a and supp b lies strictly between log6 and log7:
exp(2eps)<1/(1-2eps)=50/49<min(13/12,14/13).
Consequently ALL prime-power mixed correlations vanish. Supports are disjoint,
so the diagonal mixed term vanishes; the odd pole pairings vanish by parity.
The exact remaining mixed form is

    k(a,b)=integral integral a(x)b(y)
                       [p(x)p(y)-j(|x-y|)] dx dy >0.       (V4)

Indeed p(x)p(y)>=2 and j(s)<1 for s>log6>1. Thus, for f=a-b,

    |f|=a+b,  k[|f|]-k[f]=4k(a,b)>0.                      (V5)

Normalizing f does not change the strict sign. These are rigorous smooth
physical tests, not claimed exact finite Fourier bottoms. They disprove the
universal source property k[|f|]<=k[f]; they do NOT disprove a bottom-specific
or escape-conditional estimate. The even pole is an actual obstruction to
importing a positivity-preserving/Dirichlet argument for the signed form.

## 5. Jet escape alone does not control Fourier return

On the original schedule take the exact carrier vectors

    f_m(x)=sqrt(2/L) cos(2*pi*m*(x+L/2)/L) 1_I(x).

They are normalized and even. Every fixed theta derivative has finite L1
norm, so its pairing with f_m tends to zero, bounded by sqrt(2/L) times that
L1 norm. Hence every fixed finite jet projection tends to zero.

But |cos(theta)| has constant Fourier coefficient2/pi and its other modes
are2k. Therefore in the carrier |n|<=m the projection of |f_m| retains ONLY
its constant mode, and exactly

    ||P_m|f_m|||²=8/pi²,
    ||(I-P_m)|f_m|||²=1-8/pi² >0.                           (V6)

Thus jet escape does not even imply an L2-small return error. Form-small
return is a further requirement. These vectors are not asserted to be
bottoms: (V6) identifies the missing use of minimality/source information,
not a counterexample to T. Nonnegative escaping profiles have d_f=0, so
phase repair also cannot alone exclude pure spatial escape.

## 6. Exact unpaid source estimates and distinction from T

T is a statement about ONE fixed finite observable of actual bottoms along
an unbounded original sequence. It says nothing about a modulus transform,
its jump gain, its pole increase or its carrier-return cost.

This attempt needs a source theorem excluding the following possibilities
on a hypothetical escaping low-energy bottom sequence:

1. insufficient jump phase defect to beat H (including nonnegative escape);
2. a Fourier-return form error that consumes the improvement.

The explicit unpaid estimate for this route is (V3), preferably supplied
as independently proved gain and error inequalities as in section3, using
minimality/low energy to exclude the two failures. It is a STRONGER,
transformation-specific mechanism; it is not asserted equivalent to T.
It can fail on ordinary admissible functions even if T is true. Equations
(V5),(V6) show why it does not follow from generic form contraction or jet
escape. They also specify concrete tests for any proposed supplier.

Outcome: no admissible competitor with proved strict gain has been produced
for an actual escaping CCM bottom. The two exact source obstructions are
identified; no claim of NOESCAPE, RH, or a completed proof is made.

Independent read-only review checked V1-V6, domains, signs and quantifiers;
conditional only on the inherited literal source form/carrier conventions.
Reviewed pre-status SHA256:
452c8066c4556b71c69ab603b49381bb3cca72ae7358b3466115d442cf74bf8c.
