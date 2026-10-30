# GREEN audit: escaping jump anchor, retained response still open

Status: bounded independent PAPER reviews and root exact replay PASS.
T and RH remain OPEN. Original verdict is byte-preserved.
Delivered by Proshka's ordinary GitHub commit bf8612ad, authorized new path
only; fast-forwarded at the22:50UTC check. All744 lines read.
Verdict SHA256: 22f55b348b13c3a6188027578bc1a4a8130fe8388c1a2cdc32f427da762ad081.
Request SHA256: f0a32cbee5a7643ef2bbb0e2730dee96ef33437109a1c672c0713c22e7bb8c72.
Appendix copied verbatim to ../thetagrade_2026-10-28/green_proshka_algebra.py;
SHA256 f318416d183bcd5f74414e83397473347c4fe2064a0ebc544b7f6299e4393d4d.
`uv run --with sympy python .../green_proshka_algebra.py` returned
ALL_EXACT_CHECKS_PASSED. This replay checks algebra/plants, not analytic rates.

## The new literal-source proof

The central binomial coefficient divides lcm(1,...,2n). Consequently the
elementary Chebyshev bound Psi(x)>=x log2/2 holds for x>=16.
The unit constant trial in the original carrier gives for the bulk
B=J-C I, alpha=lambda_min(B), eventually

    alpha <= -(2log2/e) sqrt(m)/log(m).

This is a variational bound for B, not A=B+uu*. The full-source theta return
supplies s_m approximating each fixed r=h^(2k), with both ||s_m-r|| and
||A s_m|| superpolynomially small. For ANY unit B-bottom e_m,

    |alpha| |<e_m,s_m>| <= ||A s_m||+||u|| |<u,s_m>|.

The pole norm is O(m^(1/4)), while <u,s_m> tends to
<sqrt2 cosh(x/2),h^(2k)>=2sqrt2*4^(-k). Hence every fixed jet pairing
of the ENTIRE lowest J eigenspace is O_r(log(m)m^(-1/4)).
The inherited fixed-jet density gives weak-zero convergence, with no
simplicity or unproved ||A||/||u||² ratio. This improves the conditional
e1 statement in NOESCAPE_POLE_DIRECTION_PROFILE, whose pole-vector proof
was independently obtained while GREEN was running.

The proof uses every prime power in the retained bulk and the complete
theta-return budget. It does NOT delete the pole from a claim about A.
It does NOT show that the selected full CCM bottoms escape.

## Other results and their scope

- Open-branch Schur formulas agree with our positive-complement attempt.
  Singular eigenvalues are classified using spectral projectors and the
  Moore–Penrose inverse; endpoints are not silently removed.
- A bounded positive-cone-preserving operator killing an a.e. strictly
  positive L² vector must be zero (truncate g by min(g,n e)). Therefore a
  nonzero complement inverse killing such a mode cannot have that order
  property. Actual finite J positivity/Perron behavior is not assumed.
- The exact 2x2 control has S=t²->0, inverse-square response t^-2->infinity,
  and a simple exact bottom. Small S plus exact minimality is insufficient
  at this abstract scope; this is not a literal CCM counterexample.
- W=(J_plus-beta+u_plus u_plus*)^-1 supplies the full filtered residual
  Wr_plus. The normalization and energy corrections (6.1)–(6.5) retain it.
  Quadratic-form W<=R does not imply W²<=R²; the supplied exact plant passes.
- Substituting the actual theta equation returns
  s_plus+b s1 W u_plus=W(e_plus-lambda s_plus).
  The old full leakage, its inverse amplification and signed cross terms
  survive. This is an identity, not a better response estimate.

## The remaining consumer

On the strict branch the normalized bottom is f=a e1-z, with
z=b R u_plus/sqrt((1+S)²+b²||R u_plus||²). Since e1 weakly escapes,
any retained fixed-jet component must occur in this coherently summed z.
This locates the component; it does not establish its retention.

A fixed compact cutoff chi with ||chi z||²>=eta>0 and uniformly bounded
logarithmic Fourier moment of chi z would give local compactness, a nonzero
weak limit and T. This is a conditional sufficient mechanism, not necessary
for T and not proved from CCM coefficients. No carrier return is needed
merely to observe chi z; an energy competitor would require the full return.
The existing J[f]<=C_m+o(1) budget grows with m and supplies neither required
local mass nor a uniform local logarithmic regularity bound.

No new Proshka question has been sent. Next bounded source attempt must
derive one of those missing quantities from coefficients, or try another
same-carrier strict variation. It must not relabel leakage as a supplier,
assume the strict branch cofinally, or equate J ground with the theta anchor.

## Independent review closeout

The Lemmas2–3 reviewer checked the real-x binomial/Psi argument, exact
constant2log2/e, constant-mode trial, all inherited CONFINE return terms,
pole pairing and uniformity over the entire lowest J eigenspace. No
substantive gap found. This accepts the literal bulk-anchor theorem at
bounded PAPER level, conditional on the previously checked source interfaces.
The Lemmas5–11 reviewer checked singular classification, order positivity,
full leakage, residual/normalization and local compactness. No algebraic
defect found. Precision guard: Lemma9's Rayleigh specialization still
requires q^T B q to lie in the standing open gap (mu1,mu2); generic trials
need not satisfy it. Original verdict remains unchanged. No Lean/Arb
proof of the analytic theorem is claimed. No strict A-bottom descent found.
