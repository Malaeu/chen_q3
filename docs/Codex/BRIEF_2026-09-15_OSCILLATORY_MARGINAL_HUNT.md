# Bounded hunt: oscillatory marginal mechanism for exact gamma reciprocity

Source base: 4353bf4d7304457e3731cf6112149619f0116282.
Status: source-pinned exploratory discovery, INCOMPLETE_NO_CONSUMABLE_TARGET; canonical consumer edge remains unbound. No admission, goal change or Proshka dispatch.

Exact source and target: r_N is the density of sum_(n<=N) Gamma(2,1)/(pi n^2), G_N(x)=sqrt(r_N(e^(2x))r_N(e^(-2x))), and M_N(z)=integral_R G_N(x)e^(-izx)dx / integral_R G_N(x)dx. For every R>0 and 0<epsilon<1/2, C6 asks for N0 so every N>=N0 has no M_N zero on |Re z|<=R, epsilon<=|Im z|<=1/2. Source: REPORT_2026-09-15_GAMMA_CRITICAL_STRIP_INTERFACE.md §3, SHA256 97213adb97f5a5b8224ce1f4268e4afc186e15a125dd1f7b95cc57a4e0f8c5e0.

Known input: exact simplex marginal plus Prekopa gives -(log G_N)''>=4pi cosh(2x), hence every real tilted variance <=1/(4pi). Therefore |M_N(u+iv)|>=1/256 for all N>=1, |u|<=5, real v. Accepted intake REPORT_2026-09-15_CRITICALSTRIP_INTAKE.md I1-I2, SHA256 f28495620937793b270bf28208019c0d3c6915cd4de00932fe48f351c37b6e21. Full arbitrary-R C6 stays open. Arithmetic reciprocal H_N has the same limit but loses uniform positive curvature; source rebuilding alone does not supply the zero theorem.

Negative control: g(x)=exp(-16x^2)P(4x), P(y)=16y^4+112y^2+333, is positive even with -(log g)''>16>4pi. Its normalized Fourier transform is exp(-z^2/64)[(z^2/16-20)^2+1]/401, with nonreal zero 4sqrt(20+i) in K_(20,1/4). Multiplication by exp(-eta cosh(2x)) for sufficiently small eta>0 preserves a nonreal zero and a qualitative double-exponential tail. This is outside the full gamma/TN rate-product class. Raw CRITICALSTRIP §6, SHA256 c84d367a7d3a30fed8671c482380c9c754f67d356846e9f6806e2a4c327f706c. A putative generic real-curvature-to-zero-free theorem must fail on this control.

Own search rewrites, UNVERIFIED:
1. The oscillatory Fourier integral is a complex marginal; perhaps a complex Prekopa/direct-image or phase-sector theorem constrains its cancellation, rather than only the integral of its modulus or a section norm.
2. The exact joint density may admit a stability-preserving contraction/integration rule; determine the input stability hypothesis without assuming the desired target zero property.

Three dictionaries: (a) complex Prekopa, Berndtsson direct image, Bergman kernel and log norm; (b) complex Brascamp-Lieb, sectorial marginal, nonvanishing partition function; (c) stable polynomial integration, Lieb-Sokal, Lee-Yang closure.

Shelf reconciliation already found: REPORT_2026-09-12_PHYSICS_BROTHER_LEE_YANG.md explicitly records that Lieb-Sokal needs single-site Lee-Yang; the exact theta entropy-binomial lift was excluded by LYGSPHI intake. The N=1 imaginary-order Bessel/Sturm-Liouville brother is already in GAMMA_RECIPROCITY_BRIDGE. Do not rediscover those as new results. The prior Fock/Krein/Schur hunt did not resolve oscillatory marginals.

Bounded stop: inspect primary statements for at most three mechanisms; report exact variable/quantifier mapping and first unpaid or false hypothesis. No generic conclusion from a theorem name, no stronger all-plane approximant requirement, no absence claim from an INCOMPLETE shelf receipt. New useful information must distinguish complex signed integration from positive marginalization or provide an actual source-specific sufficient hypothesis. If none transfers, preserve the mismatch and return to source structure; do not create a renamed C6 task.
