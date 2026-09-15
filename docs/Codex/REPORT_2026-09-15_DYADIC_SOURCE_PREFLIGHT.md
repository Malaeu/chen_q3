# Exact dyadic source rebuild: the odd block retains xi and adds zeros

STATUS: INDEPENDENTLY_REVIEWED_ANALYTIC_PREFLIGHT; scoped verdict and exact reviewed hash in the accompanying certificate.
SOURCE_BASE: 509270e47ca4b381461abaad8991fa087380a8bd.
Scope: one isolated analytic preflight of an exact arithmetic source rebuild;
no canonical admission, no new native goal, no full-V sign or RH claim.

## Why this bounded test

The accepted SIZEBIASCOMP result supplies full-field convergence, not sign.
The HANKEL_JORDAN result supplies a positive normalized kernel, not positivity
of its inverse Lyapunov image. Before another general positivity request,
test a source-specific rule using the full rates pi*n^2: split even/odd n.
The proposed shortcut is that the independent odd block is a simpler,
already real-zero building block. The cheapest falsifier is its exact Mellin
transform, with the xi critical line preserved. We do not ask for another
tail budget or claim that additive independence implies positivity of V.

This is direct analytic preflight plus verification of an already identified
primary source; it is not a new broad Semantic Hunt or an absence claim.
Reconciled inputs: REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md L1-L2
(full source/moments); REPORT_2026-09-15_RH_ROUTE_AUDIT.md sections 1-3
(target and exact-transfer limits); old DENSITY_SELFDECOMPOSABLE usage card
(self-decomposability already known). Do not count the general fixed-point
representation as new mathematics. No old failure counter is reset.

## D1. Exact arithmetic decomposition

Let T=sum_(n>=1) G_n/(pi*n^2), with independent G_n~Gamma(2,1).
Let U=sum_(n odd) G_n/(pi*n^2), and let T' have the same law as T,
independent of U. The even-index sum has law T'/4. Thus

    T =_d U + T'/4.                                           (D1)

Both sums converge almost surely, since their positive expectations converge.
With z=sqrt(pi*s), s>=0, their Laplace transforms are

    L(s)=(z/sinh z)^2,
    L_U(s)=L(s)/L(s/4)=sech(z/2)^2.                           (D2)

The value at s=0 is by continuity. The full infinite odd set is retained.
This is Pitman-Yor equation (85), with t=2, T=(pi/2)S_2 and
U=(pi/8)C_2. In particular U is not an elementary gamma first mode.

## D2. The odd-block density is an exact average of the full density

Write r for the density of T and q for that of U. Then

    q(t)=(4/pi) integral_t^(4t) r(v) dv, t>0.                 (D3)

Proof without a Mellin-contour interchange: the right side is nonnegative,
continuous and has total mass (3/pi)ET=1, because ET=pi/3.
Tonelli gives its Laplace transform, for s>0, as

    (4/(pi*s))[L(s/4)-L(s)] = sech(z/2)^2.

The last equality follows directly from sinh(2a)=2sinh(a)cosh(a).
Laplace uniqueness proves (D3). Let T* be size-biased T, with density
v*r(v)/(pi/3), and A independent uniform on [1/4,1]. Conditioning on A
gives exactly (D3), hence

    U =_d A T*.                                             (D4)

This is a statement in distribution. The independent T' in D1 and the
variables in D4 may be constructed independently, but T* is not an
independent unweighted copy of T. D4 retains, rather than removes, the
dependence of the building-block law on the original full source.

## D3. Exact Mellin relation, all complex parameters

Let m(p)=ET^p=2xi(2p), and m_U(p)=EU^p. All real positive and negative
moments of T exist by the full source bounds. D4 and 1/4<=A<=1 imply the
same for U. Both Mellin transforms are entire, with log derivatives
dominated on compact parameter sets by slightly larger real moments.
Fubini in D3 is therefore valid for every complex p. It yields

    m_U(p)=a(p)m(p+1),
    a(p)=(4-4^(-p))/(pi*(p+1)).                              (D5)

The singularity at p=-1 is removable: a(-1)=4 log(4)/pi.
For example, m_U(0)=1 and m_U(1)=pi/4, agreeing with the odd gamma sum.
The explicit entire factor a has zeros

    p_k=-1+i*pi*k/log(2),   k in Z, k!=0.                   (D6)

These are actual zeros of m_U because m(p+1) is entire. No assertion that
these are all its zeros, or that they are simple zeros of m_U, is needed.
The original xi zeros are also retained, translated by p=rho/2-1.

## D4. Preserve the target line before claiming a real-zero block

To compare the xi factor in D5 to xi(1/2+i*w), set

    p=-3/4+i*w/2,
    F_U(w)=m_U(-3/4+i*w/2)/m_U(-3/4).

The denominator is strictly positive. By D5,

    F_U(w)=[2a(-3/4+i*w/2)/m_U(-3/4)] xi(1/2+i*w).           (D7)

D6 therefore supplies the explicit nonreal zeros

    w_k=2*pi*k/log(2)+i/2,   k!=0.                          (D8)

This exact odd-block transform cannot serve as an already real-zero
starting object at the original xi center, irrespective of RH.
No assertion that F_U is even or belongs to the original V source class
has been made; D8 is NOT a negative V witness for the true theta source.

More generally at a real Mellin tilt p=b+i*w/2 the nuisance zeros lie on
Im(w)=2(b+1). They are real only at b=-1. But the xi factor then samples
xi(i*w), not xi(1/2+i*w). Retaining the original critical line requires
b=-3/4. No real power tilt aligns both lines. A positive rescaling U->cU
only multiplies the transform by c^p and cannot change any zeros.
This excludes only these operations, not other transforms or coupled maps.

Dividing D7 by the explicit a factor, with analytic continuation at its
zeros, returns precisely a nonzero constant times xi(1/2+i*w). It supplies
no independent theorem about the remaining zeros.

## D5. Decision and exact remaining interface

KEEP D1-D5 as exact source structure. REJECT the proposed shortcut
"use the odd block as a simpler independently real-zero building block".
Do not submit a request that assumes that property or calls D1 positivity
preservation. No general impossibility of source rebuilding is proved.

A useful future assembly theorem must act on the coupled complete form
and supply its all-finite-complex sign; scalar source positivity,
independence, or an interval average does not supply that theorem. This
preflight has not found that theorem. Do not turn the remaining interface
into another renamed source-sign attempt without a new independent input.

Counter scope: one DYADIC_SOURCE_REBUILD_REALZERO_BLOCK preflight. Its
algebra, primary-source check, independent review, and publication are
not separate attempts. Existing Barvinok and other counters are preserved.
Full V, all-R C6, IC/ODD2 and RH remain open. No Proshka request is sent.

## Primary-source record and provenance

Jim Pitman and Marc Yor, Infinitely Divisible Laws Associated with Hyperbolic
Functions, Canadian Journal of Mathematics 55(2), 2003, 292-330.
DOI: 10.4153/CJM-2003-014-x.
URL: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D91B384C84FA02C55A332B396BB85385/S0008414X00033484a.pdf/infinitely_divisible_laws_associated_with_hyperbolic_functions.pdf
Retained local PDF SHA256:
302f232c65a647b3e8a69bddb18163d12157b0d2b26e499e4c47fdde50ab957b.
Locators: equation (85) and following sentence; Table 1, printed p294,
row C2; discussion printed p293. Quote at equation (85):
"just a probabilistic expression of the duplication identity".
Mapping: T=(pi/2)S2, U=(pi/8)C2. The C2 Mellin table is consistent with
D5 after multiplying by 4^(-p). The paper supplies distribution/transform
identities; it is not cited as an RH or full-V theorem. D2-D8 above include
the parent derivation and its scoped consequence rather than a new claim
to discovery of the underlying distribution.

The web text was retrieved and matched to the retained local text. A web
screenshot request timed out; it is not evidence of a successful render.
The formulas relied on here are independently derived above, not guessed
from a failed screenshot. No new library search or no-hit claim is made.
