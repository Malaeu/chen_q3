# Independent bounded audit: Gamma, PNT diagonal, assembly, theorem imports

Status: DIAGNOSTIC / PAPER audit. No route-state or export changes. No counterexample found in the assigned claims. This is not an audit of the separate section 3 geometric bound, section 6 finite tail, or inherited rank–trace theorem. Consequently the main proportion conclusion remains conditional on those audits.

Input: local `INPUT_VERDICT.md`, pinned verdict supplied by root. Assigned equations (2.1), (4.1), (4.4), (5.1)–(5.2).

## Gamma identity (2.1), input lines 145–184

The identity has the correct sign, scalar factor, and basis phases. Write the source contribution of one exponential `exp(-a u)` as `2I/a - integral_0^L exp(-a u) R_u du`. Subtract its periodic diagonal symbol `2/a - 2a/(a²+omega_j²)`. For j != k, inserting (2.2) gives exactly

`2 d_j d_k a² (1-exp(-a L)) / [L (a²+omega_j²)(a²+omega_k²)]`.

On the diagonal j>0, integrating both `(1-u/L)cos(omega_j u)` and `sin(omega_j u)/(L omega_j)` gives `4a²(1-exp(-aL))/[L(a²+omega_j²)²]`; this equals (2.1) since d_j²=2. At j=0 the correction is `2(1-exp(-aL))/(L a²)`, again (2.1). In particular the u>=L source tail is essential; it is present in the `2I/a` term. The (-1)^j phase in the stated physical basis makes both endpoint values d_j/sqrt(L), consistently removing spurious alternating phases from this formula.

Summing a=2r+1/2 produces PSD rank-one terms. The bound sum_r a_r²/(a_r²+w²)²=O((1+w)^-1) yields tr K=O(log m)=O(L). Hence ||K||<=tr K and ||H||=O(L). The O(L²) error in the H² asymptotic is consistent: D² follows from Stirling summation of log²(j/L), with the O(L) low modes contributing O(L); cross DK and K² contribute at most O(L²). No positivity of A follows.

## Prime diagonal (4.1), input section 4

Let S(x)=sum_{n<=x}Lambda(n)²/n. Quantitative PNT and partial summation give S(x)=0.5 log²x+C_Lambda+O_A(log^-A x). The prime-power difference from the prime-only weighted measure is summable at infinity, while the PNT error is integrable after a sufficiently high log power; thus the displayed constant exists. The stronger unweighted assertion sum Lambda(n)²=x log x-x+O_A(x/log^A x) is also valid: choose the PNT exponent larger than A before partial summation, and prime powers contribute O(sqrt(x) log³x).

The exact averaging identity Q=(1/L)integral_0^L S(exp u)du gives Q=L²/6+C_Lambda+O(1/L). The finite initial segment produces the O(1/L) term and must not be omitted. Multiplying by d=2m+1 and using the separately audited (3.2) yields exactly D=mL²/3+2 C_Lambda m+O(m/L+L³). The extra `+1` in d contributes O(L²), already within O(L³). Thus the coefficient 1/3 is correct, conditional on (3.2).

## Frobenius assembly and transfer

The expansion is exactly ||H+P-B||F²=||H||F²+||P||F²+||B||F²+2tr(HP)-2tr(HB)-2tr(PB). Bounds (4.2)–(4.3) suffice: sqrt(m)L²=o(mL), m=o(mL), and the O(mL) arithmetic off-diagonal absorbs all smaller contributions. Thus (4.4) follows from (2.3), (3.6), and (4.1). This checks the assembly; it does not independently establish (3.6).

For fixed c in (0,1), fixed b>0, N(T)~m and sigma~L imply v->4/3 and t->1, hence Phi=4t-v->8/3. The claimed fractions 2/3 and 5/6 then follow algebraically from the inherited safe-score consumers `s1>=Phi_safe-2N` and `Nd>=(Phi_safe-N)/2`, provided their source normalization and o(N) tail payment are correct. These are asymptotic lower bounds, not finite census bounds and not RH. Finite off-line exceptions are compatible. At finite m the correct trace is 4t, not the substituted constant4.

## Primary external sources retrieved independently

1. Montgomery–Vaughan, *Hilbert's inequality*, JLMS (2)8 (1974), 73–82:
   https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf
   Local `external_mv.pdf`, text `external_mv.txt`, rendered/visually inspected page `external_mv_page1.png`.
   Theorem1, equation(1.3), p73 explicitly states the circular cosecant inequality with coefficient3/2 and arbitrary local lower gaps `0<delta_r<=min_{s!=r}||x_r-x_s||`. This is the correct circular theorem, not the real-line 3pi/2 version. No missing pi factor in the verdict's (0.1). The unweighted circular bound (1.2) has constant delta^-1. This verifies the imported theorem statement, not its application to section3.
   SHA256 PDF: 0dbcddf24bc41c65d1920c59aafe7fe85f13a7519b0edf9be9164c84d1cc6db4.

2. Johnston–Yang, arXiv:2204.01980v2:
   https://arxiv.org/pdf/2204.01980v2
   Local `external_pnt.pdf`, `external_pnt.txt`. Corollary1.2 gives theta error bounded by A1*x*(log x)^B*exp(-C sqrt(log x)) for a fixed listed row and sufficiently large x, which implies every fixed O_A(x/log^A x) rate used here. The classical rate is therefore a sufficient ordinary unconditional PNT import; no explicit onset/constants are needed in section4.
   Caveat: J–Y's proof expressly incorporates verification of RH up to finite height. This is not a global RH assumption and does not invalidate its unconditional theorem, but it would be inaccurate to assert their proof avoids computational zero verification. The verdict can consistently use only the classical asymptotic PNT rate and cite J–Y solely as a stronger external statement.
   SHA256 PDF: 565993a6def48b237a68a92acba604f2c42f99165e0e71e390f8e21a313b74b2.

3. Faber–Kadiri, *New bounds for psi(x)*:
   https://www.cs.uleth.ca/~kadiri/articles/New-Bounds-for-Psi-Math-Comp-Faber-Sept2013.pdf
   Local `external_rosser.pdf`, `external_rosser.txt`. Theorem1.5 p3 reproduces Rosser Theorem19: T>=2; P(T)=T/(2pi)log(T/(2pi))-T/(2pi)+7/8; R(T)=.137logT+.443loglogT+1.588; |N(T)-P(T)|<=R(T). Immediately preceding definition counts nontrivial zeros in 0<=gamma<=T, 0<=beta<=1. No line-only census or assumed RH is in this theorem. The paper's nearby computed-RH theorem is not needed. Original Rosser proof was not independently obtained; statement verified through this primary Faber–Kadiri source, matching the verdict's declared provenance.
   SHA256 PDF: a1d3f37e458d43a87bc33d5fe9c0d0d8d52ec34e8f610053dbdcbc0f72a7c5be.

External files were obtained directly by HTTPS and converted using pdftotext; the MV constants were also visually inspected because text extraction drops the displayed formula. No spectral scans or new zero census were performed. No `CCM_PHI_AUDIT_COUNTEREXAMPLE` is asserted by this bounded audit.
