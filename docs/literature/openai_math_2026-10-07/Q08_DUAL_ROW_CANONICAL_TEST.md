# Dual-row return: the canonical Gauss moment has the wrong width

2026-10-09. Own attempt on the OPEN Q8(24)/(32) joint correlation.
Independent read-only q05_moment_audit PASS for D1–D4, including the
coefficient distinction and the zero-extended insertion. Source is the same pinned paper,
SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
No full source certification or new estimate is asserted here.

## Candidate and exact domain test

Q8(21) converts the actual Mobius coefficients into cubic Gauss coefficients.
On the allowed primitive branch g=t=f=1, b,c~L=U^r, the natural dual range
is K=L^2/U. Thus K>L for r>1: perhaps sum in the dual row FIRST, rather
than reflecting each column separately. This is a test of a supplier,
not a bound or lower bound for that branch or the full correlation.

The source canonical marked estimate (paper9296–9340) is unusually close:

    Z^-V sum_f w(f) sum_(q_k<<Z^M)
      |Z^-N/2 sum_(n sf) baralpha(n) gamma2(n) nu(n) rho(n)
          chi_n(k) chi_n(f)^4 d(n) W(q_n/Z^N)|^2
       << Z^(N+V+epsilon).

Here f is an ADDITIONAL averaged squarefree ideal of size Z^V, not the
divisor f in Q8(24). The source requires, with F0=N+V and c_*>0,

    q_(r_rho) <= Z^(N+V-M-z0-c_*),
    3M+6z0+c_* <= 4(N+V).                              (D1)

The complete coefficient/mark hypotheses also apply: no arbitrary residual
coefficient, fixed finite-ray nu, puncture independent of k,f, permitted
product-form prime slots only. Exact separation of Q8's pair conditions
and common profile would still need payment. Even granting that mapping
and the most favorable rho=1,z0=0, the numerical entrance fails:

    Z=U, N=r, M=2r-1, V=0:
    N-M-c_* = 1-r-c_* < 0.                             (D2)

The norm-one puncture cannot be bounded by a negative power of U. A shorter
column relative to the dual row therefore does NOT permit applying this
particular canonical Gauss estimate. At r=5617/5000 the deficit before
c_* is617/5000. In contrast, the marked INVERSE moment at source9250–9268
allows short columns but has the actual mu(n)nu(n) coefficients, not the
Gauss coefficients obtained after Poisson. Interchanging the two lemmas
would be a coefficient substitution.

## Why the missing fourth-power average is not free

Abstractly a new V>r-1+c_* could repair the first inequality in D1, but that
does not construct the required chi_n(f)^4 average in the actual kernel.
The simplest attempted invariance insertion is k→k*f^2, since

    chi_n(k*f^2) chi_n(f)^4 = chi_n(k) 1_(n,f)=1.     (D3)

This retains the original zeros and requires no (k,f)=1. Its row length
becomes M+2V. Even if all other costs, collisions, and the new column mask
could be returned for free, the necessary width condition would become

    N+V-(M+2V)-c_* = 1-r-V-c_* < 0.                  (D4)

Thus this precise insertion cannot repair the canonical-moment entrance.
The index shift f^2 is the smallest nonnegative exponent whose sum with4
is0 modulo6. This does not rule out a different coupled averaging identity.
In particular, the Mobius mask inversion from Q8(8) is not automatically
available for the new Gauss coefficient sequence; no such return is assumed.

## Decision and next supplier

The canonical-moment import in the form D2, and its f^2 repair D3, are
STALLED by their explicit domain inequalities. Neither refutes Q8(32),
nor does a branch test estimate the full sum. The exact remaining candidate
is a joint Gauss correlation estimate in the row-longer-than-column range,
or a coupling that genuinely introduces the missing fourth-power average
without paying two extra row lengths. All actual coprimalities, w_P,
the common radial argument, dual branches, and scale/profile returns must
survive that map. No new power gain has been obtained.

One UNVERIFIED search direction is a centered/asymptotic Gauss second
moment, rather than a bound on the full positive energy. On the upper
small-gcd region the actual equal-column diagonal is absent. Source
10187–10209 pays principal/equal columns by O(Z^M); simply importing
that positive bound after forgetting the exclusion reintroduces a charge.
Moreover source9970–10004 uses triangle/Cauchy bounds during completion,
so removing a principal term at the outset does not automatically remove
every principal term of every resulting square. Any centered recursion
must retain these cross terms and restore its exact diagonal explicitly.
This is a candidate mechanism, not a proved extension of the source lemma.
