# Boundary removal restores H1 but not polynomial full-space transport

2026-10-08, own calculation while Q4 is pending. Not included in its sent packet.
Use exactly E,P,a,h,L,Lp of CCM_PHYSICAL_WINDOW_TRANSPORT.md.
Define the full analysis map Otilde_(kj)=sqrt(a)*sinc(pi(j-a*k)), k in Z.
The earlier finite projection-return matrix O is its restriction to |k|<=M.

## Orthogonal boundary split, with the removed component retained

For coefficients c on |j|<=m let beta_j=(-1)^j, d=2m+1,
R=beta beta*/d and S=I-R. The centered polynomial f_c has both endpoint
values beta*c/sqrt(L). Thus f_(Sc) vanishes at both endpoints, and its
zero extension is H1 on the larger periodic interval. In particular,

    sum_k (2pi*k/Lp)^2 |(Otilde S c)_k|² = ||f_(Sc)'||²
                                  <= (2pi*m/L)^2 ||Sc||².      (1)

No endpoint distribution remains in(1). The original vector is still
c=Sc+Rc; R is not discarded. For any source matrix A and actual PSD T,

    Tr(T A)=Tr(T S A S)+Tr(T S A R)+Tr(T R A S)+Tr(T R A R).     (2)

Neither cross term is signed by positivity of T. Small rank of R alone gives
no smallness for these terms. Applying this separately at both endpoints
must also retain the different beta vectors/dimensions and original padding.

## A boundary-vanishing original vector still leaks logarithmically

For m>=16 take the unit old-carrier vector

    f=(phi_(L,m)-(-1)^m phi_(L,0))/sqrt(2).

Both endpoint values are zero. At the omitted new label k=m+2 set
epsilon=(m+2)h; the previously proved bounds give
epsilon in(0,1/2], a>=1/2 and epsilon>=1/Lp. Exact overlap gives

    |<phi_(Lp,m+2), Ef>|
      = sqrt(a/2) sin(pi*epsilon)/pi
          [1/(2-epsilon)-1/(m+2-epsilon)]
      >= epsilon/(4pi) >= 1/(4pi*Lp).                         (3)

Indeed the bracket is at least1/4 for m>=16, sin(pi*epsilon)>=2epsilon,
and sqrt(a/2)>=1/2. Therefore even on the complete endpoint-vanishing
old subspace a uniform O(m^(-b)) L2 leakage estimate is false for each b>0.
This is an exact original-carrier control, not an assertion about the
actual negative spectral density. No bound restricted to that density
has been refuted.

The finite-energy projection theorem can now be applied, but its input
energy need not be uniformly bounded: for this example
||f'||²=(2pi*m/L)^2/2. With new cutoff M=m+1 its elementary tail upper
bound is order1, not a polynomial gain. Restoring finiteness of the energy
does not establish the bounded-energy hypothesis used for selected decay.

## Mathematical decision

Boundary removal by itself does not fix the uniform transport obstruction.
Any useful actual-T estimate must both control its source-weighted frequency
distribution and pay(2), or bypass this transport norm. Q4 already asks for
the actual relative-form estimate; do not send another message while it runs.
SP/RH remain OPEN. No new arithmetic floor gain is asserted.

Independent ccm_window_transport audit PASS after making the full-analysis
versus finite-matrix notation explicit. The Parseval equality uses all integer
rows of Otilde, while P uses only |k|<=M. All constants and control scopes
checked; no source-specific signed gain claimed.
