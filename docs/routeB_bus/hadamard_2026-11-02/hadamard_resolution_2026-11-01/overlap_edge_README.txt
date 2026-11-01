Finite ground overlap / physical edge diagnostics

Baseline: python overlap_edge.py 96 100
Validation: python overlap_edge.py 128 140 --validation
Summary: python overlap_edge_finalize.py

The shared convergence.py is imported only after sys.argv specifies quadrature order and dps. Its literal source matrix is built at N44; each smaller even principal block is diagonalized separately. Every integerN8..44 is included at each of L=log8,log12,log16 (111rows). Literal N=m is recalculated among those blocks.

The physical edge of unit eigenvector c is (c0+sqrt(2)*sum(cj,j>=1))/sqrt(L). Its squared value is divided by the actual ground eigenvalue and also by L times that eigenvalue.

P_N h is the actual L2 window projection: coefficients are integral h(x)e_(j,L)(x)dx computed with shared quadrature nodes, not full-line Fourier samples. h(x)=exp(x/2)*sum_n(16pi^2 n^4 exp(4x)-24pi n^2 exp(2x))*exp(-pi n^2 exp(2x)), using evenness for negative x. This is the full HARDBREAK profile with hhat=4xi, without unit normalization of h. w0=(c^T coeff)^2/(coeff^T coeff).

Baseline JSON/CSV contain all111rows, including overlap deficit, projection norm and eigenpair residual. The 140dps/GL128 run independently recomputes N40,N44 and literal N=m at all3anchors. The summary compares the two precisions/quadrature orders.

High overlap is an L2 statement; it does not imply agreement at the extremely small energy scale. No cofinal convergence or uniform edge bound is established by these finite samples.
