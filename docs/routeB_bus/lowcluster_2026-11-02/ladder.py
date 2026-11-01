"""Principal angles of the literal theta-derivative ladder and low CCM clusters.

compute_ladder(m, V, nodes, dps=None) accepts an (m+1)-row even eigenvector
matrix V (orthonormal columns ordered by eigenvalue) and quadrature nodes
(y,w) on [0,1].  No matrix construction or file mutation occurs here.
Profiles use H=hat h=4 xi(1/2-it); D=-x*d/dx-1/2.
All returned numbers are decimal strings, except dimensions and booleans.
"""
import mpmath as mp

PROFILE_NAMES = ('h', 'h_second', 'h_fourth', 'h_sixth', 'D_h', 'D_h_second')


def derivative_polynomials(max_order=6):
    """Exact dyadic coefficients P_r: P_(r+1)=P_r/2+2y(P'_r-P_r)."""
    polys = [[mp.mpf(0), mp.mpf(-24), mp.mpf(16)]]
    for _ in range(max_order):
        p = polys[-1]
        q = [mp.mpf(0)] * (len(p) + 1)
        for j, a in enumerate(p):
            q[j] += (mp.mpf('0.5') + 2*j) * a
            q[j+1] -= 2*a
        polys.append(q)
    return polys


def theta_derivatives(x, polys=None):
    """Return full theta h^(r)(x), r=0..6, preserving parity."""
    if polys is None:
        polys = derivative_polynomials()
    xx = abs(x)
    ex2 = mp.exp(2*xx)
    pref = mp.exp(xx/2)
    sums = [mp.mpf(0)] * len(polys)
    # Stronger than working precision: tail exponent is >~5.5*dps.
    cutoff = mp.mpf('2.4') * mp.mp.prec
    n = 1
    while True:
        y = mp.pi*n*n*ex2
        if y > cutoff:
            break
        ee = mp.exp(-y)
        for r, poly in enumerate(polys):
            val = mp.mpf(0)
            for a in reversed(poly):
                val = val*y + a
            sums[r] += ee*val
        n += 1
    return [pref*z*(-1 if x < 0 and r % 2 else 1)
            for r, z in enumerate(sums)]


def _maxabs(A):
    return max((abs(x) for x in A), default=mp.mpf(0))


def compute_ladder(m, V, nodes, dps=None):
    """Compute the six-profile subspace and its low-cluster principal angles.

    SVD is applied to column-normalized projected profiles. No normal-equation
    Gram inverse is used. Rank threshold is 10^(-dps+20), explicitly reported.
    At k=3 there are four canonical angles and two unmatched ladder dimensions.
    At k=7 there are six canonical angles and two unmatched cluster dimensions.
    """
    precision = int(dps or mp.mp.dps)
    with mp.workdps(precision):
        if V.rows != m+1 or V.cols < 8:
            raise ValueError('V must have m+1 rows and at least eight eigenvector columns')
        L = mp.log(m)
        quad = [(mp.mpf(y), mp.mpf(w)) for y, w in nodes]
        polys = derivative_polynomials()
        profile_values = []
        for y, _ in quad:
            x = L*(y-mp.mpf('0.5'))
            hd = theta_derivatives(x, polys)
            profile_values.append((hd[0], hd[2], hd[4], hd[6],
                                   -x*hd[1]-hd[0]/2,
                                   -x*hd[3]-hd[2]/2))
        A = mp.matrix(m+1, len(PROFILE_NAMES))
        for n in range(m+1):
            factor = mp.sqrt(L)*(mp.sqrt(2) if n else 1)
            trig = [mp.cos(2*mp.pi*n*y) for y, _ in quad]
            for j in range(len(PROFILE_NAMES)):
                A[n,j] = factor*mp.fsum(w*profile_values[i][j]*trig[i]
                                        for i, (_,w) in enumerate(quad))
        norms = [mp.norm(A[:,j]) for j in range(A.cols)]
        if any(n == 0 for n in norms):
            raise ArithmeticError('A projected ladder profile is zero')
        normalized = mp.matrix([[A[i,j]/norms[j] for j in range(A.cols)]
                                for i in range(A.rows)])
        U, svals, W = mp.svd_r(normalized, full_matrices=False)
        rank_threshold = mp.power(10, -precision+20)
        rank = sum(s > rank_threshold*svals[0] for s in svals)
        Q = U[:,:rank]
        fmt = lambda z: mp.nstr(z, precision)
        orth_error = _maxabs(Q.T*Q-mp.eye(rank))
        recon_error = _maxabs(normalized-U*mp.diag(svals)*W)
        cluster_results = []
        for k in (3,5,7):
            C = V[:,:k+1]
            overlap = Q.T*C
            left_sv, cosines, right_sv = mp.svd_r(overlap, full_matrices=False)
            coslist = [min(mp.mpf(1),max(mp.mpf(0),x)) for x in cosines]
            # Obtain sine from the orthogonal residual, avoiding acos(1-eps)
            # cancellation for nearly shared directions.
            sinlist = []
            for i in range(len(coslist)):
                z = C*right_sv.T[:,i]
                residual = z-Q*(Q.T*z)
                sinlist.append(mp.norm(residual))
            angles = [mp.atan2(s,c) for s,c in zip(sinlist,coslist)]
            cluster_results.append(dict(
                k=k, cluster_dimension=k+1, ladder_rank=rank,
                ambient_dimension=m+1,
                forced_intersection_dimension=max(0,rank+k+1-(m+1)),
                forced_intersection_note='At least this many canonical angles are exactly zero by dimension; raw computed angles retained',
                number_of_canonical_angles=min(rank,k+1),
                canonical_cosines=[fmt(x) for x in coslist],
                canonical_sines_from_residual=[fmt(x) for x in sinlist],
                angle_method='atan2(norm((I-Q Q^T) canonical_cluster_vector), cosine)',
                canonical_angles_radians=[fmt(x) for x in angles],
                canonical_angles_degrees=[fmt(x*180/mp.pi) for x in angles],
                unmatched_cluster_dimensions=max(0,k+1-rank),
                unmatched_ladder_dimensions=max(0,rank-k-1),
                overlap_frobenius_squared=fmt(mp.fsum(x*x for x in coslist)),
                cluster_orthonormality_error=fmt(_maxabs(C.T*C-mp.eye(k+1))),
                largest_raw_cosine=fmt(max(cosines)),
                smallest_raw_cosine=fmt(min(cosines))))
        return dict(
            m=m,N=m,L=fmt(L),dps=precision,
            theta_normalization='hat h(t)=4 xi(1/2-it)',
            dilation_operator='D=-x*d/dx-1/2; project full D h and D h_second',
            profile_names=list(PROFILE_NAMES),
            projected_profile_norms=[fmt(x) for x in norms],
            projected_profile_coefficients=[[fmt(A[i,j]) for j in range(A.cols)]
                                             for i in range(A.rows)],
            column_normalized_singular_values=[fmt(x) for x in svals],
            relative_rank_threshold=fmt(rank_threshold),ladder_rank=rank,
            ladder_orthonormality_error=fmt(orth_error),
            normalized_profile_SVD_reconstruction_error=fmt(recon_error),
            clusters=cluster_results,
            quadrature_nodes=len(quad),interval_certificate=False)
