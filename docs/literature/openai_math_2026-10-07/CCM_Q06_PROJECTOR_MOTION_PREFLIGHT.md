# Q06 waiting calculation: slow original projector, unpaid signed coupling

2026-10-21. Q06 already sent; this note was NOT sent as a second message.
Root derivation, read-only q06_signed_preflight bounded PAPER PASS, including transport and constants. No full exponent gain.

Work on an interval of L with M fixed. Do not freeze the original constraints.
In the coefficient carrier |j|<=M the exponential vectors have the same
spans as w_plus/minus with entries (1/2 +/- i 2pi j/L)^(-1); the omitted
common nonzero scalar factors do not affect their lines or P. Let u_plus,
u_minus be these vectors normalized, b the constant unit vector, U=[b,u+,u-].

Componentwise |w'_j|<=|w_j|/L, hence ||w'||<=||w||/L and
 ||u'_plus||, ||u'_minus||<=2/L, ||U'||<=2sqrt(2)/L.
On the late sparse schedule the existing receiver's normalized Gram estimate
G=U*U>=I/2 applies (M/L tends to infinity). This is also valid throughout
late constant-M intervals by the same uniform O(L/M) estimates.
The projector onto the constraint space is E=U G^(-1)U*, P=I-E. Differentiating
without estimating G' separately gives the exact formula

 E'=(I-E) U' U^dagger + [(I-E) U' U^dagger]*,
 U^dagger=G^(-1)U*, ||U^dagger||<=sqrt(2).

Thus ||P'||<=8/L, with no hidden M or rank factor. This bounds geometry,
not the arithmetic effect of that geometry.

For a transported unit vector c in ran P choose c'=[P',P]c=P'c. The
commutator is skew-adjoint, preserves norm, and preserves Pc=c. For the
complete unprojected sparse-carrier prime matrix A(L), the derivative of
<c,A c> has the projector-transport term

 2 Re <P'c,A c> = 2 Re <P'c,(I-P) A c>.

The elementary full source norm ||A(L)||<=4 exp(L/2)L (all prime powers)
yields only
 |2 Re <P'c,A c>|<=64 exp(L/2).

The actual constant-M cell has width epsilon^(-1)log(1+1/M), at most
1/(epsilon M). Absolute integration there gives O_epsilon(m^(1/2-epsilon))
with m taken at the upper end of the cell. This is still not subpower as
epsilon tends to zero. Adding cells over a fixed-length L interval costs
order exp(L/2), before mode jumps. Slow projection alone is insufficient.
This is an upper-budget failure, NOT a lower bound on the actual coupling.
A joint signed control can still be better. The derivative of A(L) itself,
old atoms, moving Fourier synthesis and mode-addition costs remain payable.
No use of P'=0, no replacement of the full cross term by the compressed
operator alone, and no claim that this is the full drift.

At jumps of floor(exp(epsilon L)), M changes; the present fixed-carrier
calculation does not bound the new-mode contribution. The Q06 response must
include that contribution or a justified cofinal way around it, preserving
one original cell for all vectors and the original fixed epsilon receiver.

Sources: CCM_SPARSE_BAND_RECEIVER.md (Gram), original Q04 §8 elementary
bound, FULL_CCM_MOMENT_SCHEDULE.md (schedule fees).
