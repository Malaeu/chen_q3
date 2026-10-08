# Perturbed principal Euler box: uniform local return

2026-10-09. Root calculation; independent bounded audit recorded below. This supplies ONLY
principal correction hypotheses for the candidate in PARAMETER_BUDGET.md,
not a new high/low transfer theorem, zero-free strip or RH proof.
Pinned paper.tex hash42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3;
local identities4007-4050, selected replacement8670-8750, principal bound9050-9095.

Fix t=1/100000, sigma=7/8-t/4 and any fixed physical slot system of
positive lengths ell_i, total ell=1/6+t, disjoint supports as in source.
The slot count K and lengths ell_i are chosen before and independently of
the target eta. Fixed arithmetic data and constants may depend on eta.
Use the original unramified principal row u=1. Consider the CLOSED box
of real parts x_r>=sigma,w_r>=19/20,z_r>=33/200. Estimates below are
uniform in all imaginary parts and all finite-order target unit phases;
normal convergence is local on the corresponding complex region.
Original finite excluded S stays fixed.

## Literal factors and a convergent majorant

Write Q=q_p>=2, q0=Q^(-1), V=Q^(-6z), W=Q^(-w),
D=eta(p)Q^(-x), R=baralpha(p)^6 eta(p)^6 Q^(4-6x-6z).
The accepted unramified identity in ANGULAR_FACTOR_NEIGHBORHOOD.md is

 (1-R)H_p=1+[-VW-R q0(1-W)-R W²(1-V)
       +D(W+V-QWV+(Q-1)W²V)]/(1-D).                 (B1)

Both denominators 1-D and 1-R are uniformly away from zero:
|D|<=2^(-sigma)<1 and |R|<=2^(4-6sigma-99/100)<1.
The absolute decay exponents in H_p-1 are bounded below by

 min{w_r+6z_r, 6x_r+6z_r-4,
      x_r+w_r, x_r+6z_r, x_r+w_r+6z_r-1,
      x_r+2w_r+6z_r-1} >9/5.                       (B2)

The omitted Rq0 and RW² terms decay faster since w_r,z_r>0.
The smallest displayed lower-corner value is sigma+19/20+99/100-1
=1.8149975>9/5. Thus |H_p-1|<=C Q^(-9/5), uniformly in heights.
Ideal counting yields a convergent positive product majorant. The same
majorant controls every product with any finite set of selected primes
removed, without dividing by possibly vanishing H_p. Normal convergence
and nonzero rational denominators prove holomorphy in a neighborhood of
every point of this box; strict margins allow a slightly enlarged box.

## Selected factor without quotient division

At u=1 the source local identity gives

 E_p:=P_p^*+D
   =R[(1-q0)/(1-V)+W-D]/(1-R)
     -D(Q-1)WV/[(1-R)(1-V)].                       (B3)

Source normalized cancellation, with v=1, is

 G_p+H_p=(1-V)(1-W)/(1-D)
       [(1-Q^(-w))(V/(1-V)-D)
        +(bar eta(p)Q^x+1-Q^(-w))E_p].             (B4)

There is no H_p denominator here. B3-B4 and the uniform rational bounds give

 |G_p+H_p|<=C[Q^(-x_r)+Q^(-6z_r)
                     +Q^(4-5x_r-6z_r)+Q^(1-w_r-6z_r)]
             <=C Q^(-sigma).                     (B5)

Indeed the four lower-corner decay rates are sigma,99/100,
5sigma+99/100-4=1.3649875, and19/20+99/100-1=94/100.
Consequently G_p=-1+O(Q^(-sigma)), so |G_p|<=C uniformly.
The quotient-free selected-tuple definition and ideal counting in each
annulus imply, on every fixed real box,

 |Hfrak_(eta,1,Z)(x,w,z)|<=C_(boxes,slots,S) Z^(ell z_r). (B6)

No imaginary-height factor is needed for this local correction bound.
All selected factors and every unselected prime remain. Finitely many
small primes contribute bounded holomorphic factors, not deleted terms.

## Principal slice and exact acceptance boundary

On w=1,z=1/6, B1 and B5 give B_p=G_p/H_p=-1+O(Q^(-sigma))
for every sufficiently large selected prime, since |H_p-1|<1/2 there.
The original nonnegative slot weights yield

 B_i=-S_i(Z)(1+O(P_i^(-sigma))),
 Hfrak_(eta,1,Z)(x,1,1/6)
     =H_(eta,1)(x,1,1/6)(-1)^K prod_i S_i(Z)
                         [1+O(Z^(-sigma min_i ell_i))]. (B7)

The relative estimate applies once S_i(Z)>0; it uses the original slot
prime-mass input, not a new proof of that input. For even K the sign is +.
The nonzero unselected slice product is the already checked principal
angular factor result for x_r>2/3. Its angular Euler argument6x-3>1,
so no critical-strip nonvanishing of an angular Hecke function is used.
Equations B6-B7 provide the local correction bound and slice error required
by source principal-residue-interface; that interface itself still requires
its paths and scalar reciprocal bounds to be re-established at sigma<7/8.

This does not verify ramified rows, buffered-bin moment hypotheses, low
estimate, all contour joins, target-independent order of choices, or the
complete perturbed high identity. Those remain OPEN. It does not import
Hecke uniformity from the Linux zeta Comparator report. Constants for fixed
S and slots may depend on those fixed data but not Z, heights or moving
prime labels. No improved zero-free assertion follows yet.


## Conditional contour return (C1; bounded independent audit)

Here the starting principal integral must first be established as the u=1
term of the SAME physical probe's exact high identity. This section does
not define the physical probe by that integral. Retain the source scalar
quotient zeta_F^S(6z)zeta_F^S(w)/L_F^S(s,eta) and all Mellin tests.
Assume the source global reciprocal estimate on Re s>beta_* and its
polynomial height bounds. Its logarithmic-control lemma1531ff allows
any a in[1/2,1]; it does not require beta_*>7/8. This is a source
family premise, not something inferred from the zeta Comparator report.

Write P_eta(Z) for that principal term (source mathscr P_eta).
Let beta_*>sigma and0<e<1/1000. With B6-B7 and the source original
prime-mass input, set A_eta(Z)=(-1)^K Z^(-ell/6)prod_i S_i(Z).
For sufficiently large Z, A_eta is nonzero and its reciprocal has
subpower growth by that prime-mass input. Set mu=sigma min_i ell_i>0.
The principal residue proof6174-6303 then gives, conditionally on the
stated exact starting identity,

 P_eta(Z)/(c_S A_eta(Z))-f_eta(Z)
   << Z^(C_t(beta_*)+(1+h_t)e-ly_t/20+epsilon)
      +Z^(C_t(beta_*)+e-h_t/600+epsilon)
      +Z^(C_t(beta_*)+e-mu+epsilon).                 (C1)

Here f_eta is the original scalar integral on Re s=2 with C_t(s)=s-11/16
and the SAME H_eta(s)=H_(eta,1)(s,1,1/6). Proof: isolate u=1 on the
absolute lines; move s to beta_*+e, w to1+e and z to1/6+e. Every
point has real parts in the enlarged principal box. The reciprocal is
on a global zero-free line. B6 bounds the correction uniformly in
heights. The source integrated/trace tail lemma5673ff and unchanged
Mellin tests justify horizontal limits using a finite height degree
chosen before the tail order.

Next move w to19/20 and, only in its w=1 residue, z to33/200.
The correction is holomorphic by B1-B6 and the only crossed poles are
the scalar poles w=1,z=1/6. The unresidued w integral keeps z=1/6+e;
its outside exponent is C_t(beta_*)+(1+h_t)e-ly_t/20. The z remainder
has exponent C_t(beta_*)+e-h_t/600. On each extended vertical axis
the relevant scalar zeta argument is strictly on one side of its pole;
the horizontal joins have nonzero large height. Thus the same tail
lemma applies; after the w residue use its two-dimensional version.

At the double residue B7 supplies the relative error Z^(-mu), giving
the third term. Move only its error-free main integral right to s=2:
H_eta is bounded and holomorphic throughout this fixed real strip by
B2, the reciprocal is holomorphic for Re s>beta_*, and the Gaussian
kills its polynomial height bound. A principal L pole gives a zero of
the reciprocal, not an extra residue. The residue constant c_S>0 is
unchanged. The principal error exponents have strict positive margins
ly_t/20,h_t/600,mu before choosing e and epsilon.

This conditional proof uses the new principal box in place of D2 in
the original argument; it does not invoke the published lemma outside
its stated sigma0>=7/8 domain. It closes neither the physical high
identity nor the nonprincipal row estimates. No complete high approximation is yet accepted.

Independent read-only q05_moment_audit checked B1-B7 and the conditional
C1 contour argument against the pinned source. The audit required making
the pretarget choice of K and ell_i explicit so mu is target-independent;
that quantifier is now stated above. C1 still assumes the exact physical
starting identity and source family reciprocal estimates. No full
nonprincipal high estimate or new zero-free assertion is admitted.
