# Q53: full canonical weight return and divisor-lattice budget

2026-10-27. Full original100044bytes/1662LF read, including all code.
SHA256 9e053358e4d653e2787a1f85520589e2077a6d6c8edf4f4f9a281cbea6fe2489.
Independent q53_bounded_audit: qualified PAPER PASS §§3–9, no material
findings, bound to that hash and canonical request9561eb7be86d7f6bb72790d174566a68809cdbe198353c8be6621044155444e0.
Upstream contour and receiver are inherited, not independently recertified.
Four exact assets inspected and replayed once in /tmp/ccm_q53_replay; all hashes and eight source frames verified, JSON byte-identical. Archived in q53_replay/. Finite rational/formal controls only, no actual zeros, production spectrum, Lean or Arb.

## Exact model return

Keep original P,N=m,L=log m,M=R=floor(m^epsilon), fixed0<epsilon<1/32.
For the finite actual divisor B=Pi/Q with all multiplicities, the rational
model p/Q has boundary L2 metric and conjugation C_B f=-B f#.
Clockwise right closure gives <C_B f,g>=sum Res(fg/B).
Simple weights are 1/Bprime(w); repeated roots require all jets.
Hermite interpolation of h_m g, h_m=exp(Lz)Bprime(z), restores exactly
 sum_actual r_w exp(Lw) f(w)g(w).
The full metric return proves ||T_m||=||J||. It is not a lower bound on
compressed CCM and does not exclude additional cancellation on its image.

Both observations share the same complex c=Pc. Precisely,
 c*Rlow c=(2/L) Re <O_minus c,A_B O_plus c>, A_B selfadjoint.
With O_minus=O_plus F, Rlow=(F X+X F)/L. Opposite parity requirements are
 X_even>=-L s_m/2, X_odd<=L s_m/2.
Neither follows from Gram positivity or selfadjointness. Lyapunov identity
Gamma G+G Gamma*=11* contracts exp(-t Gamma), whereas the actual source
contains exp(+L Gamma). Changing that sign would change the source.
Q53(5.11), the whole linked-image lower with vanishing exponent, stays OPEN.

## Different arithmetic map, complete price

Actual divisor identity sum_(d|n) Lambda(d)=log n yields the finite graph
upper log(Nvirtual)+3. The tensor lift over exponent box0<=a_p<=K is an
exact physical-norm isometry, but each p^k edge retains only
 alpha_(k,K)=(1-k/(K+1))_+.
Every missing coefficient is returned, including proper powers and both
times; virtual edges d>=m have zero integrated overlap by support, but
remain in the graph price. The full source upper is
 s_K=K theta(m)+3+[12sqrt(m)+24L(1+L)]/(K+1).
Elementary theta(m)>=m/8 eventually gives s_K>=m/8 for every integer K>=1;
K=1 has exponent1. This is the price of this certificate ONLY, not a
lower bound on the actual signed source. K=0 returns the entire source.
Stop optimizing K with the same graph cap.

## Consumer and rollback

If independent Rlow>=-s_m P were proved, original contour fees p_m give
 T_>R<=(s_m+p_m+bdiv)P-H_P,
 PKP>=H_P-(s_m+p_m+50L+8)P,
eta=max(theta,2epsilon) when s_m=Oepsilon(m^theta). This input is unpaid.
Retain the better independent direct fallback without duplicated fees:
 s_keep<=6sqrt(m)+6m^(1/4),
 T_>R<=(s_keep+bdiv)P, PKP>=-(s_keep+50L+8)P.
No new exponent; all-P goal OPEN, RH unclaimed, CF22/PySR parked.
Rollback before full-model norm or full virtual graph payment. A possible
next bounded question is whether a nonuniform finite carrier can reduce
that paid price; first test a carrier-independent coefficient/cutoff
constraint before introducing another representation. This is not a proved
supplier or an automatic Q54 dispatch.
AUTOPSY: dropped=NO_DERIVATION; note=Canonical conjugation restores actual weights at the old core price; the isometric box lift costs a linear virtual logarithmic cutoff.
