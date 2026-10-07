# Actual local resonance before separate norms — 2026-10-07

Own calculation independently checked by causal_algebra_audit: PASS for exact local identity, zero masks, source overlap and limited scope. Source: pinned qrh78 paper.tex 630–641 (sextic symbols and zero powers), 3350–3478 (Gauss convention and joint row), 3735–3761 (full Poisson coefficient), 15575–15665 (nonvanishing principal normalization). Same file hash as sources.json.

## Exact one-prime calculation

At a good prime p of norm q, let chi=chi_p be the nontrivial sextic residue character, extended by zero, and g(chi,a)=sum_{d mod p} chi(d)e(ad/p). With the paper's convention, for m nonzero modulo p the change u=-m*d gives

g(chi,-m)=conj(chi(-m))*g(chi,1).

At m=0 both g(chi,0) and every zero-extended chi power vanish. Therefore, for every residue m and integer k,

chi(m)^k q^(-1/2)g(chi,-m)
 = q^(-1/2)conj(chi(-1))g(chi,1) chi(m)^(k-1).             (1)

The last factor is STILL zero at nonunits when k-1 is divisible by six; it is not the constant one. The standard finite-character sum now yields

q^(-1)sum_m chi(m)^k q^(-1/2)g(chi,-m)
 = q^(-1/2)conj(chi(-1))g(chi,1) (1-1/q)                 (2)

when k=1 mod 6, and zero otherwise. The normalized Gauss factor has modulus one, so the resonant average has modulus 1-1/q, not a negative power of q.

## Exact source correspondence and limits

The actual unseparated arithmetic row is xi(m) chi_A(m) q_s^(-1/2)g_{chi_s}(s,-m). When s=p, its p-local factor is (1) with k=v_p(A). Completed indices A=c*n^3 allow shared primes and k=v_p(c)+3v_p(n). Thus the resonant congruence k=1 mod 6 occurs when p divides squarefree c and v_p(n) is even, including A=p. This is an allowed local arithmetic pattern, not an independent artificial choice of row phases.

This calculation does NOT assert that a given global weight is nonzero at a given triple, nor that the entire compensated probe has a lower bound. The auxiliary xi at b*, other prime factors, ray restrictions, theta coefficients, annular m weight and all signed slot combinations remain. In particular, global complete zero-frequency cancellation from xi is compatible with a nonzero local p average. It cannot be inferred that the global zero frequency reappears.

What (2) rules out: a blanket claim that the two original m-dependent factors remain nonprincipal and cancel at EVERY good prime simply because each started with a sextic character. They can cancel each other's phases and leave a principal zero mask at shared primes. The global weighted sum is not a complete residue average anyway.

## Why removing all nonzero frequencies destroys the detector

The paper's exact joint Poisson expansion, before separate norms, already kills H=0 through primitive xi at b*. Surviving H=u*a^6 retain their full Fourier coefficient F(s,A,H). The u=1 family contains the reciprocal target-L signal. At its principal residue, the compensated prime slots are -S_i(Z)*(1+rho_i(s)), with |rho_i|<<P_i^(-7/8). Their nonzero scalar A_T(Z) has size comparable to (log Z)^(-K), and the same scalar divides BOTH low and high estimates. Thus the intended signal is expressly retained by the compensation; cancelling it away is not an improvement of the same detector.

A proposed subtraction of the principal family must construct an independent nonvanishing detector and an estimate for that subtracted family. Merely writing J=P+(J-P), bounding J-P, and declaring the remainder small moves the unproved estimate to P, whose Mellin integral already contains 1/L. No universal no-go is claimed: a genuinely new joint cancellation estimate could still improve the probe while retaining a nonzero signal.

This note is a discriminator for the pending Pro Q1, not a second question or a new mechanism. No RH/SP status changes.
