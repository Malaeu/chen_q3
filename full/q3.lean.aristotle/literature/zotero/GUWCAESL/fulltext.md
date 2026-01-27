---
title: "<span class=\"nocase\">H=xp</span> model revisited and the Riemann zeros"
authors:
  - "Germ\u00e1n Sierra"
  - "Javier Rodr\u00edguez-Laguna"
date: "2011-00-00 2011"
publication: "Physical Review Letters"
doi: "10.1103/PhysRevLett.106.200201"
url: null
zotero:
  attachment_key: "W282XHIE"
  parent_key: "GUWCAESL"
  item_id: 1960
  attachment_item_id: 2047
---

The H = xp model revisited and the Riemann zeros
Germ ́an Sierra∗ and Javier Rodrı ́guez-Laguna†
∗Instituto de Fı ́sica Teo ́rica, CSIC-UAM, Madrid, Spain †Universidad Carlos III, Madrid, Spain
Berry and Keating conjectured that the classical Hamiltonian H = xp is related to the Riemann zeros. A regularization of this model yields semiclassical energies that behave, in average, as the non trivial zeros of the Riemann zeta function. However, the classical trajectories are not closed, rendering the model incomplete. In this paper, we show that the Hamiltonian H = x(p + `2
p/p) contains closed periodic orbits, and that its spectrum coincides with the average Riemann zeros. This result is generalized to Dirichlet L-functions using different self-adjoint extensions of H. We discuss the relation of our work to Polya’s fake zeta function and suggest an experimental realization in terms of the Landau model.
One of the most promising avenues to prove the Riemann hypothesis (RH) is to find a self-adjoint operator H whose spectrum contains the imaginary part of the non trivial Riemann zeros [1, 2]. This idea was suggested by Polya and Hilbert in the dawn of the XX century and still, one hundred years later, it remains unproved, as well as the RH itself (see [3] for a recent review on physical approaches to the RH). There are significant hints of the validity of the Polya-Hilbert conjecture. Two of them are: the Montgomery-Odlyzko law which states, that the local statistics of the Riemann zeros is given by the Gaussian Unitary Ensemble (GUE) of Random Matrix Theory, and the formal similarities between counting formulas of zeros in Number Theory and energy levels in Quantum Chaotic systems. In this web of relationships, Michael Berry suggested the existence of a classical Hamiltonian whose quantum version would realize the Polya-Hilbert conjecture [4]. This conjectured Hamiltonian must satisfy the following conditions: i) be chaotic, with isolated periodic orbits related to the prime numbers, ii) break time reversal symmetry, to agree with the GUE statistics and iii) be quasi-one dimensional. These conditions were derived from a formal analogy between the fluctuation part of the Riemann-Mangoldt formula of the zeros of the zeta function and the Gutzwiller formula for the fluctuation term of the counting of energy levels in a chaotic quantum system.
In 1999 Berry and Keating showed that the classical Hamiltonian Hcl = xp fullfills conditions ii) and iii) but not condition i) [5]. The failure of i) is dramatic because this Hamiltonian is integrable, and therefore not chaotic, and moreover the classical trajectories are not closed, which leads naturally to a continuum spectrum. Indeed, the Hamiltonian Hcl = xp can be quantized in terms of the self-adjoint operator ̂H = (x̂p + ̂px)/2, with ̂p = −iħd/dx, and its spectrum is given by the real line [6, 7]. In order to obtain a discrete spectrum, out of the xp model, Berry and Keating imposed the conditions |x| ≥ `x and |p| ≥ `p, where the minimal length `x, and minimal momentum `p span the Planck area `x`p = 2πħ in phase space. Subject to these conditions, a particle with energy E > 0 describes a truncated hyperbola in
phase space,
x(t) = `xet, p(t) = E
`x
e−t, 0 ≤ t ≤ TE = log E
h . (1)
The area bounded by this trajectory, and the x = `x and p = `p axes, measured in Planck units, gives the semiclassical number of states
N (E) = E
2πħ
(
log E
2πħ − 1
)
+7
8 + . . . (2)
where the constant 7/8 comes from a Maslov phase. Rather remarkably, this formula coincides with the asymptotic behaviour of the average term in the Riemann-Mangoldt formula [1], where E/ħ is interpreted as the height of a non trivial zero. Incidentally, Connes also studied the xp Hamiltonian imposing the constraints |x| ≤ Λ, |p| ≤ Λ, where Λ is a cutoff [8]. In the limit Λ → ∞, one obtains semiclassically a continuum spectrum, where the smooth Riemann zeros appear as missing spectral lines. However, a more appropiate interpretation of Connes’s result is that Riemann’s formula gives a finite size correction to the energy levels. Connes’s regularization were later derived from the Landau model of a particle moving in 2D under the action of external magnetic and electric fields [9]. A fundamental problem of the Berry-Keating model is that the classical trajectories are not closed. The particle starts at the phase space point (`x, E/`x), and stops at the point (E/`p, `p) in a time TE (see eq.(1)). The xp hamiltonian breaks time reversal, so the particle cannot return to its initial position along the time reversed path. Berry and Keating suggested different ways to close the trajectories, such as the identification of x and −x , and p and −p, or the use of symmetries, but no definite conclusion was reached, and consequently, the connection of (2) with the Riemann formula could not be put on more solid grounds. The aim of this letter is to show that the closure problem can be solved by a modification of the xp model that preserves several of its features, but makes it into a consistent quantum model. First of all, we shall constrain the motion of the particle to the half line `x ≤ x ≤ ∞
arXiv:1102.5356v1 [math-ph] 25 Feb 2011


 2
A
B
C
FIG. 1: Classical trajectories given in eqs. (5) (continuous line) and (1) (dotted line)
.
while the momentum is allowed to take any real value. The classical Hamiltonian is defined as
Hcl = x
(
p + `2p
p
)
, x ≥ `x, p ∈ IR (3)
where `p is a coupling constant with dimensions of momentum. If |p| >> `p, the extra term added to the xp Hamiltonian is negligible, but it becomes dominant if |p| << `p, forbidding the particle to escape to infinity, since that would cost an infinite energy. This result is made clear by the solution of the Hamilton equations
x ̇ = x
(
1 − `2p
p2
)
, p ̇ = p + `2p
p (4)
given by
x(t) = `x
|p0| e2t
√
(p20 + `2p)e−2t − `2p (5)
p(t) = ±
√
(p20 + `2p)e−2t − `2p.
A complete cycle of a classical trajectory can be described as follows (see fig 1). The particle starts at the point A = (`x, p0) (with |p0| ≥ `p). Then, x increases and p decreases monotonically reaching the turning point B = (xm(E), `p), where xm(E) = E/2`p is the maximal elongation. After that, the particle moves backwards to the point C = (`x, `2p/p0), which is attained in a time
TE = cosh−1 E
2h → log E
h (E >> h) (6)
where h ≡ `x`p should not still be identified with Planck’s constant 2πħ. At the point C, the particle bounces off, meaning that its momentum `2p/p0 becomes p0, and the cycle repeats itself, with TE being the period. The latter process preserves the total energy, and it is analogue of the change in the momentum, p → −p of a particle hitting a wall. The classical energies are bounded from below by the condition |E| ≥ E0cl = 2h. The minimum energy correspond to the static solutions x = `x and p = ±`p.
An extra condition on the Riemann dynamics is the existence of complex periodic orbits (instantons) with periods Tinst,m = πim (with m an integer) [5]. The orbits (1) of the xp model are periodic in imaginary time, but with a wrong period 2πi. After a complex time ∆t = iπ, the position and momenta change sign, which led Berry and Keating to suggest the aforementioned identification between x and −x, and p and −p, which in any case does not close the orbits. This problem does not arise for the Hamiltonian (3), which contains complex periodic orbits with a period πi, as can be seen from eq.(5). The semiclassical number of states is given by the phase space area swept by the particle measured in units of 2πħ, and it is given by
N (E) = E
2πħ
(
cosh−1 E
2h − √1 − (2h/E)2
)
(7)
'E
2πħ
(
log E
h −1
)
+ O(E−1), E
2h >> 1.
This formula agrees with eq.(2) if h = 2πħ, up to the constant term, which has not been considered in (7). Let us now proceed to the quantization of the classical Hamiltonian (3). We choose the normal ordering prescription,
̂H = x 1
2
(
̂p + `2p
̂p
)
x
1
2 , (8)
where 1/̂p is the 1D Green function satisfying ̂p ̂p−1 = ̂p−1
̂p = 1, and whose matrix elements are
〈x| 1
̂p |y〉 = − i
ħ θ(y − x) (9)
with θ(x) the Heaviside step function. ̂H acts on a wave function ψ as
̂Hψ(x) = −ix 1
2
[
ħd
dx
{
x
1
2 ψ(x)
}
+ `2
p
∫∞
`x
dy
ħ θ(y − x)y 1
2 ψ(y)
]
.
(10) This operator is hermitean, i.e. 〈ψ1| ̂Hψ2〉 = 〈 ̂Hψ1|ψ2〉, if both wave functions satisfy the non local boundary condition
ħ`
1
x2 eiθ ψ(`x) + `p
∫∞
`x
dx x 1
2 ψ(x) = 0. (11)
where θ ∈ [0, 2π). To derive (11), we have assumed that ψ(x) decays asymptotically faster that x−1/2. Using eq.(10), the Schroedinger equation ̂HψE = EψE becomes an integro-differential equation which can be converted into a second order differential equation and a boundary condition. The solution of both equations yields a unique square integrable eigenfunction given by
ψE (x) = x iE
2ħ K 1
2 − iE
2ħ
( `px ħ
)
, (12)


 3
x
»ΨE»
FIG. 2: Absolute value wave functions ψE(x), given in eq.(12) (continuous line), and x− 1
2 + iE
ħ (dotted line).
where Kν(x) is the modified K-Bessel function (the normalization factor is not included). The asymptotic behaviour of (12) is given by
ψE(x) ∼
{
x− 1
2 + iE
ħ x << xm(E)
x− 1
2 + iE
2ħ e−`px/ħ x >> xm(E) (13)
where xm(E) is the maximal length of the classical trajectory. If x << xm the wave function ψE(x) behaves, up to oscilations, as the eigenfunction x− 1
2 + iE
ħ of the quantum Hamiltonian x 1
2 ̂px 1
2 . However, ψE(x) drops exponentially in the classical forbidden region (see fig 2). The hermiticity of ̂H, requires the eigenfunctions (12) to satisfy the boundary condition (11), which in turn provides the equation for the eigenenergies, En,
Ξ
̂H(E) ≡ e−i θ
2 K1
2 + iE
2ħ
(h
ħ
)
+ ei θ
2 K1
2 − iE
2ħ
(h
ħ
)
= 0.
(14) All the solutions of this equation will be real, if the Hamiltonian ̂H is, not only hermitean, but also self-adjoint. To verify this property we use the von Neumann theorem: ̂H is a self-adjoint operator if the deficiency indices n+ and n− coincide [10, 11]. These indices are the number of linearly independent solutions of the equations ̂H†ψ = ±iψ. Then if n = n+ = n−, the operator ̂H admits infinitely many self-adjoint extensions parameterized by matrices of the unitary group U (n). In our case we find that n+ = n− = 1, therefore the self-adjoint extensions correspond to a phase, that can be identified with the factor eiθ appearing in equations (11) and (14). This ends the proof of the reality of all the eigenenergies En. If θ 6= π, all the eigenenergies are non vanishing and form time conjugate pairs {En, −En} with their associated eigenfunctions being related by the time reversal transformation ψ−En (x) = ψ∗
En (x). If θ = π, there is a unique state of zero energy E0 = 0, and eigenfunction
ψE0 (x) ∝ x− 1
2 e−lpx/ħ, while the non zero energy states form again time conjugate pairs. The ground state energies ±E0 depend strongly on θ and can be lower or higher than the classical value E0cl. To fix the value of θ, corresponding to the average Rie
5 10 15 20 25 30 E 1000 1001 1002 1003 1004 1005 E
FIG. 3: From bottom to top: plot of − log |Ξ(E)| (Riemann zeros), average Riemann zeros, − log |Ξ ̂H (E)| (eigenenergies
of ̂H for h = 2πħ, θ = π/4, and − log |Ξ∗(E)| (Polya zeros). The cusp represents the zeros of the corresponding equations.
mann zeros, we use the asymptotic behaviour of eq.(14),
Ξ
̂H (E) '
( 4πħ h
)1
2
e− πE
4ħ cos
(E
2ħ log E
2he − θ
2
)
, (15)
which vanishes at
E
2πħ log E
2he − θ
2π = n + 1
2 , n ∈ ZZ. (16)
If h = 2πħ and θ = 5π/4, one recovers the semiclassical estimates for N (E) given in eqs. (2) and (7). In references [4, 12], it is shown that a better estimate of the average position of the Riemann zeros is obtained equating N (E) to a half integer n + 1
2 , rather than an integer, which in view of eq.(16) yields θ = π/4 (see fig 3). A confirmation of these results comes from a comparison with Polya’s work on the Riemann Ξ-function [13] (see also [1, 2]),
Ξ(t) = 1
2 s(s − 1)π−s/2Γ(s/2)ζ(s), s = 1
2 + it, (17)
which is an entire and even function in t, whose zeros coincides with the non trivial zeros of ζ( 1
2 +it). Polya made a Fourier expansion of (17) and truncated it, obtaining
Ξ∗(t) = 4π2(K 9
4 + it
2 (2π) + K 9
4 − it
2 (2π)), (18)
which is called Polya’s fake zeta function. since it shares several properties with Ξ(t). First of all, the zeros of Ξ∗(t) and Ξ(t), agree in average, as can be seen using the asymptotic expansion [2].
Ξ∗(t) ∼ π 1
4 2− 5
4 t7
4 e− πt
4 cos
(t
2 log t
2πe + 7π
8
)
. (19)
This expression vanishes when the argument of the cosine is n + 1
2 , which confirms the aforementioned rule for the average location of the Riemann zeros, and in turn the choice θ = π/4. A more remarkable fact is that all the zeros of Ξ∗(t) are real, as was proved by Polya using a general theorem on entire functions [13]. This theorem can also be applied to prove the reality of all the zeros of Ξ ̂H (E), a result that we obtained using the
self-adjointness of the operator ̂H.


 4
The RH is a particular case of the generalized Riemann hypothesis (GRH), which asserts that all the non trivial zeros of the Dirichlet L(χ, s)-functions, associated to the Dirichlet character χ, lie on the critical line Re s = 1
2. These functions are defined by a series and associated Euler product (Re s > 1)
L(s, χ) =
∞
∑
n=1
χ(n)
ns =
∏
p:prime
1
1 − χ(p)p−s , (20)
and their analytic extension to the complex plane. χ(n) are multiplicative arithmetic functions, i.e. χ(nm) = χ(n)χ(m), χ(n + qm) = χ(n), χ(1) = 1, where q is the modulus of χ. L-functions associated to primitive characters satisfy the functional relation [14],
ξ(s, χ) =
(π
q
)− s+aχ
2
Γ
( s + aχ 2
)
L(s, χ) = χ ξ(1 − s, χ)
(21) where aχ is the parity and χ is the sign of a Gaussian sum,
aχ = 1 − χ(−1)
2 , χ = τχ
iaχ q1/2 , τχ =
q
∑
n=1
χ(n) e 2πin
q
(22) A L-function is even (odd) if aχ = 0 (1). The Riemann zeta function corresponds to the trivial character χ(n) = 1, ∀n, with aχ = 0, χ = 1. Equation (21) yields the average location of the zeros of L(χ, s)
t
2π log q t
2πe − 1
8 + aχ + χ − 1
4 =n+ 1
2 (23)
which leads us to the following identification of parameters in the ̂H model (see eq.(16)),
E
ħ = t, h = 2πħ
q , θ= π
4 (3 − 2aχ − 2 χ). (24)
The Riemann zeta function corresponds to the case q = 1, for which h = 2πħ, θ = π/4. The correspondence (24) implies that the constant h is quantized as a function of the modulus of the L-functions, attaining the classical limit, h → 0, when q → ∞. A physical realization of the Hamiltonian (3) is suggested by the work of reference [9], which showed that Hcl = xp emerges as the effective Hamiltonian of an electron moving in the x − y plane, subject to the action of a uniform magnetic field B, perpendicular to the plane, and an electrostatic potential V (x, y) = V0 xy. If V = 0, the electron occupies the lowest Landau level which is completely degenerate. This degeneracy is broken by the potential V (x, y), which in perturbation theory becomes the 1D Hamiltonian Heff = ω0 xp, where ω0 = V0`2/ħ ( ` = √ħc/eB is the magnetic length). The latter Hamiltonian is obtained replacing y → `2p/ħ in V (x, y). Consider now that the particle moves in the half-plane x ≥ `
and that the electrostatic potential is
V (x, y) = V0x
(
y + (2π`/q)2
y
)
. (25)
Then, the effective Hamiltonian, in the lowest Landau level, in units of ω0, becomes (3), with the identifications `x = `, `p = 2πħ/q` and h = 2πħ/q. We expect the parameter θ to arise from an electric field applied at the boundary x = ` of the system. In summary, we have reformulated the Berry-Keating xp model in terms of the classical Hamiltonian Hcl = x(p+`2p/p) defined on the half-line x ≥ `x, which posseses closed orbits and whose semiclassical spectrum agrees with the average Riemann zeros. The quantization of this Hamiltonian, yields a self-adjoint operator ̂H, and a non local boundary condition parameterized by an angle θ. The spectrum of ̂H agrees asymptotically with the semiclassical result and the eigenenergy equation is similar to Polya’s fake zeta function that approximates the Riemann’s Ξ function. The construction is generalized to the Dirichlet L− functions, supporting the idea that the GRH could have a proof based on a common quantum mechanical model. To achieve this goal one has of course to find the quantum origin of the fluctuations of the Riemann zeros. This work suggest two possible scenarios. One is to discretize the dynamics as in the Arnold’s cat map. The other is to modify the Hamiltonian in a non trivial way. Further research is required to clarify which path is the best.
Acknowledgements.- We are grateful to Paul Townsend, Michael Berry and Jon Keating for conversations. This work has been financed by Ministerio de Educaci ́on y Ciencia, Spain (grant FIS2009-11654) and Comunidad de Madrid (grant QUITEMAD).
[1] H.M. Edwards, “Riemann’s Zeta Function”, Academic Press, New York, 1974. [2] E. C. Titchmarsh, ”The Theory of the Riemann ZetaFunction”, Oxford University Press, New York, 2003. [3] D. Schumayer, D. A. W. Hutchinson arXiv:1101.3116. [4] M.V. Berry, in Quantum chaos and statistical nuclear physics, eds. T. H. Seligman and H. Nishioka, Springer Lecture Notes in Physics No. 263, 1 (1986). [5] M. V. Berry, J. P. Keating, Siam Review 41, 236, 1999. [6] G. Sierra, Nucl. Phys. B 776, 327 (2007). [7] J. Twamley, G. J. Milburn, N. J. Phys. 8, 328 (2006). [8] A. Connes, Selecta Mathematica 5 29, (1999). [9] G. Sierra, P.K. Townsend, Phys. Rev. Lett. 101, 110201 (2008) [10] A. Galindo and P. Pascual, ”Quantum Mechanics I”, Springer-Verlag, Berlin, 1991. [11] M. Asorey, A. Ibort, G. Marmo, Int. J. Mod. Phys. A20, 1001 (2005). [12] R.K. Bhaduri, Avinash Khare, and J. Law, Phys. Rev. E 52, 486 (1995)


 5
[13] George Po ́lya, Acta Math. 48, 305 (1926). [14] H. Davenport, ”Multiplicative number theory”, Springer
Verlag, New-York, 1980.