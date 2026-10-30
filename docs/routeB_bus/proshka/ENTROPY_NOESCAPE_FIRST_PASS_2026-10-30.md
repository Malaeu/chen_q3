# Энтропия и отсутствие бегства: первая проверка

Owner request: test an entropy / prime anti-entropy mechanism after NOESCAPE.
Status: bounded PAPER derivation + saved-data diagnostic; no new source bound,
no RH claim, no Lean execution, no new Proshka dispatch.

## Exact consumer and source

Use the literal even CCM ground vectors f_m, normalized in L2(R) after zero
extension from their windows. The target T is persistent projection onto ONE
fixed finite jet J=span{h,h'',...,h^(2R)} on an unbounded set of m.
NOESCAPE L16 identifies this with a nonzero weak subsequential limit; L6 gives
T => RH. This note assumes those PAPER interfaces, not their formal admission.
It does not assert RH => T. See PROSHKA_VERDICT_NOESCAPE_2026-10-30.md §§3,6.

## 1. An anchored entropy really can forbid escape

Gram-Schmidt the fixed dense even derivative family to obtain a fixed ONB
(e_j) starting at j=0, with finite initial spans contained in fixed jets.
Set p_m,j=|<f_m,e_j>|^2. Parseval gives sum p_m,j=1. These are NOT the saved
weights of projected h in the changing eigenbasis of K_m.

Fix q_j=2^(-j-1), independently of m, and define D_m=D(p_m||q).
For t=(log 2)/2 and each bounded test g_N(j)=t min(j,N), the entropy inequality is

    D_m >= E_p[g_N] - log E_q[exp(g_N)].

This follows from nonnegativity of relative entropy to the tilted probability
q exp(g_N)/E_q exp(g_N). Let N increase. Since

    E_q exp(tj) = (1/2)/(1-1/sqrt(2)),

a uniform bound D_m<=C implies

    E_p[j] <= (C + 0.5347999967395702)/0.34657359027997264 =: B,
    sum_{j>R} p_m,j <= B/(R+1).

Choose one R with R+1>=2B: the fixed jet retains at least half the mass.
The same argument works if the bound holds only on an unbounded subsequence.
Thus uniform anchored KL is a sufficient supplier for T.

When the separate terms are finite, the balance is

    D(p||q) = (log 2) E_p[j] - H(p) + log 2,
    H(p) = -sum p_j log p_j.

Do not use this expansion as infinity minus infinity. The truncated-test proof
above does not need that manipulation. The location price opposes dispersion;
neither term has been identified with the literal prime contribution.

Negative controls:
- p=delta_M has H=0 but escapes every fixed span; D=(M+1)log 2 diverges.
- f_M=(e_0+e_M)/sqrt(2) retains half its mass in e_0, so T holds, yet
  D=(M/2)log 2 diverges for M>=1. Uniform KL is STRONGER than necessary.
- A reference q depending on m and following p_m makes D=0 even during escape.
  The reference, basis and normalization must be fixed before looking at m.

Missing source input: a uniform bound on D_m. The present NOESCAPE (6.5)
controls a Fourier logarithmic moment only by O(sqrt(m) log m). It supplies
neither this fixed-jet moment nor a uniform joint position/frequency budget.
This is an exact sufficient interface, not a gained estimate.

## 2. What the actual prime contribution does

MARKOV §6.2, equations (6.4)-(6.9), already supplies a source-specific positive
jump energy E_h=E_arch+E_prime, probability measure

    dmu = (1/2) cosh(x/2) h(x) dx,     tau(x)=tanh(x/2),

and the exact PAPER identity (all prime powers and both pole terms retained)

    k[hF] = E_h(F) - 8 Var_mu(F) - 8 |int tau F dmu|^2.

Every jump conductance in both E_arch and E_prime is nonnegative.
Polarizing this energy gives, for positive densities rho with finite integrals,

    E_part(rho,log rho) >= 0,

since (a-b)(log a-log b)>=0 for positive a,b at each jump.
IF this form is realized by a conservative reversible Markov semigroup with
generator -A and the required differentiability/domain conditions, then

    d/dt Ent_mu(rho_t) = -E_h(rho_t,log rho_t)
                       = -I_arch(rho_t)-I_prime(rho_t) <= 0.

The two pieces have the SAME entropy-dissipation sign in this representation.
This does not exclude another useful corrected functional. It excludes treating
these two particular positive jump pieces as automatic opposite entropy flows.
No semigroup construction is asserted here. Its auxiliary time t would not be
window size m, and its density would not automatically track f_m or K_m.

## 3. A tempting log-Sobolev route exposes the exact price

Suppose one proves Ent_mu(F^2)<=E_h(F)/4 on a domain allowing constants and
bounded perturbations 1+epsilon g (and all necessary limiting operations).
Here Ent_mu(s)=int s log(s/int s dmu) dmu.
For real bounded g,

    Ent_mu((1+epsilon g)^2) = 2 epsilon^2 Var_mu(g)+o(epsilon^2),
    E_h(1+epsilon g) = epsilon^2 E_h(g).

Hence that inequality implies E_h(g)>=8 Var_mu(g).
For even g the tau term vanishes: this recovers precisely the unpaid even
inequality in MARKOV (6.9), not a weaker free supplier. For general g it does
not yet pay the extra 8|int tau g dmu|^2. A weaker log-Sobolev constant or a
theorem only for another domain cannot be silently substituted.

## 4. Numbers from our existing data (nats; diagnostic only)

Input: ../thetagrade_2026-10-28/w0_monotone_dps100.jsonl and
w0_monotone_dps120_m28_36.jsonl. No eigenproblem was rerun.

| m | saved w0 | binary H(w0,1-w0) | -log w0 |
|---|---:|---:|---:|
| 8 | 0.999688977707 | 0.002822680 | 0.000311071 |
| 16 | 0.998437510548 | 0.011657255 | 0.001563711 |
| 22 | 0.998274961122 | 0.012699120 | 0.001726528 |
| 28 | 0.998340827133 | 0.012278885 | 0.001660551 |
| 36 | 0.998522137951 | 0.011108231 | 0.001478955 |

Binary H tends to zero both at w0=1 and w0=0: it cannot forbid escape.
-log w0 does detect losing this particular overlap, but its uniform boundedness
is just w0>=c restated. No mechanism is gained by renaming it entropy.
Saved w0 uses normalized projected h; its conversion to the fixed h pairing
requires the known strong projection convergence. The three-component jet fits
are nonorthogonal least-squares coordinates, not probability weights. Saved
alignment cosines are not full eigenvectors. Full fixed-basis entropy cannot
be recovered from these files; omitted mass has not been assigned zero.

## Decision and next test

The useful question is now narrower: derive from the actual source an inequality
that controls loss of a fixed compact component. Anchored entropy is one stronger
candidate; a direct compact-observable lower bound is cheaper (NOESCAPE L18).
We have no literal m-evolution law whose entropy difference has a known sign.
The next existing source-resolved test remains NOESCAPE §11: independent F/X
decomposition with relative error control on a retained m=16 or 20 cell. It can
distinguish negligible exterior coupling from signed cancellation before one
guesses a compensating functional. It cannot itself certify a cofinal law.

Shelf check: ask.sh --defer-external 'relative entropy' returned INCOMPLETE
(q3_docs freshness validation failed); no absence or literature exhaustion is
claimed. Local MARKOV/NOESCAPE sources were read directly. No new external
supplier is admitted by this note.

Independent bounded read-only check: entropy_data reviewed the KL truncation
proof, constants, stronger-than-T counterexample, conditional dissipation sign,
and log-Sobolev linearization; no algebraic defect found. The reviewer did not
author these arguments. This does not audit all MARKOV/NOESCAPE premises or
establish any source estimate. No source gain or route closure is claimed.

Follow-up after dispatch: ENTROPY_CUBIC_TEST_2026-10-30.md proves, with
an independently checked Arb cubic sign and PAPER domain passage, that the
sharp global LSI suggested in section3 is false on even compact tests. The
linearization in this first pass remains correct; it was only a hypothetical
supplier. The weaker sharp Poincare inequality remains open.
