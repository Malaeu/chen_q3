# THREE_LOBE_PREFLIGHT — CHAIN_SIGNED_NULL_MEAN_TRANSFER_PREFLIGHT (§8.4 / C25)

**Result: `CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR` — certified positive floor.**
`lam_min(Q_7,G_7) = 1.7443269450324643 ± 1e-18` ≥ 1/100; no negative upper witness. Registered event
`P_CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR` (prior 0.65): **CONFIRMED**.
`[DIAGNOSTIC_NEVER_A_PROOF]` — one frozen finite cell; it does **not** discharge R8 (§5.3), and §8.4
forbids enlargement without a candidate signed mean/complement inequality (§8 below).

Executor: Claude (Linux body). No sub-agents. Nothing committed. Scripts `tl_{core,quad,build,
kernel,analyze,check_direct,check_fourier,certify,envelope,report}.py` in
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe/`;
scratch `/home/chirurgie/.claude/jobs/4b35770d/tmp/three_lobe/`.

## 1. Conventions (frozen, taken verbatim from (C1))
`A(t)=e^{-t/2}/(1-e^{-2t})`, `c_A=gamma+log(8pi)+pi/2 = 5.372183419225665582233`,
`w_n=Lambda(n)/sqrt n`, `U_t f(x)=f(x-t)`, `C_f(t)=Re int conj(f(x))f(x+t)dx`,
`M_pm(f)=int f e^{pm x/2}`, `D(f)=int_0^inf A(t)||U_t f-f||^2 dt`,
`Q(f)=D(f)-c_A||f||^2-2 sum_{n>=2} w_n C_f(log n)+2Re{M_+(f) conj(M_-(f))}`.
Hermitian polarization, **antilinear in the first argument**, all nine generators real:

    D(f,g)     = int_0^inf A(t)[ 2<f,g> - <f,U_t g> - <f,U_{-t} g> ] dt
    Prime(f,g) = - sum_n w_n [ <f,U_{log n} g> + <f,U_{-log n} g> ]
    Pole(f,g)  = conj(M_+(f)) M_-(g) + conj(M_-(f)) M_+(g)

Second channel: `Arch = D - c_A<.,.> = (1/2pi) int q_inf conj(f^)g^`,
`q_inf(xi)=Re psi(1/4+i xi/2)-log pi` (identity verified in PROFILES_INDEPENDENT_CHECK §1).
Normalization was never adjusted after seeing a number. Packet:
`delta=(log3-log2)/8=0.050683138513520547747`, centres `x_i in {0,log2,log3}`,
`eta(x)=exp[-1/(1-(2x/delta)^2)]` on `|x|<delta/2`, `phi_0=eta`, `phi_1=eta'`,
`phi_2=eta''-eta/4`, `f_ij=U_{x_i}phi_j`, index `3p+j`.

## 2. Moment rows, exact rank, exact seven-dimensional kernel
`m_eta = M_pm(eta) = 0.011251642852030559757`. The by-parts identities `M_pm(phi_1)=∓m_eta/2`,
`M_pm(phi_2)=0` hold to working precision (residuals `-1.3e-51`, `-2.7e-48`; `phi_2` moment-integrand
scale ≈ 17). After removing `m_eta` the two rows are algebraic:

    r_+ = e^{ x_p/2}(1, -1/2, 0),   r_- = e^{-x_p/2}(1, +1/2, 0),   e^{x_p/2} in {1, sqrt2, sqrt3}.

`rank[r_+; r_-] = 2` (sympy, exact). With `u_p=a_p-b_p/2`, `v_p=a_p+b_p/2` the constraints split:
`sum_p e^{x_p/2}u_p=0`, `sum_p e^{-x_p/2}v_p=0`. **Exact kernel basis** over `Q(sqrt2,sqrt3)`
(sympy: `rank K = 7`, `r_+K = r_-K = 0` symbolically):

    B1 = z (x) (1,0,0),  z = (-1, 2sqrt2, -sqrt3)   [the mean direction (C2)]
    B2 : u=(sqrt2,-1,0), v=0     B3 : u=(sqrt3,0,-1), v=0     B4 : u=0, v=(1,-sqrt2,0)
    B5,B6,B7 = e_{0,2}, e_{1,2}, e_{2,2};   a=(u+v)/2, b=v-u.  No floating projection anywhere.

## 3. What the form actually contains on this packet
* **Gram.** All centre gaps exceed `delta` (`log(3/2)=0.4055>delta`), so `G=I_3 (x) g` is block
  diagonal, `g_jk=int phi_j phi_k`; `g_01=g_12=0` by parity (numerically `5e-53`).
  `g_00=0.0033726111485069895`, `g_11=16.162655777266285`, `g_02=-16.163498930053412`,
  `g_22=665739.49849059278`. `g>0`, hence `G>0` and `G_7=K^T G K>0` (ball-LDL^T certified below;
  `G_7` eigenvalues `0.0357 … 6.657e5`).
* **Archimedean.** Diagonal and cross blocks at all lags `x_i-x_j in {0,±log2,±log3,±log(3/2)}`.
  The lag `log(3/2)` carries a genuine cross entry (`Arch[(log2,phi_0),(log3,phi_0)]=-1.8625048e-4`)
  and **no prime atom** (entry exactly `0`).
* **Primes.** Autocorrelation support `|t| <= log3+delta = 1.14929542718163`;
  `log4 = 1.38629436111989 > 1.14930`, so `n=4` is **inactive** — verified, not assumed
  (`n=2..39` scanned, only `2,3` hit). Exactly `Prime = -(Adj (x) g)`,
  `Adj=[[0,w_2,w_3],[w_2,0,0],[w_3,0,0]]`, `w_2=log2/sqrt2=0.490129071734274`,
  `w_3=log3/sqrt3=0.634284100597564`; assembled entries reproduce `-w_n g_00` to 17 digits.
* **Pole, before restriction.** `Pole=m_eta^2(r_+r_-^T+r_-r_+^T)`, rank 2, eigenvalues
  `{-2.400048624e-4, +8.097024633e-4}` and seven zeros — indefinite, kept in full.
  `K^T Pole K = 0` to `7e-53`; direct quadrature on a synthesized kernel test gives
  `M_+=-8.0e-43`, `M_-=-3.4e-43`.

## 4. Restricted form, eigenvalues, minimiser

Kernel basis rescaled to unit G-norm (generalized eigenvalues are congruence-invariant). `G_7`:

    1.000000 -0.005107  0.000000 -0.006019  0.098471 -0.278519  0.170557
   -0.005107  1.000000  0.707107 -0.942711 -0.002012  0.001422  0.000000
    0.000000  0.707107  1.000000 -0.499948 -0.002134  0.000000  0.001232
   -0.006019 -0.942711 -0.499948  1.000000 -0.001422  0.002012  0.000000
    0.098471 -0.002012 -0.002134 -0.001422  1.000000  0.000000  0.000000
   -0.278519  0.001422  0.000000  0.002012  0.000000  1.000000  0.000000
    0.170557  0.000000  0.001232  0.000000  0.000000  0.000000  1.000000

`Q_7`, same basis:

    1.813160 -0.010747 -0.002103 -0.011018  0.312897 -0.853139  0.430406
   -0.010747  3.351997  2.547512 -3.214524 -0.006511  0.005096  0.001279
   -0.002103  2.547512  3.439222 -1.974505 -0.006947  0.001043  0.004913
   -0.011018 -3.214524 -1.974505  3.351997 -0.005096  0.006511  0.000899
    0.312897 -0.006511 -0.006947 -0.005096  4.130302 -0.490129 -0.634284
   -0.853139  0.005096  0.001043  0.006511 -0.490129  4.130302 -0.000000
    0.430406  0.001279  0.004913  0.000899 -0.634284 -0.000000  4.130302

Raw diagonals: `G_7=(0.040471334, 48.490497, 64.653996, 48.490497, 6.6573950e5 ×3)`,
`Q_7=(0.073380992, 162.54001, 222.35942, 162.54001, 2.7497052e6 ×3)`. Eigenvalues `lam(Q_7,G_7)`:

    1.744326945032464317   2.088846604265752629   2.889867940906252605   3.330710078216047647
    3.691575796290293473   4.206923888444944063   4.937364930508410870

Minimiser (G-unit coordinates on `B1..B7`):
`(-1.046160, -0.068091, +0.014982, -0.056243, +0.049824, -0.150678, +0.071556)`, with
`cos_G(v_min, z) = 0.986396`. **The softest direction of the packet is, to 98.6 %, the newly freed
mean direction (C2)** — the object §2.1 exposed — and it is still bounded below by `1.744`.
Split at the minimiser: `D=7.070414`, `Arch=1.698231`, `Prime=+0.046096`, `Pole=-7.0e-53`.
Context: on the **unrestricted** nine-dimensional span `lam(Q,G)` runs `1.012410732 … 5.013476297`,
so the packet is positive even before the pole rows are imposed.

## 5. The mean direction z alone, and (C7)

`f_z = sum_p z_p eta(.-x_p)`, `||f_z||^2 = 12 g_00 = 0.040471333782083874`.
Per unit `||f_z||^2`: `D = 7.137396120417071536`, `Arch = D - c_A = 1.765212701191405953`,
`Prime = +0.04794701207529682124`, `Pole = -6.4e-53` (zero: z is in the kernel),
**`Q = 1.813159713266702775`**.

`log(4/3)/6 = 0.04794701207529682124`. Deviation `3.6e-46`. **Прошka's (C7) is confirmed exactly**:
`(-2w_2 z_0 z_1 - 2w_3 z_0 z_2)/||z||^2 = (2log3-4log2)·(-1)/12 = log(4/3)/6 > 0`, and the physical
`g_00` cancels, so the identity holds in the `G`-normalization too. The free mean direction is a
**positive** prime direction; the whole of `Q(z)` is positive, driven by the archimedean part.

## 6. Two channels, and they agree

**A (primary, spatial).** Cross blocks reduced exactly to a 2-D integral over the support square,
`D_jk(Delta) = -int int phi_j(u)phi_k(v) A(Delta+u-v) du dv` (`Delta >= log(3/2) > delta`, no
singularity). The diagonal block uses `A(t)=1/(2t)+A_reg(t)` and integrates the **cancelled**
`2[sigma_jk(0)-sigma_jk(t)] = O(t^2)`, never divergent pieces; beyond `t=delta` the closed form
`int_delta^inf A = artanh(y)+arctan(y)`, `y=e^{-delta/2}` (`=2.9569836711243785`), so there is no
tail truncation. Bump integrals use the `tanh`-map trapezoid (both endpoints infinitely flat →
doubly exponential decay → spectral accuracy, checked at four settings against the exact moments).

**B (Fourier).** `Arch = (1/2pi) int q_inf conj(f_i^) f_j^ dxi`. Transforms `F_j(xi)` computed
**directly per profile** (never as `-(xi^2+1/4)E(xi)`, which loses conditioning) by zero-padded FFT,
`dx=delta/512`, `N=2^25`, `dxi=0.00189`, Simpson in `xi`. The Gram recomputed from the same
transforms by Plancherel is the convergence gauge (exact value known):

| `xi_max` | 4 000 | 8 000 | 15 000 | 25 000 | **31 000** |
|---|---|---|---|---|---|
| `Arch` dev (G-scaled) | 1.43e-3 | 2.66e-6 | 4.66e-10 | 1.13e-13 | **8.88e-14** |
| Gram dev (G-scaled) | 2.18e-4 | 3.68e-7 | 5.95e-11 | 2.97e-15 | **1.75e-16** |

Two structurally different representations of the archimedean term — the `A(t)` shift energy with
its cancelled contact, and the digamma multiplier — agree to `9e-14` in the `G`-norm (float64 floor).

**C (end-to-end, independent code path).** For two concrete kernel tests `Q(f)` was evaluated
straight from (C1): `f` synthesized on the union of the three lobes, `||U_t f-f||^2` from its own
autocorrelation, `C_f(log n)` and `M_pm(f)` by direct quadrature — no block decomposition, no `rho`
machinery, no lag bookkeeping. `||f||^2` agrees to `1.3e-37` / `4.7e-28`; `Q` to `5.8e-8` / `7.8e-6`
relative (limited by that check's own coarse `t`-panels). It independently returns
`C_f(log n)=0` for `n=4,5,7,8,9` and `M_pm(f)=O(1e-43)`.

## 7. Coverage ledger and error ledger

| item | treatment |
|---|---|
| six support endpoints `x_i ± delta/2` | `tanh`-map fixed points; integrand `~exp(-cosh^2 y)`; truncation at `Y=4.5` leaves `<exp(-2025)` |
| correlation endpoints `x_i-x_j ± delta` | cross blocks on the support **square** (lag endpoints automatic); diagonal block on the exact overlap `[-delta/2, delta/2-t]` |
| archimedean contact at `0`; `t>=delta` tail | `A=1/(2t)+A_reg`, cancelled `O(t^2)` integrand, `B(t)/t` bounded; tail in closed form `artanh(y)+arctan(y)`, no truncation |
| prime shifts `log2`, `log3`; pole rows | from `rho_jk(0)=g_jk`, checked against `-w_n g_jk` to 17 digits, `n=2..39` scanned; pole rows exact algebraic, kernel residual `7e-53` |
| Fourier tail | `xi_max = 31000`, gauge deviation `1.75e-16` |

**Entry enclosures.** Two independent builds — (`dps=50`, `Y1=4.5/h1=0.02`, `Y2=4.0/h2=0.05`,
`Nt=40/tpan=8`) vs (`dps=60`, `Y1=5.0/h1=0.015`, `Y2=4.2/h2=0.035`, `Nt=56/tpan=12`) — differ in
`G`-scaled entries by `9.2e-49` (`G`) and `5.8e-20` (`Q`). Ball radii = **100×** those deviations
(floor `1e-30`); every step from there is rigorous Arb ball arithmetic (`prec=300`): exact
`sqrt2`,`sqrt3` kernel restriction, then LDL^T.

    G_7 positive definite (ball LDL^T)                       : TRUE
    certified   Q_7 - (1/100) G_7  >= 0                      : TRUE
    certified   Q_7 - c G_7 >= 0  for c = 1.744326945032464316193144
    certified   lam_min <= [1.744326945032464317 +/- 2.73e-19]   (ball Rayleigh at the minimiser)
    envelope width 8.07e-19   <<   1/1000  (the §8.4 tolerance)

Caveat, plainly: the entry radii rest on a quadrature-refinement ledger (two builds, two independent
channels, exact identities as gauges), not a machine-verified quadrature enclosure; everything
downstream of the radii is rigorous ball arithmetic.

**Mandatory 2×2 gluing detector.** `A=B=1`, `E=2`: Schur `S(0)=A-E*B^{-1}E=-3`. Under the same
envelope logic the ball LDL^T **fails to certify** `M>=0` and even `M-(1/100)I>=0`, and the certified
upper Rayleigh value at the exact witness `(1,-1)` is `-1 < 0` — **rejected**, as §5.1 demands,
before any positive number above is credited.

## 8. Decisions

* `lam_min(Q_7,G_7) >= 1/100` — **YES**, certified; in fact `>= 1.7443269450324643161`.
* `CHAIN_LITERAL_NEGATIVE_UPPER_WITNESS` — **not issued**. No normalized vector in the exact
  seven-dimensional kernel has a certified negative upper `Q`; the minimum is `+1.744`. Conventions
  re-checked twice (prime sign against (C7) to 20 digits; archimedean sign and normalization against
  the independent digamma channel to `9e-14`; pole sign against PROFILES §1). Nothing contradicts RH.
* `CHAIN_MEAN_OR_MIXED_SOURCE_BOUND_UNRESOLVED` — **not issued**; the stronger local floor
  `Q >= ||v||^2/100` on this cell is the same statement and also holds.

**What this does not do.** One frozen finite cell, one profile family. It does not discharge R8
(`S_n(1/n) >= 0` for every `n`), it is not a mechanism, and §8.4 forbids automatic enlargement.
The candidate whole-class inequality this run suggests — a *candidate*, unproved — is that the free
mean direction is not the enemy: it is at once the softest direction of the cell (`cos_G=0.986` with
`v_min`) and a direction whose prime part is **positive** and exactly computable, `log(4/3)/6`, with
`g_00` cancelling. The shape that would cover the omitted profiles is
“archimedean gap on the mean direction ≥ the mixed coupling to its complement, uniformly in the
number of centres”. Nothing above establishes it.

## 9. Runtime and labels

primary build (dps 50) 45.5 s · refinement build (dps 60) 138.5 s · Fourier channel 68 s ·
end-to-end channel 22 s · restriction + eigenvalues 0.6 s · ball certification + envelope 1.9 s;
≈ 5 min wall clock, one core. mpmath 1.3.0 / numpy 2.3.5 / scipy 1.16.3 / sympy 1.14.0 /
python-flint 0.8.0 (Arb).
`[DIAGNOSTIC_NEVER_A_PROOF]` `[FINITE_CELL]` `[ARB_BALL_CERTIFIED downstream of the entry radii]`
