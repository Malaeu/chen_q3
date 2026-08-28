# Pellegrino–Teixeira, arXiv:2608.16584 (Aug 2026) + relayed Hamming-cube note — usage cards

Pulled 2026-08-28 by `./paper.sh 2608.16584`. The **owner also relayed an unsigned
note** "Polynomial growth of Bohnenblust–Hille constants on the Hamming cube",
which adapts [1] to `{±1}^n` and proves `C_m <= K m^27`, `tilde C_m <= K m^28`.

**Provenance flag.** The relayed note carries **no author and no arXiv id**. It is
treated here as a readable exposition of the method, not as a citable source. Its
reference [1], Pellegrino–Teixeira arXiv:2608.16584, is real and was verified:
"Polynomial growth of complex polynomial Bohnenblust–Hille constants", abstract
confirms `D_m <= K m^{B_0}` replacing `exp(O(sqrt(m) log m))`, `D_m = o(m^mu)` for
`mu > 2.47`, and `liminf D_m > 1.27`.

## 1. What the machine actually is

Read in full. Six moving parts, in the order they are used:

1. **Bonami–Beckner hypercontractivity** replaces Weissler on the cube:
   `||g||_2 <= ((k+1)/(k-1))^{e/2} ||g||_{q_k}` for Walsh-homogeneous degree `e`.
2. **Mixed-norm interpolation** (their Lemma 4): `||a||_{q_m} <= X_d(a)^{d/m} Y_e(a)^{e/m}`
   for `m = d + e`. Pure `l_p` interpolation plus Minkowski — **no holomorphy**.
3. **Vertex maximum**: for multilinear `f`, `||f||_{L^inf([-1,1]^n)} = ||f||_{L^inf({±1}^n)}`,
   by convexity in each coordinate separately.
4. **Fair 2-colouring plus Hoeffding capture**: split `[n] = X ⊔ Y` at random; the
   `x`-degree of a character `chi_S` is `Bin(|S|, 1/2)`, so a constant fraction of
   the mass lands in a prescribed bidegree band with probability
   `1 - 2 exp(-2(1/2 - a)^2 r)`.
5. **Entropy contraction**: with a tunable weight exponent `B`, the band's
   contribution carries `exp(-(B + 1/2) h(a))`, `h(a) = -a log a - (1-a) log(1-a)`.
   Choosing `a = 1/6`, `B = 5`, `R = 12` makes the contraction factor `c_12 < 1/2`.
6. **Markov brothers' inequality on slices** for the low-degree head:
   `||g^{=r}||_inf <= Lambda_{m,r} ||f||_inf` with
   `Lambda_{m,r} = T_m^{(r)}(1)/r! = m^2(m^2-1)...(m^2-(r-1)^2)/(r!(2r-1)!!)`,
   which is `<= m^{2r}/(r!(2r-1)!!)`.

**The architecture, which is the real content.** Define a *weighted* quantity
`Gamma(f;B)` with weights `r^{-2B}` over the degree layers, prove
`Gamma <= (head) + c Gamma` with `c < 1`, and conclude `Gamma <= 2 (head)`. The
bound is never proved directly; it is proved to **self-improve**. That is the
"fixed-ratio / weighted bootstrap" the abstract names.

## 2. What it gives us

**Not the inequality.** BH bounds a coefficient `l^q` norm **by** a sup norm.
Every open item on our front needs the opposite direction — a sup bound from
coefficient data — so the theorem itself does not apply. The cube/Walsh setting
is also not ours: our carrier is an integer mode lattice with a Cauchy kernel, not
`{±1}^n` with Walsh characters, and there is no product measure to hypercontract
against.

**The architecture, possibly.** Our route has failed four times in a row by trying
to prove an envelope *directly*: the Stieltjes majorant, the observability
infimum, the Schur effective source, the central mass. Not one of those attempts
was structured as a self-improving inequality. The `Gamma <= head + c Gamma` shape
is a genuinely different move and we have never used it. Whether any of our open
quantities admits such a splitting is an open question and is **not** claimed
here.

**Markov on slices has a genuine relative in our setting.** Their head bound is
"extract a low-degree coefficient, pay `T_m^{(r)}(1)/r!`". Our transforms are
entire of exponential type `L/2`, so the corresponding classical tool is
**Bernstein / Plancherel–Pólya**, not Markov. That is worth recording because it
is the tool `R1_A` actually wants, and it is not the one in this paper.

## 3. A caution this reading produced, and it bears on R1 directly

Checking whether a coefficient-to-sup bound could give `SelectedRawLocallyBounded`
forced a look at the object. From `D0CanonicalApproximation.lean:39`,

    rawFplus D i z = proposition59RawTransform (logLength i) (modeSet i) (D.kTrial i) (-z),

so `rawFplus` carries the full numerator `2 sin(z L/2)` and hence
`|rawFplus(z)| ~ e^{L |Im z|/2} = m^{|Im z|/2}` off the real axis. The corridor's
**normalized** object is one line below:

    bareTransform D i z = exp(i z L/2) * rawFplus D i z,

whose multiplier has modulus `m^{-Im z/2}` — exactly cancelling that growth in the
**upper** half plane and doubling it in the lower.

So a uniform compact bound stated on `rawFplus` over an arbitrary compact in the
strip is asking for boundedness of an object of exponential type against its own
type. Either the intended compact is real, or the intended object is
`bareTransform`, or the hypothesis is stronger than the geometry supports. This is
a question for the R1 transaction and is raised as a caution, not as a defect
claim — I have not read how `SelectedRawLocallyBounded` is consumed downstream.

## 4. Variable correspondence

    their m (degree)             <->  no direct analogue; our m is the prime cutoff
    their n (number of variables)<->  our carrier size 2N+1
    their ||f||_inf              <->  sup over a fixed compact, not over a cube
    their weight exponent B      <->  no analogue yet; this is the tunable knob
    their h(a) entropy           <->  no analogue; there is no random colouring in our setting
    their Markov Lambda_{m,r}    <->  Bernstein/Plancherel–Pólya for exponential type L/2

## 5. Not read

The source paper `2608.16584` itself (only its abstract, verified by fetch); the
companion `2608.16217` on quasipolynomial bounds; the phase-preserving
decomposition and spectral-projection steps named in the abstract, which are the
parts the relayed note explicitly *replaces* rather than reproduces.

## 6. Standing status

`REFERENCES.md` line for `2608.16584` remains `NEEDS_CARDS` until the source paper
itself is read; this card documents the relayed note and the verified abstract
only.
