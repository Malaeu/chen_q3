# `PO2` cross-sign bulk exactness (2026-03-16)

## Status

First post-`P1` direct theorem receiver in lane `A`.

Reactivated on 2026-03-20 as the first undischarged proof-critical gate on the
actual path to RH.

The upper bridge `H2^f -> H3^f -> H4^f` is now packaged tightly enough at the
theorem-shell level, but it is still conditional on the unresolved `H1^f`
input. So the honest blocker is no longer route description. It is whether the
cross-sign tail block is bulk-exact in the strong sense required by `PO2`.

`P1` already froze:

- the tail defect object `\mathcal D_{a,N}`;
- its sign-block split;
- Hermitian recovery of `(-+)`, `(--)`.

So the next honest question is narrower:

```tex
\text{does the cross-sign tail block carry any genuine bulk residue?}
```

## Why this is next

The whole asymmetry of the current route depends on one strong claim:

- `(+,-)` is the calibration block;
- `(++)` is where any same-sign boundary term should live.

That asymmetry does not become theorem-grade until the cross-sign block is
shown to be bulk-exact before any boundary/cap discussion.

## Exact target

The `PO2` receiver should be written in the following equivalent forms.

### PO2a. Bulk vanishing statement

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

### PO2b. Boundary/cap-only remainder statement

Equivalently,

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}.
```

This is the strongest acceptable `PO2` output before `PO3`.

It says:

- no genuine bulk mismatch survives in `(+,-)`;
- whatever remains must already belong to the later
  boundary/cap classification problem.
- if even this weaker boundary/cap-only form fails, the current `H-bridge`
  theorem shape is killed and must be written to
  `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md` before rollback to `PSD-pd`.

## Worker-ingested refinement

The first worker pass on `P2` confirmed the right asymmetry and sharpened one
important policy decision:

- the **primary** `PO2` lemma must stay pure:
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- the **fallback** form must already name both admissible remainder channels:
  boundary and cap;
- compression must stay out of `PO2` entirely and remain deferred to `PO6`.

So the correct theorem posture is:

```text
prove pure bulk vanishing in PO2;
name boundary/cap in the equivalent fallback;
do not let compression or same-sign language leak into this stage.
```

## Strongest existing anchors

### 1. Old strongest filtered thesis

`Main_closure.tex` already records the finite filtered receiver

```tex
M^{+-}(a)=\kappa(a)\widetilde Q_{M,N}^{+-}+F_a^{+-},
```

with the explicit remark:

```text
no extra section-boundary defect once \widetilde Q_{M,N} is used.
```

So `PO2` is not inventing a new theorem shape. It is isolating the bulk part
of the old strongest filtered thesis.

### 2. Exact four-block filtered bulk formulas already exist

The four-block note already freezes

```tex
M_{mn}^{\sigma\tau}(a)
=
W(\psi_n^\sigma[a]*\widetilde{\psi_m^\tau[a]}).
```

So the cross-sign bulk is not heuristic. It is already an exact filtered
operator expression.

### 3. Raw mismatch is not the issue here

The dead raw identity

```tex
w_{rs}(a)=\kappa(a)q_{rs}
```

does not obstruct `PO2`, because `PO2` is already formulated on the filtered
tail object `\mathcal D_{a,N}^{+-}`, not on the raw Toeplitz-vs-Weil entries.

## Research synthesis for this blocker

Local embedding search on `q3_docs` keeps returning the same four anchors:

- `h1_four_block_bulk_2026_03_08.md` as the exact filtered bulk formula layer;
- `Main_closure.tex` as the strongest older finite receiver for exact `(+,-)`;
- `h1_raw_entry_reduction_2026_03_08.md` as the place where raw mismatch is
  explicitly separated from the filtered target;
- `IMPLEMENTATION_PLAN.md` / `PROJECT_ORCHESTRATOR.md` as confirmation that
  the direct filtered bulk identities are still the live mathematical route.

External sanity-check from the finite-section / Toeplitz-Hankel side does not
push against this picture: the natural place for any non-bulk remainder is a
boundary/finite-section channel, not a mysterious floating bulk defect. So the
working `PO2` posture stays aggressive:

```tex
\text{either cross-sign bulk vanishes, or the current reset is wrong.}
```

## Proof-facing reduction

The note is only useful if it shrinks to a short local packet.

### PO2.1. Entrywise filtered bulk receiver

For `n,m>N`, freeze the cross-sign filtered entries as

```tex
M_{mn}^{+-}(a)
=
\left\langle G_g[a]\phi_n^+[a],\phi_m^-[a]\right\rangle
=
W(\psi_n^+[a]*\widetilde{\psi_m^-[a]}).
```

This is the exact Suzuki-side bulk object that must be compared to the
corresponding entries of `\kappa_{+-}(a)Q_\infty^{+-}`.

### PO2.2. Bulk exactness lemma

The first real theorem attempt inside `P2` should be the tail-level statement

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

Equivalent receiver:

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}.
```

That is the narrowest acceptable theorem output before `PO3`.

### PO2.3. Bulk route-kill lemma

Any statement of the form

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+ \cdots,
\qquad
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0,
```

with no operator reclassification into boundary or cap, is not a weakened win.
It is the explicit route-kill event for the current boundary/cap reset.

## Compact proof plan

The next real attack on `PO2` should stay brutally short.

### Step 1. Freeze the exact cross-sign tail object

Work only with

```tex
\mathcal D_{a,N}^{+-}
=
P_{+,N}\mathcal D_{a,N}P_{-,N},
```

not with finite-section diagnostics and not with the same-sign block.

### Step 2. Expand the filtered Suzuki side entrywise

Use only the exact filtered bulk formulas from the four-block note:

```tex
M_{mn}^{+-}(a)
=
\bigl\langle G_g[a]\phi_n^+[a],\phi_m^-[a]\bigr\rangle
=
W(\psi_n^+[a]*\widetilde{\psi_m^-[a]}).
```

So the left-hand side is already a genuine filtered bulk object.

### Step 3. Expand the Q3 side through the pulled-back block

Compare against

```tex
\kappa(a)\widetilde Q_{N}^{+-}
\quad\text{or finite shadows }\quad
\kappa(a)\widetilde Q_{M,N}^{+-},
```

using only the frozen two-sided filter `\Delta_N`.
The key point is that both sides must be read through the same four-term
stencil induced by the two-sided adjacent-packet filter.

### Step 4. Kill the common bulk stencil first

The first theorem attempt is not “classify all remainders”, but:

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

So the shared filtered stencil must cancel before any cap analysis.
If it does not, the route is not weakened; it is killed.

### Step 5. Name the only admissible remainder channels

After bulk cancellation, the only allowed output is

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
\,
\mathcal D_{a,\mathrm{cap}}^{+-}.
```

No compression term belongs here.
No same-sign operator belongs here.
No unnamed matrix residue belongs here.

### Step 6. Immediate handoff

If bulk vanishing lands, the next theorem attempt is forced:

```tex
PO3:\qquad
\mathcal D_{a,\partial}^{+-}=0.
```

If bulk vanishing does not land, do not climb back to `H2/H3/H4`.
Treat the current `H`-bridge as still conditional and unresolved.

## Exact lemma package for the next attack

The next proof-facing move should no longer say “work on `PO2`”.
It should say exactly which three local lemmas we are trying to land.

### L1. Common filtered stencil on the Suzuki side

From `Main_closure.tex`, Proposition `prop:H1-raw-entry-reduction`, we already
have for `N<n,m\le M`:

```tex
M_{mn}^{+-}(a)
=
w_{m,-n}(a)
+ w_{m+1,-n}(a)
+ w_{m,-(n+1)}(a)
+ w_{m+1,-(n+1)}(a).
```

This is the exact four-term filtered stencil on the Weil/Suzuki side.
So there is no ambiguity left about what the cross-sign bulk object is.

### L2. Common filtered stencil on the Q3 side

From `Main_closure.tex`, Proposition `prop:H1-filtered-q-blocks`, we already
have:

```tex
\widetilde q_{mn}^{+-}
=
q_{m,-n}
+ q_{m+1,-n}
+ q_{m,-(n+1)}
+ q_{m+1,-(n+1)}.
```

So the pulled-back Q3 block is built from the exact same four-term stencil.
This is the key local reason `PO2` is even plausible.

### L3. Cross-sign bulk cancellation lemma

The real theorem attempt is now reduced to:

```tex
M_{mn}^{+-}(a)-\kappa(a)\widetilde q_{mn}^{+-}
```

for all tail indices `m,n>N`.

The cleanest target is:

```tex
M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}
\qquad (m,n>N),
```

which upgrades directly to

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

The only acceptable weaker output is that the whole residual operator already
belongs to the named boundary/cap channels.

### L3'. Explicit entrywise residual formula

Combining `L1` and `L2`, define the raw mixed residuals

```tex
\delta_{r,s}(a):=w_{r,s}(a)-\kappa(a)q_{r,s}.
```

Then the cross-sign filtered residual is exactly

```tex
R_{mn}^{+-}(a)
:=
M_{mn}^{+-}(a)-\kappa(a)\widetilde q_{mn}^{+-}
```

with the four-term representation

```tex
R_{mn}^{+-}(a)
=
\delta_{m,-n}(a)
+ \delta_{m+1,-n}(a)
+ \delta_{m,-(n+1)}(a)
+ \delta_{m+1,-(n+1)}(a).
```

This is the most concrete local target we currently have for `PO2`.

It is also the right reason not to resurrect the dead global raw identity:
we do **not** need each raw defect `\delta_{r,s}` to vanish.
We only need the specific cross-sign four-term stencil above to cancel, or to
collapse into named boundary/cap channels.

### L3''. Sharp local theorem fork

After `L3'`, the theorem fork becomes brutally explicit:

1. exact cancellation:
   ```tex
   R_{mn}^{+-}(a)=0 \quad (m,n>N);
   ```
2. structured fallback:
   the operator built from `R_{mn}^{+-}(a)` is already boundary/cap only;
3. route-kill:
   a genuine tail bulk contribution survives in this stencil.

### L3'''. Why the mixed block is the right first target

The formulas already show a special algebraic simplification in the cross-sign
channel.

On the Suzuki side, `Main_closure.tex` gives

```tex
M_{mn}^{+-}(a)
=
\frac{2\pi^2}{a^3}(-1)^{m+n}
\sum_\gamma
\frac{\sin^2(a\gamma)}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_n)(\gamma-\alpha_{n+1})}.
```

On the Q3 side, the explicit filtered Toeplitz term is

```tex
\widetilde a_{mn}^{+-}
=
a_{m+n}+2a_{m+n+1}+a_{m+n+2}.
```

So unlike the same-sign block, the mixed block is already naturally organized
by the combined index `m+n` and by a same-sign denominator pattern on the
Suzuki side.
This is exactly why `(+,-)` should be attacked before `(++)`: it has the
cleanest algebraic symmetry and the strongest chance of exact cancellation.

### L3''''. Exact filtered formulas on the Q side

The raw bilateral Q3 operator is already frozen in the project as

```tex
Q_\infty^{raw}=(q_{rs})_{r,s\in\mathbb Z},
\qquad
q_{rs}
=
A_{r-s}-\sum_j \lambda_j e^{2\pi i(s-r)\xi_j}.
```

On the positive and negative tail basis vectors
`e_n^+=z^n`, `e_n^-=z^{-n}` this gives:

```tex
q_{mn}^{++}
:=
\langle Q_\infty^{raw}e_n^+,e_m^+\rangle
=
A_{m-n}-\sum_j \lambda_j e^{-2\pi i(m-n)\xi_j},
```

```tex
q_{mn}^{+-}
:=
\langle Q_\infty^{raw}e_n^-,e_m^+\rangle
=
A_{m+n}-\sum_j \lambda_j e^{-2\pi i(m+n)\xi_j}.
```

After filtering by
` \Delta_+e_n^+=e_n^++e_{n+1}^+`,
` \Delta_-e_n^-=e_n^-+e_{n+1}^-`,
the pulled-back blocks become

```tex
\widetilde q_{mn}^{++}
=
2A_{m-n}+A_{m-n+1}+A_{m-n-1}
-\sum_j \lambda_j e^{-2\pi i(m-n)\xi_j}\lvert 1+e^{2\pi i\xi_j}\rvert^2,
```

```tex
\widetilde q_{mn}^{+-}
=
A_{m+n}+2A_{m+n+1}+A_{m+n+2}
-\sum_j \lambda_j e^{-2\pi i(m+n)\xi_j}(1+e^{-2\pi i\xi_j})^2.
```

So the mixed block on the Q side is a filtered Hankel-type block in the
combined index `m+n`, while the same-sign block stays filtered Toeplitz-type
in the difference index `m-n`.

### L3'''''. Sign-pure boundary lemma

Let

```tex
\mathcal H_N=\mathcal H_{+,N}\oplus\mathcal H_{-,N},
\qquad
P_+=\begin{pmatrix}I&0\\0&0\end{pmatrix},
\qquad
P_-=\begin{pmatrix}0&0\\0&I\end{pmatrix},
```

and let `\mathcal B` be the algebra generated by `P_+`, `P_-`,
the sign-separated filtered shifts `\Delta_+`, `\Delta_-`,
and operators acting only on the positive or only on the negative tail.
Then every `T\in\mathcal B` is block-diagonal:

```tex
T=
\begin{pmatrix}
T_{++}&0\\
0&T_{--}
\end{pmatrix},
```

hence

```tex
P_+TP_-=0,
\qquad
P_-TP_+=0.
```

Interpretation:

- any boundary defect produced only by moving tail projections or filtered
  shifts past sign-pure operators can contribute only to `(++)` and `(--)`;
- a genuinely mixed `(+,-)` boundary term cannot come from sign-pure boundary
  algebra alone.

### L3''''''. Structural consequence for `PO2`

Once the live defect is decomposed as

```tex
\mathcal D_{a,N}=H_{a,N}+C_{a,N},
```

with `H_{a,N}` the short-range boundary / commutator layer and `C_{a,N}` the
finite-dimensional cap, the sign-pure boundary lemma forces the mixed block
into the shape

```tex
\mathcal D_{a,N}^{+-}=C_{a,N}^{+-,\mathrm{cap}},
```

while the same-sign block is the natural home of the surviving boundary term:

```tex
\mathcal D_{a,N}^{++}=H_{a,N}^{\mathrm{ss}}+C_{a,N}^{++,\mathrm{cap}}.
```

So a non-cap mixed boundary term is not an admissible theorem output.
If one seems to survive, either the decomposition was misidentified or the
current filtered theorem shape is wrong.

### L3'''''''. Honest remaining brick

After `L1`–`L3''''''`, the whole `PO2` problem collapses to one explicit
comparison:

Define the raw mixed Weil block by

```tex
\Omega_{mn}^{+-}(a):=w_{m,-n}(a)=W(\chi_{-n}[a]*\widetilde{\chi_m[a]}),
\qquad m,n>N.
```

Then the already-frozen filtered cross-sign block is exactly

```tex
M_{mn}^{+-}(a)
=
\Omega_{mn}^{+-}(a)
+ \Omega_{m+1,n}^{+-}(a)
+ \Omega_{m,n+1}^{+-}(a)
+ \Omega_{m+1,n+1}^{+-}(a).
```

On the Q side, if we set

```tex
\Theta_{mn}^{+-}
:=
A_{m+n}-\sum_j\lambda_j e^{-2\pi i(m+n)\xi_j},
```

then

```tex
\widetilde q_{mn}^{+-}
=
\Theta_{mn}^{+-}
+ \Theta_{m+1,n}^{+-}
+ \Theta_{m,n+1}^{+-}
+ \Theta_{m+1,n+1}^{+-}.
```

So the live raw comparison can be written in the cleanest possible form:

```tex
\Omega_{mn}^{+-}(a)
\stackrel{?}{=}
\kappa_{+-}(a)\Theta_{mn}^{+-}
```

for all sufficiently large tail indices `m,n`.
Equivalently, after applying the common four-term stencil,

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+C_a^{+-,\mathrm{cap}}.
```

That is the first real bulk identity still missing on the path to RH.
Everything else in the current `H`-bridge route is now conditional on this
one comparison.

### L3''''''''. Exact proof fork after the raw mixed block

Once the notation `\Omega_{mn}^{+-}` and `\Theta_{mn}^{+-}` is frozen, the
remaining proof fork is brutally rigid:

1. exact raw identity:
   ```tex
   \Omega_{mn}^{+-}(a)=\kappa_{+-}(a)\Theta_{mn}^{+-};
   ```
2. cap-only weakened identity:
   the four-term filtered residual built from
   `\Omega_{mn}^{+-}(a)-\kappa_{+-}(a)\Theta_{mn}^{+-}`
   lands entirely in `C_a^{+-,\mathrm{cap}}`;
3. route-kill:
   a genuine non-cap mixed bulk residual survives.

There is no fourth honest option inside the current theorem shape.

### L3'''''''''. Hankel symmetry kill-test

Because the Q-side mixed block depends only on `m+n`, it satisfies the exact
anti-diagonal identity

```tex
\Theta_{m+1,n}^{+-}=\Theta_{m,n+1}^{+-},
\qquad
\widetilde q_{m+1,n}^{+-}=\widetilde q_{m,n+1}^{+-}.
```

Therefore any theorem of the form

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+C_a^{+-,\mathrm{cap}}
```

forces the filtered mixed block to satisfy the same anti-diagonal symmetry
outside the finite cap channel. The exact local test is:

```tex
K_{mn}^{+-}(a)
:=
M_{m+1,n}^{+-}(a)-M_{m,n+1}^{+-}(a).
```

If the mixed block has theorem shape

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+C_a^{+-,\mathrm{cap}}
```

with `C_a^{+-,\mathrm{cap}}` finite rank `r`, then the defect matrix
`K^{+-}=(K_{mn}^{+-})_{m,n>N}` must also be finite rank, in fact of rank at
most `2r`. Indeed, `\widetilde Q^{+-}` contributes zero to `K`, and the
remaining matrix is

```tex
K_{mn}^{+-}
=
C_{m+1,n}^{+-,\mathrm{cap}}-C_{m,n+1}^{+-,\mathrm{cap}},
```

which is the difference of two shifted copies of a rank-`r` matrix.
So the correct structural test is not pointwise vanishing in the deep tail,
but **finite-rank anti-diagonal defect**.

In particular, if one can prove that the matrix `K^{+-}` is not finite rank,
then the current mixed-block theorem shape is killed.

The earlier “deep tail pointwise zero” reading is too strong and should not be
used as the real theorem test.

For a pure Hankel block with no cap one would have the stronger identity

```tex
K_{mn}^{+-}(a)=0.
```

Using the explicit zero formulas, this becomes

```tex
K_{mn}^{+-}(a)
=
\frac{2\pi^2}{a^3}(-1)^{m+n+1}
\sum_\gamma \sin^2(a\gamma)\,\Xi_{mn}(\gamma),
```

where

```tex
\Xi_{mn}(\gamma)
:=
\frac{1}
{(\gamma-\alpha_{m+1})(\gamma-\alpha_{m+2})(\gamma-\alpha_n)(\gamma-\alpha_{n+1})}
-
\frac{1}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_{n+1})(\gamma-\alpha_{n+2})}.
```

Because `\alpha_k=\pi k/a` is an arithmetic progression, this difference
actually simplifies exactly. Writing `h:=\pi/a`, one gets

```tex
\Xi_{mn}(\gamma)
=
\frac{2h(\alpha_m-\alpha_n)}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_{m+2})
 (\gamma-\alpha_n)(\gamma-\alpha_{n+1})(\gamma-\alpha_{n+2})}
```

and therefore

```tex
\Xi_{mn}(\gamma)
=
\frac{2\pi^2}{a^2}(m-n)\,
\frac{1}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_{m+2})
 (\gamma-\alpha_n)(\gamma-\alpha_{n+1})(\gamma-\alpha_{n+2})}.
```

So the anti-diagonal defect itself factorizes as

```tex
K_{mn}^{+-}(a)
=
\frac{4\pi^4}{a^5}(-1)^{m+n+1}(m-n)
\sum_\gamma
\frac{\sin^2(a\gamma)}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_{m+2})
 (\gamma-\alpha_n)(\gamma-\alpha_{n+1})(\gamma-\alpha_{n+2})}.
```

This is a much sharper form of the kill-test:

- `K_{mn}^{+-}(a)` vanishes automatically on the diagonal `m=n`;
- off the diagonal, vanishing requires a genuine six-denominator cancellation
  across the zero sum;
- so any exact mixed Hankel symmetry in the deep tail is already a highly
  rigid arithmetic statement, not a soft boundary effect.

There is also a useful exact rank-2 decomposition. Set

```tex
p_\gamma(m)
:=
\frac{(-1)^m}
{(\gamma-\alpha_m)(\gamma-\alpha_{m+1})(\gamma-\alpha_{m+2})},
\qquad
u_\gamma(m):=\alpha_m p_\gamma(m),
\qquad
v_\gamma(m):=p_\gamma(m).
```

Then the factorized formula can be rewritten as

```tex
K_{mn}^{+-}(a)
=
\frac{4\pi^3}{a^4}
\sum_\gamma \sin^2(a\gamma)\,
\bigl(u_\gamma(m)v_\gamma(n)-v_\gamma(m)u_\gamma(n)\bigr).
```

So each zero contributes a rank-at-most-2 antisymmetric wedge kernel, and the
whole finite-rank question becomes brutally precise:

- if the infinite family of pairs `(u_\gamma,v_\gamma)` collapses to a finite
  span after summation, the mixed theorem shape might survive;
- if these wedge contributions remain genuinely independent in the tail, then
  `K^{+-}` cannot be finite rank and the route dies.

So the live mixed-block question can be sharpened one step further:

- either `K^{+-}` is finite rank, consistent with a Hankel-type comparator
  modulo finite cap;
- or `K^{+-}` is genuinely infinite-rank / not low-rank in the tail, and the
  current theorem shape is killed.

This is the cleanest exact route-kill test now available inside `PO2`.

There is also a rigorous finite-support rank-growth lemma behind this
decomposition. Write

```tex
h:=\pi/a,
\qquad
x_\gamma:=\gamma/h=a\gamma/\pi.
```

For a finite zero set `\Gamma_0`, let

```tex
K_{\Gamma_0}^{+-}(m,n)
:=
\frac{4\pi^3}{a^4}
\sum_{\gamma\in\Gamma_0}\sin^2(a\gamma)\,
\bigl(u_\gamma(m)v_\gamma(n)-v_\gamma(m)u_\gamma(n)\bigr).
```

### L3'''''''''. Finite-support generic rank growth

Assume that `\Gamma_0=\{\gamma_1,\dots,\gamma_L\}` satisfies:

1. `\sin^2(a\gamma_\ell)\neq 0` for every `\ell`;
2. there are no short resonances
   `\gamma_i-\gamma_j\in\{\pm h,\pm 2h\}` for `i\neq j`.

Then the sequence family

```tex
\{u_{\gamma_\ell},v_{\gamma_\ell}\}_{\ell=1}^L
```

is linearly independent on the tail `m>N`, and therefore

```tex
\operatorname{rank} K_{\Gamma_0}^{+-}=2L.
```

#### Proof

Suppose

```tex
\sum_{\ell=1}^L
\bigl(A_\ell u_{\gamma_\ell}(m)+B_\ell v_{\gamma_\ell}(m)\bigr)=0
\qquad(m>N).
```

Using `u_\gamma(m)=\alpha_m p_\gamma(m)=hm\,p_\gamma(m)` and the explicit
formula for `p_\gamma(m)`, this becomes

```tex
\sum_{\ell=1}^L
\frac{a_\ell m+b_\ell}
{(x_{\gamma_\ell}-m)(x_{\gamma_\ell}-m-1)(x_{\gamma_\ell}-m-2)}
=0
\qquad(m>N),
```

for suitable constants `a_\ell,b_\ell`. The left-hand side is a rational
function of the complex variable `z` with finitely many poles, and it vanishes
for infinitely many integers `z=m>N`, so it is identically zero.

Under the short-resonance exclusion, the pole triples

```tex
\{x_{\gamma_\ell},x_{\gamma_\ell}-1,x_{\gamma_\ell}-2\}
```

are pairwise disjoint. Hence the residues at `z=x_{\gamma_\ell}` and
`z=x_{\gamma_\ell}-1` must vanish separately for each `\ell`, giving

```tex
a_\ell x_{\gamma_\ell}+b_\ell=0,
\qquad
a_\ell(x_{\gamma_\ell}-1)+b_\ell=0,
```

and therefore `a_\ell=b_\ell=0`. So all `A_\ell,B_\ell` vanish, proving the
independence of the `2L` sequences.

Now form the infinite column matrix

```tex
W_{\Gamma_0}
:=
\bigl[\sqrt{c_\gamma}\,u_\gamma\ \ \sqrt{c_\gamma}\,v_\gamma\bigr]_{\gamma\in\Gamma_0},
\qquad
c_\gamma:=\frac{4\pi^3}{a^4}\sin^2(a\gamma).
```

Then

```tex
K_{\Gamma_0}^{+-}=W_{\Gamma_0}J_LW_{\Gamma_0}^*,
```

where `J_L` is the block-diagonal symplectic matrix with `L` copies of
`\begin{psmallmatrix}0&1\\-1&0\end{psmallmatrix}`. Since `J_L` is invertible
and the columns of `W_{\Gamma_0}` are independent, `K_{\Gamma_0}^{+-}` has
rank `2L`. Done.

#### Consequence

Every finite nonresonant zero packet with nonzero weights already contributes
two genuinely new mixed directions. So the survival of the mixed theorem shape
cannot come from any finite-level automatic collapse:

- finite packets generically increase rank by `2` per zero;
- for each fixed `a`, the zero-counting asymptotic `N(T)\sim T\log T/(2\pi)`
  implies there are infinitely many zeros with `\sin^2(a\gamma)\neq 0`, since
  the bad lattice `(\pi/a)\mathbb Z` has only `O(T)` points up to height `T`;
- after choosing finitely many such zeros, avoiding new short resonances costs
  only finitely many forbidden values `\gamma_i\pm h,\gamma_i\pm 2h`, so one
  can greedily build nonresonant packets of arbitrary finite size;
- therefore there exist finite packets `\Gamma_0` for which
  `\operatorname{rank}K_{\Gamma_0}^{+-}` is arbitrarily large;
- therefore a finite-rank full defect would require genuinely global
  cancellations across infinitely many zero directions;
- in particular, there is no remaining soft route in which the mixed defect
  quietly becomes low-rank for local algebraic reasons alone.

### L3'''''''''''. Meromorphic residue profiles

There is a further exact sharpening if one analytically continues the first
tail index. Define

```tex
\mathbf p_\gamma(z)
:=
\frac{e^{i\pi z}}
{(\gamma-\pi z/a)(\gamma-\pi(z+1)/a)(\gamma-\pi(z+2)/a)},
\qquad
\mathbf u_\gamma(z):=\frac{\pi z}{a}\mathbf p_\gamma(z),
\qquad
\mathbf v_\gamma(z):=\mathbf p_\gamma(z).
```

Then for fixed tail index `n>N` the mixed anti-diagonal defect has the
meromorphic continuation

```tex
\mathbf K^{+-}(z,n)
:=
\frac{4\pi^3}{a^4}
\sum_\gamma \sin^2(a\gamma)\,
\bigl(\mathbf u_\gamma(z)v_\gamma(n)-\mathbf v_\gamma(z)u_\gamma(n)\bigr),
```

which converges locally normally away from its pole set because the summand is
`O(\gamma^{-6})` uniformly on compact `z`-sets.

For any zero `\gamma` that is nonresonant with all the others in the first
variable, the residue at `z=x_\gamma=a\gamma/\pi` is explicit:

```tex
\operatorname*{Res}_{z=x_\gamma}\mathbf K^{+-}(z,n)
=
-\frac{2a}{\pi^2}\sin^2(a\gamma)e^{ia\gamma}
\frac{(-1)^n}{(x_\gamma-n-1)(x_\gamma-n-2)}.
```

So every such zero leaves a genuine two-pole residue profile in the second
tail index `n`. Finite-support nonresonant packets therefore produce not only
rank growth, but also explicitly distinguishable residue channels.

This isolates the only serious hard wall now left inside `PO2`:

- the finite-support algebra is no longer the issue;
- the remaining question is whether finite rank on the **discrete** tail can be
  upgraded to a finite-dimensional statement on these meromorphic residue
  profiles;
- if that upgrade is valid, then the existence of infinitely many nonresonant
  zeros with `\sin^2(a\gamma)\neq 0` kills the mixed theorem shape
  immediately.

So the route is now squeezed to one exact meta-lemma, not to a vague cloud:
bridge finite rank on the integer tail to finite-dimensional meromorphic
residue data for `\mathbf K^{+-}`.

External sanity-check says this wall is real and not an artifact of bad
packaging:

- classical Kronecker/Hankel theory explains why finite rank is the correct
  structural benchmark once a mixed block is Hankel modulo cap;
- Carlson-type uniqueness theorems explain why values on the integers can
  determine an entire function of sufficiently small exponential type;
- but `\mathbf K^{+-}` sits strictly between these languages: it is not a pure
  Hankel symbol problem, and its column kernels are meromorphic rather than
  entire.

So no off-the-shelf theorem currently closes the gap. The residue-upgrade
lemma is a genuinely new bridge that still has to be proved or refuted.

### Exact remaining bridge lemma

The last unresolved step can now be stated cleanly.

```tex
\textbf{Residue-upgrade lemma (target).}
```

Let `F(z,n)` be a kernel of the same class as `\mathbf K^{+-}(z,n)` above:

- meromorphic in `z` with poles only at the triples
  `x_\gamma,x_\gamma-1,x_\gamma-2`;
- locally normally convergent off its poles;
- of the form
  `\sum_\gamma (A_\gamma(n) \mathbf u_\gamma(z)+B_\gamma(n)\mathbf v_\gamma(z))`
  with the same Cauchy-type profiles.

Assume the discrete tail matrix

```tex
\bigl(F(m,n)\bigr)_{m,n>N}
```

has finite rank `r`. Then the residue profile family

```tex
n\longmapsto \operatorname*{Res}_{z=x_\gamma}F(z,n)
```

should lie in an `r`-dimensional subspace of tail sequences.

If this lemma is true, `PO2` dies immediately: the explicit residue profiles
above are linearly independent for arbitrarily large nonresonant zero packets,
so `K^{+-}` cannot be finite rank.

If this lemma is false, then the current route has located its exact hard
failure mode: discrete low rank on the tail does not control the meromorphic
residue data strongly enough to kill the mixed block.

### Reduction to a scalar uniqueness principle

The residue-upgrade lemma itself reduces to a one-variable uniqueness
statement. Let `\mathcal M_a` denote the class of meromorphic functions of the
form

```tex
H(z)
=
\sum_\gamma \bigl(A_\gamma \mathbf u_\gamma(z)+B_\gamma \mathbf v_\gamma(z)\bigr),
```

with locally normal convergence off the pole set and with the same pole
triples `x_\gamma,x_\gamma-1,x_\gamma-2`.

Then the whole `PO2` bridge is reduced to:

```tex
\textbf{Scalar uniqueness principle (target).}
```

If `H\in\mathcal M_a` and

```tex
H(m)=0\qquad\forall m>N,
```

then `H\equiv 0`.

Indeed, assume this scalar principle. If the discrete matrix `F(m,n)` has rank
`r`, choose tail columns `n_1,\dots,n_r` spanning all others. For each `n`
there exist coefficients `c_j(n)` such that

```tex
F(m,n)=\sum_{j=1}^r c_j(n)F(m,n_j)
\qquad\forall m>N.
```

So the meromorphic difference

```tex
H_n(z):=
F(z,n)-\sum_{j=1}^r c_j(n)F(z,n_j)
```

lies in `\mathcal M_a` and vanishes on every integer `m>N`. By scalar
uniqueness, `H_n\equiv 0`. Taking residues at `z=x_\gamma` shows that every
residue profile `n\mapsto \operatorname*{Res}_{z=x_\gamma}F(z,n)` lies in the
span of the `r` basis residue profiles coming from `n_1,\dots,n_r`. This is
exactly the residue-upgrade lemma.

So one more compression is now available:

- finite rank on the tail `\Longrightarrow` residue-upgrade
  **provided** scalar uniqueness holds in `\mathcal M_a`;
- finite-support scalar uniqueness is already true by the rational-function
  proof above;
- therefore the real unresolved core is no longer matrix rank, but the
  infinite-support scalar uniqueness problem for `\mathcal M_a`.

This is the cleanest exact statement of the remaining mixed-block difficulty.

### Difference-descent for `\mathcal M_a`

The scalar uniqueness problem also admits one exact simplification by discrete
antidifferencing. Write

```tex
f_\gamma(z):=\frac{1}{x_\gamma-z},
\qquad
g_\gamma(z):=\frac{1}{(x_\gamma-z)(x_\gamma-z-1)},
\qquad
\Delta F(z):=F(z)-F(z+1).
```

Then the basic pole identities are

```tex
\frac{1}{(x_\gamma-z)(x_\gamma-z-1)(x_\gamma-z-2)}
=
-\frac12 \Delta g_\gamma(z),
```

and

```tex
z\frac{1}{(x_\gamma-z)(x_\gamma-z-1)(x_\gamma-z-2)}
=
-\frac12 \Delta\bigl(zg_\gamma(z)-f_\gamma(z+1)\bigr).
```

Therefore each basis element in `\mathcal M_a` is already a discrete
difference of a simpler kernel:

```tex
\mathbf v_\gamma(z)
=
-\frac{e^{i\pi z}}{2h^3}\Delta g_\gamma(z),
\qquad
\mathbf u_\gamma(z)
=
-\frac{e^{i\pi z}}{2h^2}
\Delta\bigl(zg_\gamma(z)-f_\gamma(z+1)\bigr).
```

So every `H\in\mathcal M_a` can be written as

```tex
H(z)=e^{i\pi z}\Delta G(z),
```

where `G` belongs to a simpler meromorphic class `\mathcal N_a` generated by
the double-pole kernels `g_\gamma` and the shifted simple-pole kernels
`f_\gamma(z+1)`.

Equivalently, everything can already be rewritten in terms of the simple
Cauchy kernels `f_\gamma` and their first two discrete differences, because

```tex
\Delta f_\gamma(z)=-g_\gamma(z),
\qquad
\Delta^2 f_\gamma(z)=2\frac{1}{(x_\gamma-z)(x_\gamma-z-1)(x_\gamma-z-2)}.
```

So the basis elements become

```tex
\mathbf v_\gamma(z)
=
\frac{e^{i\pi z}}{2h^3}\Delta^2 f_\gamma(z),
```

and

```tex
\mathbf u_\gamma(z)
=
\frac{e^{i\pi z}}{2h^2}
\Bigl(2\Delta f_\gamma(z)+(x_\gamma-2)\Delta^2 f_\gamma(z)\Bigr).
```

Hence every `H\in\mathcal M_a` has the explicit form

```tex
H(z)
=
e^{i\pi z}\sum_\gamma
\Bigl(c_\gamma \Delta f_\gamma(z)+d_\gamma \Delta^2 f_\gamma(z)\Bigr),
```

for suitable coefficients `c_\gamma,d_\gamma`. In particular, `\mathcal M_a`
already sits inside the discrete-difference algebra generated by the single
pole family `f_\gamma`.

Writing

```tex
J(z):=\sum_\gamma \bigl(c_\gamma f_\gamma(z)+d_\gamma \Delta f_\gamma(z)\bigr),
```

one has simply

```tex
H(z)=e^{i\pi z}\Delta J(z).
```

Now use `\Delta f_\gamma(z)=f_\gamma(z)-f_\gamma(z+1)`. Then `J` itself can be
rewritten as a difference of two plain simple-pole Cauchy transforms:

```tex
J(z)=P(z)-Q(z+1),
```

where

```tex
P(z):=\sum_\gamma (c_\gamma+d_\gamma)f_\gamma(z),
\qquad
Q(z):=\sum_\gamma d_\gamma f_\gamma(z).
```

So the scalar uniqueness wall has an even cleaner equivalent form:

- if `H(m)=0` for all `m>N`, then `\Delta J(m)=0`, hence `J(m)=0` on the tail;
- equivalently,
  `P(m)=Q(m+1)` for every `m>N`.

Therefore the remaining problem can be restated as a **simple-pole
shift-uniqueness principle**:

```tex
\textbf{Shift-uniqueness principle (target).}
```

If `P,Q` belong to the simple Cauchy class

```tex
\mathcal C_a:=\left\{\sum_\gamma c_\gamma f_\gamma(z)\right\},
```

and satisfy

```tex
P(m)=Q(m+1)\qquad\forall m>N,
```

then

```tex
P(z)=Q(z+1)
```

identically.

This is now the sharpest clean formulation of the mixed-block hard wall: not a
three-pole theorem, but a shifted equality problem for simple Cauchy
transforms on the integer tail.

### Cauchy-operator reformulation

The shift-uniqueness principle can be rewritten as plain injectivity of an
infinite Cauchy transform. Set

```tex
Y_a:=\{x_\gamma:\gamma\in\mathcal Z_+\}\cup\{x_\gamma-1:\gamma\in\mathcal Z_+\},
```

and define coefficients on this merged support by

```tex
e(x_\gamma):=a_\gamma,
\qquad
e(x_\gamma-1):=-b_\gamma.
```

Then

```tex
R(z):=P(z)-Q(z+1)=\sum_{y\in Y_a}\frac{e(y)}{y-z}.
```

So the shift-uniqueness target is equivalent to:

```tex
\textbf{Cauchy-tail injectivity principle (target).}
```

If

```tex
\sum_{y\in Y_a}\frac{e(y)}{y-m}=0
\qquad\forall m>N,
```

then `e\equiv 0`.

This immediately splits the problem into a solved finite-support piece and the
genuine infinite-support wall.

#### Finite-support case

If `e` is supported on distinct points
`y_1,\dots,y_L\in\mathbb C\setminus\mathbb Z`,
then choosing any distinct integers `m_1,\dots,m_L>N`, the system

```tex
\sum_{j=1}^L \frac{e_j}{y_j-m_k}=0
\qquad(k=1,\dots,L)
```

has coefficient matrix

```tex
\Bigl(\frac{1}{y_j-m_k}\Bigr)_{k,j},
```

whose determinant is the classical Cauchy determinant

```tex
\frac{\prod_{i<j}(y_j-y_i)\prod_{i<j}(m_i-m_j)}
{\prod_{i,j}(y_j-m_i)},
```

and is therefore nonzero. Hence all `e_j=0`.

So the finite-support version of the shift-uniqueness principle is already
completely closed. The only unresolved issue is:

- does injectivity of these finite Cauchy sections survive under our
  infinite support `Y_a` and the coefficient class inherited from `PO2`?

That is now the plainest exact statement of the live wall.

### Moment-side sufficient criterion

There is also a genuinely useful side theorem here, but it is important not to
confuse it with the live wall.

Suppose `Y\subset\mathbb R` satisfies `|y|>1` for all `y\in Y`, and let

```tex
S_m:=\sum_{y\in Y}\frac{c_y}{y^m},
\qquad
\sum_{y\in Y}|c_y|<\infty.
```

Then the following is true:

```tex
\textbf{Tail-moment injectivity.}
```

If `S_m=0` for all `m>N`, then all coefficients `c_y` vanish.

The proof is clean: set `x_y:=1/y`, push the atomic measure
`\mu:=\sum_y c_y\delta_{x_y}` onto the compact `K=\overline{\{x_y\}}\subset
[-1,1]`, multiply by `x^{N+1}`, and reduce to vanishing of all polynomial
moments of a finite signed measure; Stone--Weierstrass then gives `\mu=0`.

This theorem is real and useful. But it does **not** yet settle the current
`PO2` wall by itself, because our live hypothesis is not tail-moment vanishing.
What we actually know in `PO2` is the Cauchy-tail identity

```tex
\sum_{y\in Y_a}\frac{e(y)}{y-m}=0
\qquad\forall m>N.
```

So the exact missing implication is still:

```tex
\text{Cauchy-tail vanishing}
\quad\Longrightarrow\quad
\text{tail-moment vanishing}.
```

If one could prove that implication for our `\ell^1(Y_a)` class, the
tail-moment theorem above would finish the job immediately. But that
implication is precisely the current hard wall: after inversion the support
accumulates at `0`, so a naive large-`m` geometric-series expansion is not
uniform enough to justify the passage to moments.

So the moment theorem should be treated as:

- a correct and powerful sufficient criterion;
- a good sanity-check for bounded-support or already-momentized variants;
- but not yet a proof of the live `\ell^1`-Cauchy-tail injectivity problem.

There is now one more decisive correction: the generic bridge

```tex
\ell^1\text{-Cauchy-tail vanishing}
\Longrightarrow
\text{tail-moment vanishing}
```

should no longer be treated as a live global theorem target at all.
A half-shifted-lattice Gamma-ratio mechanism provides a nonzero
`\ell^1` simple-Cauchy sum vanishing on every sufficiently large integer,
while the coefficients are not zero and therefore cannot have all tail
moments vanishing. So even if the full counterexample is written elsewhere,
the route-level conclusion for `PO2` is already clear:

- generic momentization is not the theorem we need;
- the first route can only survive in a **`Y_a`-specific** form.

This changes the live first-route target to:

```tex
\textbf{Y}_a\textbf{-specific no-counterexample lemma.}
```

Prove that the actual pole geometry

```tex
Y_a=\{x_\gamma,\ x_\gamma-1\},
\qquad
x_\gamma=\frac{a\gamma}{\pi},
```

does **not** admit the half-shifted-lattice / Gamma-ratio mechanism that kills
the generic bridge.

If that `Y_a`-specific exclusion lands, the first route stays alive in a form
strong enough to matter for RH. If it fails, then the mixed `H`-bridge route
is in much deeper trouble than a mere missing lemma.

There is also an immediate first split inside this `Y_a`-specific task.

```tex
\textbf{Finite gamma-quotient exclusion.}
```

Any counterexample built from a **finite** quotient of Gamma factors has pole
divisor supported on a finite union of affine unit lattices

```tex
\alpha_j+\mathbb Z_{\ge 0},
```

up to finitely many exceptional rational factors. This is exactly the Euler /
gamma-quotient mechanism behind the generic half-shifted-lattice example.

By contrast, the full structured support

```tex
Y_a=\{x_\gamma,\ x_\gamma-1\}
```

has counting law

```tex
n_{Y_a}(R)\asymp \frac{R\log R}{a},
```

whereas any finite union of affine unit lattices has only `O(R)` points up to
height `R`. So one immediate theorem-grade consequence is:

- no finite Gamma-quotient mechanism can realize **all but finitely many** of
  the poles of `Y_a`;
- any surviving first-route counterexample must therefore live on a genuinely
  sparse affine-lattice subfamily of `Y_a`, not on the bulk of the pole set.

This is good news, but it also changes the tactical picture.

The remaining sparse-subfamily question is already very close to arithmetic
progression questions for zeta zeros themselves: an infinite affine lattice
inside `Y_a` would mean an infinite progression

```tex
\gamma_0+\frac{\pi}{a}\mathbb Z_{\ge 0}
```

of zero ordinates at a fixed imaginary offset. External sanity-check says this
territory is genuinely deep and should not be mistaken for a routine closure
lemma.

So the first-route conclusion is now:

1. finite Gamma-quotient / finite shifted-lattice mechanisms are excluded on
   density grounds for the full `Y_a`;
2. the only remaining first-route danger is a sparse affine-lattice subfamily;
3. that sparse question is likely not the fastest critical-path move toward RH.

Therefore, after this split, the preferred live attack moves to the second
route unless a very sharp `Y_a`-specific exclusion of sparse affine-lattice
subfamilies appears unexpectedly.

### Why a direct Carlson shortcut does not yet close `PO2`

There is a tempting stronger shortcut:

```tex
F(z):=\sum_{y\in Y_a}\frac{e(y)}{y-z},
\qquad
F(m)=0 \quad \forall m>N.
```

Since `e\in\ell^1(Y_a)`, one indeed expects `F(z)=O(|z|^{-1})` along rays away
from the pole set, so it is natural to ask whether a Carlson theorem could
kill `F` directly and bypass the moment reduction.

This observation is good, but the direct Carlson step is still blocked at the
level of hypotheses.

Carlson's theorem in the form used in the external sanity-checks applies to
functions holomorphic in `\Re z\ge 0` (or entire variants), with controlled
exponential type on the imaginary axis, and vanishing on `\mathbb N`.
Our live object `F` is not in that class:

- `F` is meromorphic, not holomorphic, because it has poles at the points
  `y\in Y_a`;
- for the actual merged support in `PO2`, this pole set meets the right
  half-plane itself, so the raw Cauchy transform fails Carlson's holomorphy
  hypothesis before any growth estimate even begins;
- decay of `F(z)` at infinity does **not** repair this: it does not turn a
  meromorphic function into an entire or half-plane-holomorphic one, and it
  does not by itself place `F` in Carlson's uniqueness class.

So the exact missing bridge is not "apply Carlson to `F`". The missing bridge
would be one of the following stronger statements:

```tex
\text{either }
\sum_{y\in Y_a}\frac{e(y)}{y-m}=0 \ \forall m>N
\Longrightarrow
\text{tail moments vanish},
```

or else a genuine pole-killing regularization theorem:

```tex
\text{construct } \Phi_{Y_a}(z)
\text{ so that } \Phi_{Y_a}(z)F(z)
\text{ is holomorphic in } \Re z\ge 0
```

with growth still below the Carlson barrier.

At the moment we have neither of these two upgrades. Therefore the direct
Carlson shortcut should be treated as:

- a very good diagnostic insight;
- evidence that the remaining wall is about holomorphic regularization rather
  than local algebra;
- but not yet a completed proof step inside `PO2`.

### First direct attack: why naive momentization still does not close

The first natural move after the Cauchy-tail formulation is to try to convert

```tex
\sum_{y\in Y_a}\frac{e(y)}{y-m}=0
\qquad (m>N)
```

into tail-moment identities by geometric expansion.

That naive route is still blocked for a concrete reason. The merged support
`Y_a` is unbounded, so for a fixed large integer `m` there is no uniform
expansion of the kernel `1/(y-m)` that is simultaneously valid on all of
`Y_a`: the regions `y<m` and `y>m` require different expansions, and the
support crosses both regions for every large `m`.

After inversion `x=1/y`, this becomes the same obstruction in another form:
the support accumulates at `0`, so there is no uniform positive radius on
which one can justify a single power-series argument and then exchange the
sum over `y` with the expansion.

So the first route is still open, but now in a much sharper form:

```tex
\textbf{Open sublemma.}\quad
\ell^1\text{-Cauchy-tail vanishing}
\Longrightarrow
\text{tail-moment vanishing}
```

must be proved by something more structural than a naive geometric-series
exchange.

### Second direct attack: naive Weierstrass regularization looks too large

The second natural move is to cancel the poles of

```tex
F(z)=\sum_{y\in Y_a}\frac{e(y)}{y-z}
```

by multiplying with an entire factor vanishing on `Y_a`.

Here the raw density of the pole set already gives a serious obstruction. The
merged support is

```tex
Y_a=\{x_\gamma:\gamma\in\mathcal Z_+\}\cup\{x_\gamma-1:\gamma\in\mathcal Z_+\},
\qquad x_\gamma=\frac{a\gamma}{\pi},
```

so by the zeta zero counting law

```tex
N_\zeta(T)\sim \frac{T\log T}{2\pi},
```

the support counting function satisfies heuristically

```tex
n_{Y_a}(R)\asymp \frac{R\log R}{a}.
```

Consequently,

```tex
\sum_{y\in Y_a,\ y\le R}\frac1y
\asymp
(\log R)^2,
```

so the zero set is not genus-0 summable. A naive pole-killing entire factor
would therefore have to be at least genus 1, and the corresponding
exponential compensation suggests real-axis growth on the scale

```tex
\log |\Phi_{Y_a}(x)|
\sim
x\sum_{y\le 2x}\frac1y
\asymp
x(\log x)^2,
```

which is already larger than the `x\log x` Carlson/Pila barrier.

This does not yet kill every imaginable regularization, but it does kill the
naive canonical-product route. Any surviving Carlson strategy would need a
highly structured regularizer with cancellations far beyond the bare
Weierstrass construction.

### Structured regularizer candidate: the built-in `\xi` factor

The second route is not dead. What dies is only the naive ad hoc Weierstrass
factor. There is a much more structured candidate already sitting inside the
Suzuki block formulas.

Indeed the raw sums are indexed by zeros of the entire function

```tex
z\longmapsto \xi(1/2-iz),
```

and the pole locations in the Cauchy reformulation are

```tex
x_\gamma=\frac{a\gamma}{\pi},
\qquad
x_\gamma-1.
```

So define

```tex
\Xi_a(z):=\xi\!\left(\frac12-\frac{i\pi z}{a}\right),
\qquad
\Phi_a(z):=\Xi_a(z)\Xi_a(z+1).
```

Then `\Xi_a(z)` vanishes at `z=x_\gamma`, and `\Xi_a(z+1)` vanishes at
`z=x_\gamma-1`. Therefore `\Phi_a` is the first genuinely natural pole-killing
candidate for the Cauchy transform

```tex
F(z)=\sum_{y\in Y_a}\frac{e(y)}{y-z}.
```

This candidate is qualitatively different from a bare Weierstrass product:

- along the positive real axis, `\Xi_a(x)=\xi(1/2-i\pi x/a)` sits on the
  critical line and inherits the strong Gamma decay there;
- along the imaginary axis, `\Xi_a(it)=\xi(1/2+\pi t/a)` is controlled by the
  real-axis Stirling regime of `\xi`, hence of `\exp(O(|t|\log|t|))` type
  rather than the naive `\exp(O(|t|(\log|t|)^2))` suggested by the genus-1
  canonical product;
- the zero set is not imposed externally: it is exactly the zero set that the
  Suzuki-side meromorphic kernel already sees.

So the second route now has a clean new form:

```tex
\textbf{Structured Carlson candidate.}\quad
H_a(z):=\Phi_a(z)F(z)
```

and the live question is whether `H_a` can be shown to lie in a Carlson/Pila
uniqueness class on `\Re z\ge 0`.

That is a real advance. The regularization problem is no longer "invent some
entire factor". It is now:

- prove that the built-in `\xi`-factor really cancels the poles of `F`;
- prove that the resulting `H_a` is holomorphic in the right half-plane;
- prove the required `x\log x`-scale growth bounds on the boundary data so
  that a Carlson/Pila theorem can actually fire.

### First boundary estimates for the structured `\xi`-regularizer

This new route is already sharper than a mere name, because the pole geometry
and the `\xi`-growth line up correctly.

Write a zero of `\xi(1/2-iz)` as

```tex
\gamma=\tau+i(\beta-\tfrac12),
```

where `\rho=\beta+i\tau` is a nontrivial zero of the zeta function. Hence

```tex
|\Im \gamma|\le \frac12,
\qquad
\Re \gamma=\tau>0,
```

so after scaling

```tex
x_\gamma=\frac{a\gamma}{\pi}
```

the pole set `Y_a=\{x_\gamma,x_\gamma-1\}` lies in a fixed horizontal strip:

```tex
\Re y > -1,
\qquad
|\Im y|\le \frac{a}{2\pi}.
```

Because `e\in \ell^1(Y_a)`, this already gives a uniform imaginary-axis bound
for the raw Cauchy transform:

```tex
|F(it)|
\le
\sum_{y\in Y_a}\frac{|e(y)|}{|y-it|}
\ll_a
\frac{\|e\|_{\ell^1(Y_a)}}{1+|t|}.
```

Now look at the structured factor

```tex
\Xi_a(it)=\xi\!\left(\frac12+\frac{\pi t}{a}\right).
```

Along the imaginary axis of `z`, the argument of `\xi` is real. So Stirling on
the Gamma factor in

```tex
\xi(s)=\frac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
```

gives

```tex
\log |\Xi_a(it)|
=
\frac{\pi}{2a}|t|\log|t| + O_a(|t|),
```

and therefore

```tex
\log |\Phi_a(it)|
=
\frac{\pi}{a}|t|\log|t| + O_a(|t|).
```

Combining this with the `O(|t|^{-1})` decay of `F(it)` yields the first real
imaginary-axis estimate:

```tex
\log |H_a(it)|
\le
\frac{\pi}{a}|t|\log|t| + O_a(|t|).
```

This is already much better than the naive Weierstrass route. But it is
important not to overstate what it gives: in the Pila theorem we are using as
sanity-check, the `x\log x` growth is allowed on the positive real axis,
whereas the imaginary axis still needs sub-Carlson linear type. So the bound
above is on the wrong axis for a direct application of Pila.

The positive-real-axis side can nevertheless be controlled very cleanly.

Indeed, for real `x\ge 0`, every pole `y\in Y_a` lies in the strip

```tex
\Sigma_a:=\{\zeta\in\mathbb C:\ \Re \zeta\ge -1,\ |\Im \zeta|\le a/(2\pi)\}.
```

Since `\Phi_a(y)=0`, one has

```tex
\frac{\Phi_a(x)}{x-y}
=
\frac{\Phi_a(x)-\Phi_a(y)}{x-y}
=
\int_0^1 \Phi_a'(y+t(x-y))\,dt.
```

The segment from `y` to the real point `x` stays inside `\Sigma_a`, and
standard strip bounds for `\xi` plus Cauchy estimates give

```tex
M_a:=\sup_{\zeta\in\Sigma_a}|\Phi_a'(\zeta)|<\infty.
```

Therefore

```tex
|H_a(x)|
\le
\sum_{y\in Y_a}|e(y)|\,\left|\frac{\Phi_a(x)}{x-y}\right|
\le
M_a\|e\|_{\ell^1(Y_a)}
\qquad(x\ge 0).
```

So the structured route now has a complementary boundary package:

```tex
H_a(x)=O_a(1)\quad (x\to+\infty),
\qquad
\log|H_a(it)|\le \frac{\pi}{a}|t|\log|t|+O_a(|t|).
```

This is real progress, but it is not yet a direct Carlson/Pila theorem. The
remaining second-route wall is now very precise:

- either find a transport that moves the `x\log x` burden from the imaginary
  axis to the positive real axis;
- or use a different uniqueness theorem adapted to exactly this boundary
  pattern.

### Rotated Gamma transport candidate and its exact obstruction

There is a natural way to attack exactly that remaining wall. Pila's proof
uses powers of `\Gamma(z+1)` to move `x\log x` growth on the positive real
axis into linear type on the imaginary axis. Here the heavy axis is reversed,
so the natural rotated transport is:

```tex
G_{a,k}(z):=H_a(z)\,\Gamma(1-iz)^{-k},
```

with an integer `k` chosen large enough.

This is a serious candidate rather than a slogan:

- `\Gamma(1-iz)^{-1}` is entire, so this transport introduces no new poles;
- if `H_a(n)=0` for all integers `n>N`, then automatically
  `G_{a,k}(n)=0` for all `n>N`, because `\Gamma(1-in)` is finite and nonzero;
- along the imaginary axis `z=it`, the factor becomes
  `\Gamma(1+t)^{-k}` on the positive side and, by the reflection formula,
  still decays superexponentially on the negative side.

Using the previous bound

```tex
\log |H_a(it)|
\le
\frac{\pi}{a}|t|\log|t| + O_a(|t|),
```

one gets for any integer `k>\pi/a`:

```tex
\log |G_{a,k}(it)|
\le
-\Bigl(k-\frac{\pi}{a}\Bigr)|t|\log|t| + O_a(|t|).
```

So after this transport the imaginary-axis growth is not merely linear; it is
actually strongly decaying, which is more than enough for the Carlson side.

On the positive real axis, the previous bound `H_a(x)=O_a(1)` together with
the vertical-line Stirling estimate

```tex
\log |\Gamma(1-ix)^{-k}| = \frac{k\pi}{2}x + O(\log x)
```

gives

```tex
\log |G_{a,k}(x)| = O_a(x),
```

which is still `c=0` in Pila's `x\log x` scale.

The external sanity-check from Pila's note explains why this move looked
natural:

- Pila's transport step is `g(z)=f(z)/\Gamma(z+1)^{2c'}` on the same
  right half-plane, used to exchange `x\log x` growth on `\mathbb R_+` for
  Carlson-type growth on the imaginary axis;
- our candidate `G_{a,k}(z)=H_a(z)\Gamma(1-iz)^{-k}` is the axis-rotated
  analogue of that move, designed for a boundary pattern where the heavy
  `|t|\log|t|` term currently sits on `i\mathbb R` instead of `\mathbb R_+`;
- so it was reasonable to test whether a single rotated Gamma factor could
  fit the same holomorphy-plus-growth template after the axis swap.

But the test fails on the lower imaginary half-axis.

Indeed, for `z=it` with `t<0`, one has

```tex
G_{a,k}(it)=H_a(it)\,\Gamma(1+t)^{-k}.
```

Now the reflection formula gives

```tex
\Gamma(1+t)\Gamma(-t)=\frac{\pi}{\sin(\pi(1+t))},
```

hence

```tex
\Gamma(1+t)^{-1}
=
\frac{\sin(\pi t)}{\pi}\Gamma(-t).
```

So on any sequence `t\to-\infty` staying a fixed distance away from the
negative integers, Stirling yields

```tex
\log |\Gamma(1+t)^{-k}|
=
k|t|\log|t|+O_k(|t|).
```

That is the wrong sign: on the lower half of `i\mathbb R` the single rotated
Gamma factor does **not** damp the heavy `|t|\log|t|` term, it amplifies it.
So the candidate `G_{a,k}` is not in a Pila/Carlson class on the full
imaginary axis.

The obvious symmetric rescue also fails. If one tries

```tex
H_a(z)\,\Gamma(1-iz)^{-k}\Gamma(1+iz)^{-k},
```

then on `z=it` the reflection formula collapses the Gamma pair to

```tex
\frac{\sin(\pi t)^k}{(\pi t)^k},
```

which gives only polynomial control and therefore cannot cancel the
`\exp((\pi/a)|t|\log|t|)` scale coming from `H_a(it)`.

So this subroute is now honestly killed:

```tex
\textbf{Killed subroute.}\quad
\text{single-Gamma rotated transport } H_a(z)\Gamma(1-iz)^{-k}.
```

Its exact kill certificate is:

- it improves the upper half of `i\mathbb R`;
- it blows up on the lower half of `i\mathbb R` like
  `\exp(k|t|\log|t|+O(|t|))`;
- the naive symmetric Gamma pair only gives polynomial decay and is still far
  too weak.

Therefore the second route remains alive only in the following reduced form:

```tex
\textbf{Remaining second-route wall.}
```

Find either

- a genuinely two-sided transport that damps both halves of `i\mathbb R`
  without spoiling the positive-real-axis bound, or
- a uniqueness theorem adapted directly to the boundary pattern
  `H_a(x)=O_a(1)` on `\mathbb R_+` and
  `\log |H_a(it)|\le (\pi/a)|t|\log|t|+O_a(|t|)` on `i\mathbb R`.

There is one more useful compression here. The failure is not special to the
single factor `\Gamma(1-iz)^{-k}`; it propagates to the whole obvious finite
Gamma family.

```tex
\textbf{Finite shifted-Gamma transport obstruction.}
```

Consider any transport built from finitely many inverse Gamma factors

```tex
\Psi(z)
=
\prod_{j=1}^p \Gamma(\alpha_j-iz)^{-u_j}
\prod_{\ell=1}^q \Gamma(\beta_\ell+iz)^{-v_\ell},
```

with fixed shifts `\alpha_j,\beta_\ell\in\mathbb C` and nonnegative weights
`u_j,v_\ell`.

Let

```tex
U:=\sum_{j=1}^p u_j,
\qquad
V:=\sum_{\ell=1}^q v_\ell.
```

Then Stirling on the positive-real arguments and reflection on the negative
ones give:

- on the upper half of the imaginary axis,
  ```tex
  \log |\Psi(it)|
  =
  -(U-V)t\log t+O(t)
  \qquad (t\to+\infty);
  ```
- on the lower half,
  ```tex
  \log |\Psi(-it)|
  =
  +(U-V)t\log t+O(t)
  \qquad (t\to+\infty).
  ```

So there are only three possibilities:

1. `U>V`: the transport damps the upper half but blows up on the lower half;
2. `U<V`: it damps the lower half but blows up on the upper half;
3. `U=V`: the `t\log t` terms cancel on both halves, leaving at best
   `O(t)` or smaller, which is too weak to kill the
   `(\pi/a)|t|\log|t|` growth of `H_a(it)`.

Therefore no **finite shifted-Gamma product** can supply the genuinely
two-sided damping required for the structured second route.

This is an exact family-level kill certificate, not just a failure of one
pretty formula.

So the live second-route target sharpens again:

```tex
\textbf{Non-Gamma two-sided transport target.}
```

Find either

- a zero-free holomorphic factor `\Omega_a` on `\Re z\ge 0` with
  ```tex
  \log |\Omega_a(it)|
  \le
  -\Bigl(\frac{\pi}{a}+\varepsilon\Bigr)|t|\log|t|+O_a(|t|),
  \qquad
  \log |\Omega_a(x)|=O_a(x),
  ```
  for some `\varepsilon>0`, together with the routine global
  `O(|z|^{2-\delta})` bound needed by Pila;
- or a uniqueness theorem that reads the boundary pattern of `H_a` directly,
  without any Gamma-product transport at all.

Together with the first-route correction above, this means the remaining
honest fork is now:

1. `Y_a`-specific exclusion of the **sparse** affine-lattice / Gamma-ratio
   mechanism;
2. or a genuinely non-Gamma two-sided transport / uniqueness theorem for the
   structured class `H_a=\Phi_a F`.

Nothing more generic should remain on the critical path.

At the current information level, branch 2 is the preferred fast route:
branch 1 now appears to touch deep arithmetic-progression questions for zeta
zeros, while branch 2 stays within the structured analytic package already
native to `PO2` even after the whole finite Gamma-family is removed.

#### External uniqueness scan: the real gap is now an orientation gap

The closest actual uniqueness theorems found so far are not generic folklore
claims but two concrete right-half-plane results:

- Yoshino's Carlson-type theorem for holomorphic functions on `\Re z>0`
  satisfying
  ```tex
  |F(z)|\le C_{\varepsilon,\varepsilon'}\exp(x\log x+k|y|+\varepsilon|z|)
  \qquad (x=\Re z>\varepsilon'),
  ```
  with `k<\pi/2`, from which `F(n)=0` on all natural numbers forces
  `F\equiv 0`;
- Pila's 2003 refinement, where one allows
  ```tex
  \limsup_{x\to+\infty}\frac{\log|f(x)|}{2x\log x}\le c,
  \qquad
  \limsup_{|y|\to\infty}\frac{\log|f(iy)|}{\pi|y|}\le \gamma,
  ```
  with `c+\gamma<1` and a routine global `O(|z|^{2-\delta})` bound.

The important point is structural: both theorems have the **same orientation**.
They allow the heavy `x\log x` growth on the **positive real axis** and only
linear/exponential-type control on the **imaginary axis**. Our structured
object `H_a=\Phi_a F` has the **transposed** boundary pattern:

```tex
H_a(x)=O_a(1)\quad (x\ge 0),
\qquad
\log|H_a(it)|\le \frac{\pi}{a}|t|\log|t|+O_a(|t|).
```

So the remaining second wall is no longer "find some Carlson theorem". It is
now much sharper:

```tex
\textbf{Rotated Pila--Yoshino target.}
```

Find either

1. a zero-free holomorphic factor `\Omega_a` on `\Re z\ge 0` such that
   `\Omega_a H_a` is pushed into the **Pila/Yoshino orientation**, i.e.
   heavy growth is moved from `i\mathbb R` to `\mathbb R_+`;
2. or a new uniqueness theorem that reads the **transposed** boundary pattern
   of `H_a` directly, without reducing to Pila/Yoshino.

This also sharpens the transport side. Since the entire finite shifted-Gamma
family is already dead, the only remaining transport mechanism would have to be
genuinely non-Gamma and genuinely two-sided. In practice this means the next
honest subtarget is one of:

- produce an explicit `\Omega_a` for which `\Omega_a H_a` satisfies a theorem
  of Pila/Yoshino type;
- or prove a half-plane Poisson/Herglotz obstruction showing that no zero-free
  holomorphic factor can simultaneously
  ```tex
  \text{damp } |t|\log|t| \text{ on both halves of } i\mathbb R
  ```
  and still keep only `O_a(x)` growth on `\mathbb R_+`.

At the current information level, this Poisson-style obstruction is the
fastest exact theorem target inside branch 2.

#### Standard outer/Herglotz transports are already incompatible

The Poisson/Herglotz obstruction can already be made precise for the entire
standard outer-function class on the right half-plane.

Assume `\Omega` is zero-free and holomorphic on `\Re z>0`, and that
`u(z):=\log |\Omega(z)|` lies in the standard half-plane outer/Nevanlinna
regime, so that `u` admits a Poisson-Herglotz representation with at most a
linear harmonic term:

```tex
u(x+iy)
=
\sigma x+c
+\frac{x}{\pi}\int_{\mathbb R}\frac{g(t)}{x^2+(y-t)^2}\,dt,
\qquad x>0,
```

where `g(t)` is the boundary log-modulus on `i\mathbb R` and
`\sigma,c\in\mathbb R` are finite.

Now impose the transport requirement needed for `PO2`:

```tex
g(t)\le
-\Bigl(\frac{\pi}{a}+\varepsilon\Bigr)|t|\log(2+|t|)+C_a|t|
\qquad (|t|\gg 1).
```

Then already on the positive real axis `y=0` the truncated Poisson tail is
forced negative with quadratic logarithmic size. For `T>R\gg 1`,

```tex
\frac{x}{\pi}\int_{R<|t|<T}\frac{g(t)}{x^2+t^2}\,dt
\le
-\frac{2x}{\pi}\Bigl(\frac{\pi}{a}+\varepsilon\Bigr)
\int_R^T \frac{t\log t}{x^2+t^2}\,dt
+ O_a\!\left(x\int_R^T \frac{dt}{t}\right).
```

But for fixed `x>0`,

```tex
\int_R^T \frac{t\log t}{x^2+t^2}\,dt
\sim
\frac12(\log T)^2,
\qquad
\int_R^T \frac{dt}{t}\sim \log T.
```

So the negative `(\log T)^2` contribution dominates the positive `O_a(\log T)`
drift. Letting `T\to+\infty`, the Poisson integral forces `u(x)=-\infty`,
impossible for a finite-valued holomorphic function.

Therefore:

```tex
\textbf{Outer/Herglotz obstruction.}
```

No zero-free transport factor `\Omega_a` with the required two-sided
`-|t|\log|t|` damping on `i\mathbb R` can lie in the standard
outer/Nevanlinna/Herglotz class while still having only finite linear harmonic
drift on `\Re z>0`.

This is already a meaningful family-level kill:

- the remaining transport, if any, must be genuinely **non-Gamma** and also
  genuinely **non-outer** in the standard half-plane sense;
- equivalently, branch 2 is no longer "find some outer factor". It is now:
  either an exotic zero-free transport outside the standard Herglotz regime,
  or a direct rotated uniqueness theorem for `H_a` itself.

So the second wall sharpens once more:

```tex
\textbf{Remaining second-route wall.}
```

At this point one more generic temptation must be killed immediately.

```tex
\textbf{Generic rotated uniqueness is false.}
```

The bare statement

```tex
H \text{ holomorphic on } \Re z>0,\quad
H(n)=0\ \forall n\in\mathbb N,\quad
H(x)=O(1)\text{ on }\mathbb R_+,\quad
\log|H(it)|=O(|t|\log|t|)
```

does **not** force `H\equiv 0`. A trivial counterexample is

```tex
H(z)=\sin(\pi z),
```

which is holomorphic on the whole plane, vanishes on every integer, stays
bounded on the positive real axis, and satisfies

```tex
\log|\sin(\pi it)|
=
\log|\sinh(\pi t)|
=
\pi|t|+O(1),
```

which is far below the allowed `|t|\log|t|` ceiling.

So option 1 cannot mean a theorem for **all** holomorphic functions with this
boundary pattern. The Cauchy/xi structure must now be consumed explicitly.

The real direct target is therefore a theorem for the structured class

```tex
\mathcal H_a^{\mathrm{str}}
:=
\left\{
H(z)=\Phi_a(z)\sum_{y\in Y_a}\frac{e(y)}{y-z}
:\ e\in \ell^1(Y_a)
\right\},
\qquad
Y_a=\{x_\gamma,\ x_\gamma-1\}.
```

In the actual `PO2` application this class is even smaller, because the
coefficients inherited from the mixed defect have the stronger decay coming
from three Cauchy denominators in `\gamma`; but already the class
`\mathcal H_a^{\mathrm{str}}` is the correct theorem-sized receiver.

But even this is not yet the **minimal** direct receiver. Earlier in the
reduction we already reached the sharper form

```tex
H(z)=e^{i\pi z}\Delta J(z),
\qquad
J(z)=P(z)-Q(z+1),
\qquad
P,Q\in \mathcal C_a,
```

with

```tex
\mathcal C_a
:=
\left\{
\sum_\gamma c_\gamma f_\gamma(z)
\right\},
\qquad
f_\gamma(z)=\frac{1}{x_\gamma-z}.
```

So for the actual `PO2` wall, the theorem does not need to mention arbitrary
elements of `\mathcal H_a^{\mathrm{str}}`. The proof-critical core is already
the simple-pole shift equality problem.

Hence the remaining second-route wall should be rewritten one step more
economically:

Either

1. prove the **minimal shift-uniqueness receiver**
   ```tex
   P,Q\in \mathcal C_a,
   \qquad
   P(m)=Q(m+1)\ \forall m>N
   \Longrightarrow
   P(z)=Q(z+1)\ \text{ identically};
   ```
   equivalently, in Cauchy-tail form,
   ```tex
   \sum_{y\in Y_a}\frac{e(y)}{y-m}=0\ \forall m>N
   \Longrightarrow e\equiv 0,
   ```
   but now understood only for the actual structured support/coefficients
   inherited from `PO2`;
2. or exhibit an explicit transport mechanism outside the standard
   outer/Nevanlinna/Herglotz class.

At the present information level, option 1 is now the preferred fast route
inside branch 2.

#### Coefficient class actually inherited from `PO2`

The live `PO2` coefficients are not arbitrary. In the original meromorphic
kernel

```tex
\mathbf K^{+-}(z,n)
=
\frac{4\pi^3}{a^4}
\sum_\gamma \sin^2(a\gamma)\,
\bigl(\mathbf u_\gamma(z)v_\gamma(n)-\mathbf v_\gamma(z)u_\gamma(n)\bigr),
```

for each fixed tail index `n` one has

```tex
u_\gamma(n),v_\gamma(n)=O(\gamma^{-3})
\qquad(\gamma\to+\infty),
```

because each carries three Cauchy denominators in `\gamma`. Hence every
scalar combination produced in the residue-upgrade reduction has coefficients

```tex
c_\gamma,d_\gamma=O(\gamma^{-3}),
```

uniformly up to the finite column-span coefficients coming from the discrete
rank assumption.

Since the positive zero counting law is

```tex
N_\zeta(T)\sim \frac{T\log T}{2\pi},
```

this decay is absolutely summable:

```tex
\sum_{\gamma>0} |c_\gamma|+\sum_{\gamma>0}|d_\gamma|<\infty.
```

Equivalently, in the Cauchy-tail formulation the coefficient function on
`Y_a` belongs to `\ell^1(Y_a)`.

So the live infinite-support wall is now narrower than a completely arbitrary
Cauchy transform problem. What remains is:

```tex
\textbf{\ell^1-Cauchy-tail injectivity (target).}
```

If `e\in \ell^1(Y_a)` and

```tex
\sum_{y\in Y_a}\frac{e(y)}{y-m}=0
\qquad\forall m>N,
```

must one have `e\equiv 0`?

This is the exact infinite-support hypothesis still needed by `PO2`.

This gives a strict descent:

- if `H(m)=0` for all `m>N`, then `\Delta G(m)=0` for all `m>N`;
- hence `G(m)` is constant on the integer tail;
- because every generator of `\mathcal N_a` is `O(m^{-1})` or better, one has
  `G(m)\to 0` as `m\to+\infty` along the integers, so in fact `G(m)=0` on the
  whole tail.

Thus scalar uniqueness for `\mathcal M_a` reduces to scalar uniqueness for the
simpler class `\mathcal N_a`:

```tex
G\in\mathcal N_a,\qquad G(m)=0\ \forall m>N \Longrightarrow G\equiv 0.
```

This is not yet the end, but it removes one exact layer of the mixed-block
difficulty: the three-pole class collapses to a two-pole / one-pole class
before any genuinely new uniqueness theorem is needed.

### L3''''''''''. Numerical smoke test for the finite-rank test

As a quick diagnostic only, using the local fixed list of the first 20
positive zeta zeros already embedded in `src/q3_corrected_model.py`, the
anti-diagonal defect

```tex
K_{mn}^{+-}(a)=M_{m+1,n}^{+-}(a)-M_{m,n+1}^{+-}(a)
```

does **not** look automatically zero on moderate tail indices.
Representative values from the raw zero-sum formula are:

```text
a = 0.5:
  K_{20,18}^{+-} ≈ -4.29e-06
  K_{30,25}^{+-} ≈  2.23e-07
  K_{40,39}^{+-} ≈  2.21e-09

a = 1.0:
  K_{20,18}^{+-} ≈ -1.02e+00
  K_{30,25}^{+-} ≈  4.96e-03
  K_{40,39}^{+-} ≈  4.69e-08

a = 1.7:
  K_{20,18}^{+-} ≈ -2.73e+00
  K_{30,25}^{+-} ≈  1.10e-01
  K_{40,39}^{+-} ≈ -3.87e+00.
```

Interpretation:

- this is **not** a theorem and not a kill certificate by itself;
- it is only a smoke test on a short zero list;
- but it does show that the new `K_{mn}^{+-}` test is not vacuous:
  the mixed block does not appear to satisfy automatic anti-diagonal symmetry
  for free.

A stronger smoke test is the singular-value profile of the truncated
anti-diagonal defect matrix `K^{+-}` built from the same short zero list.
For example:

```text
a = 0.5, M = 16:
  top singular values ≈ 10.26, 10.26, 7.35, 7.35, 4.74, 4.74
  top-6 energy share ≈ 0.964

a = 1.0, M = 16:
  top singular values ≈ 9.16, 9.16, 7.17, 7.17, 5.50, 5.50
  top-6 energy share ≈ 0.862

a = 1.7, M = 16:
  top singular values ≈ 7.29, 7.29, 5.89, 5.89, 5.60, 5.60
  top-6 energy share ≈ 0.882
```

So at least on this short diagnostic sample, the truncated mixed
anti-diagonal defect does not behave like an obviously tiny-rank perturbation.

So the exact burden remains unchanged:

- either prove that the full infinite zero sum makes `K^{+-}` finite rank
  modulo cap;
- or prove that the wedge family above cannot collapse to finite rank, which
  kills the current theorem shape.

### What not to do inside these lemmas

- do not revive the dead global raw identity `w_{rs}(a)=\kappa(a)q_{rs}`;
- do not move to finite sections first;
- do not let `(++)` leak into the argument;
- do not accept a “small numerically” cross-sign residue.

### Immediate theorem fork

After `L1` and `L2`, the proof splits cleanly:

1. either `L3` lands exactly and `PO2` is done;
2. or `L3` fails but the residual is already theorem-grade
   `\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
3. or an unnamed bulk residue survives and kills the route.

## Admissible remainder channels after `PO2`

If `PO2` lands, only these channels may still remain in `(+,-)`:

| Channel | Allowed after `PO2`? | Why |
| --- | --- | --- |
| `\mathcal D_{a,\partial}^{+-}` | yes, temporarily | it is the exact subject of `PO3` |
| `\mathcal D_{a,\mathrm{cap}}^{+-}` | yes | cap-only fallback remains admissible |
| unnamed bulk residue | no | route-kill |
| finite compression term | no at this stage | belongs later to `PO6`, not to the tail bulk theorem |

## Route-kill condition

The current theorem picture dies immediately if `PO2` produces:

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+ \text{other terms},
\qquad
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0,
```

with no operator-theoretic reclassification into boundary or cap.

In words:

```text
an unnamed persistent cross-sign bulk residue kills the boundary/cap reset.
```

## Preferred theorem fork

### Best case

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{cap}}^{+-},
```

with preferred stronger version

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0.
```

### Acceptable pre-`PO3` case

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-},
```

where `\mathcal D_{a,\partial}^{+-}` is now a named residual targeted next by
`PO3`.

This is also the right place to name cap explicitly without letting the cap
analysis consume the `PO2` proof itself.

### Failure case

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0.
```

This is not “one more correction channel”. It is the exact route-kill event.

## Exact handoff to `PO3`

If `PO2` lands in acceptable form, the next note should not reopen the whole
cross-sign story. It should read only:

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So the correct handoff contract is:

- `PO2` is allowed to leave a named boundary term;
- `PO3` is required to kill it;
- the cap channel may remain explicit throughout this handoff;
- compression stays out of scope until `PO6`.

This is exactly the part of the worker report worth keeping: the handoff should
remain one-line and asymmetric, not reopen the full cross-sign classifier.

## Ingest checklist for worker input

If a parallel worker report arrives on `PO2`, it should be judged against the
following checklist rather than absorbed wholesale.

### Keep immediately

- an exact theorem-shaped statement equivalent to
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- an equivalent `boundary/cap-only` reformulation;
- a sharper route-kill condition than the one already recorded here;
- a cleaner handoff contract from `PO2` to `PO3`.

### Keep only as supporting rationale

- operator-theoretic explanation of why cross-sign bulk should vanish;
- comparison with the same-sign block that sharpens the asymmetry;
- clarification of whether the cap channel should already be named in `PO2`.

### Reject on sight

- anything that reopens rank/basis language;
- anything that introduces finite-section numerics into `PO2`;
- anything that treats a surviving unnamed bulk residue as “still acceptable”;
- any attempt to turn `PO2` into a same-sign `(++)` theorem.

## Local next move if no worker result lands

If the worker remains silent, the next local tightening should be:

1. rewrite `PO2a` as one exact lemma statement plus one equivalent finite-shadow
   corollary;
2. make explicit whether the preferred theorem output is exact cross-sign
   identity or cap-only fallback;
3. only then advance to `PO3`.

## What `PO2` must not do

- no finite-section compression bookkeeping;
- no rank/basis language;
- no same-sign boundary discussion beyond contrast;
- no premature positivity/cap-absorption claims.

## Immediate next receiver

If `PO2` lands, the next packet is forced:

```tex
PO3:
\qquad
\mathcal D_{a,\partial}^{+-}=0.
```

Only after that does the route spend proof energy on the same-sign channel
`H_a^{\mathrm{ss}}`.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one exact bulk-vanishing lemma for `\mathcal D_{a,N}^{+-}`;
- one explicit theorem fork saying the only admissible remainder is
  boundary/cap-only.
