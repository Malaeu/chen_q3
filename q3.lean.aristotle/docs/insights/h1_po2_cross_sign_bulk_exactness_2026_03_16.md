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

#### Direct divisor closure inside the simple Cauchy class

There is now a receiver-native divisibility lemma that stays entirely inside
the direct `PO2` class.

Let

```tex
R(z)=\sum_{y\in Y_a}\frac{e(y)}{y-z},
```

with the inherited `\ell^1` coefficient class, and assume that `a\in\mathbb Z`
is one of the tail zeros:

```tex
R(a)=0,
\qquad
a>N.
```

Then division by `(z-a)` preserves the same simple Cauchy class. Indeed,
partial fractions give

```tex
\frac{1}{(y-z)(z-a)}
=
\frac{1}{y-a}\left(\frac{1}{y-z}+\frac{1}{z-a}\right).
```

Hence

```tex
\frac{R(z)}{z-a}
=
\sum_{y\in Y_a}\frac{e(y)}{y-a}\frac{1}{y-z}
\frac{1}{z-a}\sum_{y\in Y_a}\frac{e(y)}{y-a}.
```

But the last sum is exactly `R(a)=0`, so

```tex
\frac{R(z)}{z-a}
=
\sum_{y\in Y_a}\frac{e(y)}{y-a}\frac{1}{y-z}.
```

Thus every tail zero yields a new coefficient sequence

```tex
e^{(a)}(y):=\frac{e(y)}{y-a}
```

inside the same simple-pole receiver class.

Repeating this at the first `k` tail integers gives

```tex
R_k(z)
:=
\frac{R(z)}{\prod_{j=1}^k (z-(N+j))}
=
\sum_{y\in Y_a}
\frac{e(y)}{\prod_{j=1}^k (y-(N+j))}\frac{1}{y-z},
```

and `R_k(m)=0` for every integer `m>N+k`.

So the direct route has acquired its own intrinsic divisor tower, parallel to
the earlier `G_k`-tower but staying completely inside the original
simple Cauchy receiver.

This sharpens the active direct branch:

```tex
\textbf{D1. Direct divisor closure.}
```

Tail-zero division preserves the structured simple Cauchy class.

```tex
\textbf{D2. Direct divisor-rigidity target.}
```

Can an arbitrarily long tail-zero divisor tower exist in this paired support
class without forcing `e\equiv 0`?

There is now a much sharper theorem-shape for `D2`.

Fix any `z_0\notin Y_a`, and define the Gamma-profile family

```tex
u_k(x)
:=
\frac{1}{\prod_{j=1}^k (x-(N+j))}
=
(-1)^k\frac{\Gamma(N+1-x)}{\Gamma(k+N+1-x)}.
```

Since

```tex
R_k(z)=\frac{R(z)}{\prod_{j=1}^k (z-(N+j))},
```

evaluating at `z_0` gives for every `k\ge 0`

```tex
R(z_0)\,u_k(z_0)
=
\sum_{y\in Y_a}\frac{e(y)}{y-z_0}\,u_k(y).
```

So the direct receiver problem is equivalent to a profile-rigidity statement:

```tex
\textbf{D2a. Gamma-profile rigidity.}
```

Can one have an identity

```tex
u_k(z_0)
=
\sum_{y\in Y_a} c_y\,u_k(y)
\qquad \forall k\gg 1,
```

with `c\in \ell^1(Y_a)` and `z_0\notin Y_a`, without forcing all
`c_y=0`?

The finite-support shadow is immediate from asymptotics: by DLMF §5.11.13,

```tex
\frac{\Gamma(k+a)}{\Gamma(k+b)}
\sim
k^{a-b},
```

hence for fixed `x`

```tex
u_k(x)\sim C(x)\,k^{x-N-1},
\qquad
C(x):=(-1)^k\Gamma(N+1-x).
```

So distinct support points give distinct power exponents. If the coefficient
support had a rightmost point, that maximal exponent would dominate and force
its coefficient to vanish.

This shows exactly where the infinite-support difficulty sits:

```tex
\textbf{D2b. Right-tail obstruction.}
```

Any genuine infinite-support counterexample to `D2a` must use support points
running arbitrarily far to the right, so that no maximal exponent exists.
Therefore the real theorem is not a finite Vandermonde statement, but a
no-cancellation result for an `\ell^1` superposition of profiles with
unbounded exponents.

The next honest split inside `D2` is now:

```tex
\textbf{D2c. Finite right-packet dominance.}
```

For fixed `y>y'`,

```tex
\frac{u_k(y)}{u_k(y')}
\sim
\frac{\Gamma(N+1-y)}{\Gamma(N+1-y')}\,k^{y-y'}.
```

So every fixed support point farther to the right eventually dominates every
fixed support point to its left.

```tex
\textbf{D2d. Tail-integral upgrade.}
```

To close `D2`, one would need to upgrade this finite-packet dominance to a
statement about the whole unbounded support, using the actual inherited
coefficient decay `e(y)=O(\gamma^{-3})` and the zero-density geometry of
`Y_a=\{x_\gamma,x_\gamma-1\}`.

In other words, the direct route is no longer “show the tower cannot exist”
in the abstract. It is:

```tex
\boxed{
\text{prove that an }\ell^1\text{-superposition of Gamma profiles with support in }Y_a
\text{ cannot represent one external profile }u_k(z_0).
}
```

There is now a cleaner static reformulation of the actual profile-rigidity
statement itself, but it must include the external profile point `z_0`.

Fix `z_0\notin Y_a` and assume `R(z_0)\neq 0`. Normalize the profile identity
by dividing through by `R(z_0)`:

```tex
u_k(z_0)
=
\sum_{y\in Y_a} c_y(z_0)\,u_k(y),
\qquad
c_y(z_0):=\frac{e(y)}{R(z_0)(y-z_0)}.
```

Now augment the support by the external point:

```tex
\widehat Y_{a,z_0}:=Y_a\cup\{z_0\},
```

and define coefficients on this enlarged support by

```tex
\widehat e_{z_0}(z_0):=-1,
\qquad
\widehat e_{z_0}(y):=c_y(z_0)\quad (y\in Y_a).
```

Then the profile identity is exactly the vanishing tower

```tex
\sum_{w\in \widehat Y_{a,z_0}} \widehat e_{z_0}(w)\,u_k(w)=0
\qquad \forall k\ge 0.
```

Now fix `w\notin \{N,N+1,\dots\}` and set `g_w(x):=1/(w-x)`. A direct
induction on the forward difference operator
`\Delta f(x):=f(x+1)-f(x)` gives

```tex
\Delta^k g_w(N)
=
\frac{k!}{\prod_{j=0}^k (w-(N+j))}.
```

Hence for the Gamma-profile family

```tex
u_k(w):=\frac{1}{\prod_{j=1}^k (w-(N+j))},
\qquad
u_0(w):=1,
```

one has the exact avatar

```tex
u_k(w)
=
\frac{w-N}{k!}\,\Delta^k\!\left(\frac{1}{w-x}\right)\Big|_{x=N}.
```

Define the static reweighted transform on the augmented support

```tex
\widehat R_{N,z_0}(z)
:=
\sum_{w\in \widehat Y_{a,z_0}}
\frac{(w-N)\widehat e_{z_0}(w)}{w-z}.
```

Then summing the difference formula against `\widehat e_{z_0}(w)` yields

```tex
\sum_{w\in \widehat Y_{a,z_0}} \widehat e_{z_0}(w)\,u_k(w)
=
\frac{1}{k!}\,\Delta^k \widehat R_{N,z_0}(N).
```

By Newton's forward formula,

```tex
f(N+m)=\sum_{k=0}^m \binom{m}{k}\Delta^k f(N),
```

so the moving profile identity is equivalent to tail vanishing of one fixed
transform:

```tex
u_k(z_0)=\sum_{y\in Y_a} c_y(z_0)\,u_k(y)\ \forall k\ge 0
\iff
\widehat R_{N,z_0}(N+m)=0\ \forall m\ge 0.
```

This is the correct static direct target.

```tex
\textbf{D2e. Static augmented Cauchy uniqueness.}
```

Prove that for every `z_0\notin Y_a`, the augmented transform satisfies

```tex
\widehat R_{N,z_0}(N+m)=0\ \forall m\ge 0
\Longrightarrow
\widehat R_{N,z_0}\equiv 0.
```

This is now perfectly aligned with the actual `D2` burden. The moving
Gamma-profile family disappears from the theorem statement, but the external
point `z_0` is retained as one extra pole of the static transform.

Admissibility also survives: on `Y_a` the coefficients satisfy
`e(y)=O(\gamma^{-3})`, division by `y-z_0` improves this to `O(\gamma^{-4})`,
and reweighting by `y-N` returns only `O(\gamma^{-3})`, so the enlarged
coefficient family still lies in `\ell^1` after adjoining the single point
`z_0`.

There is one more exact simplification of `D2e`. Evaluating the tail-zero
condition for `\widehat R_{N,z_0}` at the integer points `N+m` gives

```tex
0=
\widehat R_{N,z_0}(N+m)
=
-\frac{z_0-N}{z_0-(N+m)}
+\sum_{y\in Y_a}\frac{(y-N)c_y(z_0)}{y-(N+m)}.
```

So `D2e` is equivalent to the following static kernel-representation problem
on the positive integer tail.

```tex
\textbf{D2f. Static kernel-representation uniqueness.}
```

For every `z_0\notin Y_a`, prove that the identity

```tex
\frac{z_0-N}{z_0-(N+m)}
=
\sum_{y\in Y_a}\frac{(y-N)c_y(z_0)}{y-(N+m)}
\qquad \forall m\ge 0
```

cannot hold for any nontrivial `\ell^1` coefficient family on `Y_a`.

This is stronger as a theorem target than the moving Gamma-profile statement:
the family parameter `k` is gone, the auxiliary augmented support is gone from
the statement, and the obstruction is now concentrated in one explicit kernel
representation along the integer tail.

The finite-support shadow is immediate. If only finitely many `c_y(z_0)` were
nonzero, then both sides would be rational functions of `m`, and the pole at
`m=z_0-N` on the left could not be generated by poles only at
`m=y-N` with `y\in Y_a`, because `z_0\notin Y_a`. Hence every genuine
counterexample to `D2f` must again use infinite support.

So the whole direct route is now concentrated in a single honest upgrade:

```tex
\textbf{D2f1. Infinite-support tail uniqueness.}
```

Upgrade the obvious finite-support pole-separation argument to the actual
infinite paired support `Y_a=\{x_\gamma,x_\gamma-1\}` with inherited
coefficient decay.

The next live split inside `D2f1` is now very concrete. Write

```tex
d_y(z_0):=(y-N)c_y(z_0),
\qquad
K_{z_0}(m):=\frac{z_0-N}{z_0-(N+m)}.
```

Then the static representation reads

```tex
K_{z_0}(m)=\sum_{y\in Y_a}\frac{d_y(z_0)}{y-(N+m)}.
```

Because the inherited coefficients satisfy `e(y)=O(\gamma^{-3})`, we also
have

```tex
d_y(z_0)=O(\gamma^{-3}),
```

and the local zero count on the critical line gives the natural packet bound

```tex
\#\bigl(Y_a\cap [t-1,t+1]\bigr)\ll_a \log(2+t).
```

So for every unit packet around the tail integer `N+m`,

```tex
\sum_{\substack{y\in Y_a\\ |y-(N+m)|<1}} |d_y(z_0)|
\ll_a \frac{\log(2+m)}{m^3}.
```

This produces the next exact theorem packet.

```tex
\textbf{D2f2. No-resonance asymptotic lemma.}
```

If a subsequence `m_r\to\infty` satisfies the lower-gap condition

```tex
\rho_{m_r}:=
\min\bigl\{|y-(N+m_r)|:\ y\in Y_a,\ |y-(N+m_r)|<1\bigr\}
\gg_\omega \frac{\log m_r}{m_r^2},
```

then the near packet contributes only `o(m_r^{-1})`, and the whole
representation should collapse to the first-order asymptotic

```tex
K_{z_0}(m_r)
\sim
-\frac{1}{m_r}\sum_{y\in Y_a} d_y(z_0).
```

Since the left side satisfies

```tex
K_{z_0}(m)
\sim
-\frac{z_0-N}{m},
```

this would force the moment identity

```tex
\sum_{y\in Y_a} d_y(z_0)=z_0-N.
```

There is now a clean proof skeleton for this claim. Set `M_r:=N+m_r`. Then

```tex
M_r\,K_{z_0}(m_r)
=
\sum_{y\in Y_a} d_y(z_0)\,\frac{M_r}{y-M_r}
=
-\sum_{y\in Y_a} d_y(z_0)
+\sum_{y\in Y_a} d_y(z_0)\,\frac{y}{y-M_r}.
```

The second sum can be split into three regions:

```tex
\{y\le M_r/2\},
\qquad
\{M_r/2<y,\ |y-M_r|\ge 1\},
\qquad
\{|y-M_r|<1\}.
```

For the left region,

```tex
\left|\frac{y}{y-M_r}\right|
\le
\frac{2y}{M_r},
```

so absolute convergence of `\sum_y |d_y(z_0)|\,y` gives an `O(M_r^{-1})` tail.
For the middle region one simply uses `|y-M_r|\ge 1` and
`y\asymp M_r`, so the contribution is bounded by the first-moment tail

```tex
\sum_{y\ge M_r/2} |d_y(z_0)|\,y,
```

which tends to zero because `d_y(z_0)=O(\gamma^{-3})` and the local counting
bound imply `\sum_y |d_y(z_0)|\,y<\infty`.

For the resonant packet,

```tex
\left|\sum_{\substack{y\in Y_a\\ |y-M_r|<1}}
d_y(z_0)\,\frac{y}{y-M_r}\right|
\ll
M_r\,
\frac{(\log M_r)/M_r^3}{\rho_{m_r}}
=
\frac{\log M_r}{M_r^2\,\rho_{m_r}}
=
o(1)
```

under the lower-gap assumption
`\rho_{m_r}\gg_\omega (\log m_r)/m_r^2`, meaning

```tex
\frac{m_r^2\,\rho_{m_r}}{\log m_r}\longrightarrow \infty.
```

The weaker condition `\rho_{m_r}\gg (\log m_r)/m_r^2` would give only
`O(1)`, not `o(1)`, for the resonant packet after multiplying by `M_r`. Hence

```tex
M_r\,K_{z_0}(m_r)\longrightarrow -\sum_{y\in Y_a} d_y(z_0).
```

Since also

```tex
M_r\,K_{z_0}(m_r)\longrightarrow -(z_0-N),
```

the moment identity follows.

This already yields a concrete structural consequence for any no-resonance
counterexample:

```tex
\textbf{D2f2a. Zeroth-moment cancellation.}
```

Because

```tex
d_y(z_0)=\frac{(y-N)e(y)}{R(z_0)(y-z_0)},
```

the identity `\sum_y d_y(z_0)=z_0-N` is equivalent to

```tex
\sum_{y\in Y_a}\frac{(y-N)e(y)}{y-z_0}
=
(z_0-N)R(z_0).
```

Expanding `y-N=(y-z_0)+(z_0-N)` gives

```tex
\sum_{y\in Y_a} e(y)
+
(z_0-N)\sum_{y\in Y_a}\frac{e(y)}{y-z_0}
=
(z_0-N)R(z_0),
```

and therefore

```tex
\boxed{
\sum_{y\in Y_a} e(y)=0.
}
```

So the no-resonance branch does not merely give an asymptotic; it already
forces zeroth-moment cancellation for the original paired receiver.

There is also now a useful negative result about the next obvious upgrade.
Trying to push the same argument one order further would require the formal
expansion

```tex
\frac{1}{y-M}
=
-\frac{1}{M}-\frac{y}{M^2}+O\!\left(\frac{y^2}{M^2|y-M|}\right),
```

and after summing this would naturally demand absolute control of the second
moment tail

```tex
\sum_{y\in Y_a} |d_y(z_0)|\,y^2.
```

But with the inherited decay `d_y(z_0)=O(\gamma^{-3})` and the local counting
bound `\#(Y_a\cap[t-1,t+1])\ll_a \log(2+t)`, the unit packet at height `t`
contributes only

```tex
\sum_{y\in Y_a\cap[t-1,t+1]} |d_y(z_0)|\,y^2
\ll_a
\frac{\log(2+t)}{t},
```

and the sum over packets diverges. So there is no routine absolute-convergence
path from `D2f2` to a second-order asymptotic or a first-moment identity.

```tex
\textbf{D2f2b. Naive second-order moment extraction is blocked.}
```

This is a good kill certificate, not a setback. It means the first-order
no-resonance asymptotic is the last generic layer available from the current
decay alone. Any further upgrade now has to use genuinely new structure:
either pairwise cancellation between `x_\gamma` and `x_\gamma-1`, or the
ultra-near resonance branch `D2f3`.

So the threshold scale `(\log m)/m^2` is now the exact borderline:

- above this scale by a diverging factor, the generic first-order asymptotic
  works and forces `\sum_{y\in Y_a} e(y)=0`;
- at this scale itself, the generic argument no longer closes, and the only
  remaining hope is the paired correction-term mechanism `D2g1`;
- below this scale, the route is already inside the resonance branch `D2f3`.

That missing “new structure” can now be isolated exactly. Write

```tex
e_\gamma^+:=e(x_\gamma),
\qquad
e_\gamma^-:=e(x_\gamma-1).
```

Then the original tail-zero identity

```tex
0=\sum_{y\in Y_a}\frac{e(y)}{y-M}
```

becomes

```tex
0=
\sum_\gamma \frac{e_\gamma^+}{x_\gamma-M}
+
\sum_\gamma \frac{e_\gamma^-}{x_\gamma-1-M}.
```

Using

```tex
\frac{1}{u-1}=\frac{1}{u}+\frac{1}{u(u-1)},
```

with `u=x_\gamma-M`, this rewrites exactly as

```tex
0=
\sum_\gamma \frac{p_\gamma}{x_\gamma-M}
+
\sum_\gamma \frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)},
```

where

```tex
p_\gamma:=e_\gamma^+ + e_\gamma^-,
\qquad
q_\gamma:=e_\gamma^-.
```

Because `\sum_{y\in Y_a} e(y)=0`, the one-sided main coefficients satisfy

```tex
\sum_\gamma p_\gamma=0.
```

This is the exact paired upgrade of `D2f2`.

```tex
\textbf{D2g. Paired main-term / correction-term split.}
```

The first series now lives on the one-sided support `X_a=\{x_\gamma\}` and has
zero total mass, so under no-resonance one expects

```tex
M\sum_\gamma \frac{p_\gamma}{x_\gamma-M}\longrightarrow 0
```

from first-moment summability alone.

The whole obstruction to pushing beyond zeroth-moment cancellation is
therefore concentrated in the paired correction term

```tex
\sum_\gamma \frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)}.
```

This yields the next exact theorem packet.

```tex
\textbf{D2g1. Local paired-correction control.}
```

Either prove that the resonant packet contribution of the correction term is
`o(M^{-1})` on some no-resonance subsequence by using actual pairwise residue
structure, or else the route is forced back into `D2f3`.

There is now a sharper quantitative form of this borderline problem. Fix
constants `0<c<C<\infty`, let `M=N+m`, and define the threshold packet

```tex
\mathcal P_M(c,C):=
\left\{
\gamma:
c\,\frac{\log M}{M^2}
\le |x_\gamma-M|
\le C\,\frac{\log M}{M^2}
\right\}.
```

Assume we are outside the ultra-near branch `D2f3`, so that along the
subsequence under study no support point enters the smaller scale
`o((\log M)/M^2)`. Then for every `\gamma\in\mathcal P_M(c,C)` one has

```tex
|x_\gamma-1-M|\ge 1-C\frac{\log M}{M^2}\ge \frac12
```

for all large `M`, while

```tex
|q_\gamma|=|e_\gamma^-|\ll_a x_\gamma^{-3}\ll_a M^{-3}.
```

Therefore the borderline packet of the paired correction term satisfies

```tex
\left|
M\sum_{\gamma\in\mathcal P_M(c,C)}
\frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)}
\right|
\ll_{a,c,C}
\frac{\#\mathcal P_M(c,C)}{\log M}.
```

This has an immediate consequence:

```tex
\textbf{D2g2. Borderline microcluster obstruction.}
```

If along some subsequence one has

```tex
\#\mathcal P_M(c,C)=o(\log M),
```

then the whole threshold packet is already `o(1)` after multiplying by `M`,
hence `o(M^{-1})` before rescaling. So any genuine failure of `D2g1` outside
`D2f3` must produce packets with

```tex
\#\mathcal P_M(c,C)\gtrsim \log M.
```

Since local zero counting still gives only

```tex
\#(Y_a\cap [M-1,M+1])\ll_a \log M,
```

this means that a borderline counterexample would need a near-maximal
logarithmic microcluster of support points inside a microscopic window of width
`\asymp (\log M)/M^2`.

There is now a further reduction from the paired support `Y_a` to the
one-sided support `X_a=\{x_\gamma\}`. Write

```tex
\mathcal P_M(c,C)=\mathcal P_M^{(+)}(c,C)\sqcup \mathcal P_M^{(-)}(c,C),
```

where

```tex
\mathcal P_M^{(+)}(c,C):=
\left\{
\gamma:\ c\,\frac{\log M}{M^2}
\le |x_\gamma-M|
\le C\,\frac{\log M}{M^2}
\right\},
```

and

```tex
\mathcal P_M^{(-)}(c,C):=
\left\{
\gamma:\ c\,\frac{\log M}{M^2}
\le |x_\gamma-(M+1)|
\le C\,\frac{\log M}{M^2}
\right\}.
```

Since the paired poles are separated by exactly `1`, these two packets are
disjoint for all large `M`, and

```tex
\#\mathcal P_M(c,C)
=
\#\mathcal P_M^{(+)}(c,C)+\#\mathcal P_M^{(-)}(c,C).
```

Hence any packet with `\#\mathcal P_M(c,C)\gtrsim \log M` forces one of the
two one-sided packets to satisfy

```tex
\max\{\#\mathcal P_M^{(+)}(c,C),\#\mathcal P_M^{(-)}(c,C)\}\gtrsim \log M.
```

This gives the next direct consequence.

```tex
\textbf{D2g3. Gap-extraction from borderline microclusters.}
```

If along some subsequence

```tex
\#\mathcal P_M(c,C)\ge \eta \log M
```

for some `\eta>0`, then for infinitely many such `M` there exists a block of
at least `( \eta/2)\log M` points of `X_a` inside an interval of length
`\ll_C (\log M)/M^2` around either `M` or `M+1`. Ordering those points and
using the pigeonhole principle, one obtains a consecutive one-sided gap

```tex
x_{\gamma+1}-x_\gamma \ll_{\eta,C} \frac{1}{M^2}.
```

Since `x_\gamma=(a/\pi)\gamma`, this is equivalent to an actual zeta-zero
spacing

```tex
\gamma_{n+1}-\gamma_n \ll_{a,\eta,C} \frac{1}{\gamma_n^2}
```

along an infinite subsequence.

So the current direct route has sharpened again:

- either `D2g1` is true and the borderline packet is negligible;
- or `D2g2` forces a logarithmic microcluster on the paired support;
- and then `D2g3` forces infinitely many one-sided critical-line gaps of order
  `O(M^{-2})`.

There is also now a clean local theorem for exact finite paired corrections.
Consider a finite one-sided paired correction term

```tex
K(z)=\sum_{j=1}^L c_j\left(\frac{1}{a_j-z}-\frac{1}{b_j-z}\right),
\qquad
a_j<b_j<N+1,
```

and assume

```tex
K(N+m)=0\qquad \forall m\ge 1.
```

Let `V=\{a_1,b_1,\dots,a_L,b_L\}` and define the divergence on vertices by

```tex
d(v):=
\sum_{j:a_j=v} c_j
\;-\!
\sum_{j:b_j=v} c_j.
```

Then exact regrouping gives

```tex
K(z)=\sum_{v\in V}\frac{d(v)}{v-z}.
```

Since all vertices lie in `(-\infty,N+1)`, one-sided tail-zero rigidity
implies

```tex
d(v)=0\qquad \forall v\in V.
```

Now form the finite pair-graph with vertex set `V` and one oriented edge
`a_j\to b_j` of weight `c_j` for each pair. If the underlying undirected graph
is a forest, then every divergence-free flow on it is zero: strip a leaf,
observe that its unique incident edge must have zero weight, delete that edge,
and continue inductively.

This yields:

```tex
\textbf{D2g4. Finite forest kill for exact local paired corrections.}
```

If a finite one-sided paired correction term has tail zeros and its pair-graph
is acyclic, then all coefficients vanish.

So any nontrivial exact finite local paired correction with one-sided tail
zeros must carry cycle structure.

So the direct route is now split with no ambiguity:

- `D2f2` gives the generic zeroth-moment cancellation `\sum e(y)=0`;
- `D2f2b` kills the naive second generic layer;
- `D2g1` names the only remaining no-resonance upgrade: local cancellation in
  the paired correction term;
- `D2g2` sharpens this: unless there is a logarithmic microcluster on the
  exact threshold scale, the borderline packet is already negligible;
- `D2g3` pushes any such microcluster down to one-sided gaps
  `x_{\gamma+1}-x_\gamma\ll M^{-2}`;
- `D2g4` kills every exact finite aциклический local correction packet, so any
  surviving exact local correction must already carry cycles;
- failing that, only the ultra-near resonance obstruction `D2f3` remains live.

Important boundary of applicability:

- `D2g4` is a real theorem, but only for exact finite one-sided paired
  corrections with tail zeros;
- it does not yet close the live global `D2g1`, because we still do not know
  how to exact-truncate the full infinite paired correction term to such a
  finite packet while preserving all tail zeros.

There is now a stronger finite-window upgrade of this local picture. Fix
distinct vertices

```tex
V=\{v_1,\dots,v_L\}\subset (-\infty,N+1),
```

let `x_m:=N+m` for `m=1,\dots,L`, and consider a finite oriented pair-graph
`G` on `V` with edges `e_j:a_j\to b_j` and coefficients `c=(c_1,\dots,c_M)^T`.
Define the local paired packet

```tex
K_c(z):=\sum_{j=1}^M c_j\left(\frac{1}{a_j-z}-\frac{1}{b_j-z}\right),
```

and its first `L` tail samples

```tex
s(c):=\bigl(K_c(N+1),\dots,K_c(N+L)\bigr)^T\in \mathbb C^L.
```

Introduce:

- the finite Cauchy sample matrix

```tex
C_V:=\left(\frac{1}{v_i-(N+m)}\right)_{m=1,\dots,L}^{i=1,\dots,L},
```

- and the incidence matrix `B_G\in M_{L\times M}(\mathbb C)`, whose `j`-th
  column has `+1` at `a_j`, `-1` at `b_j`, and `0` elsewhere.

Then the divergence vector on vertices is exactly

```tex
d=B_G c,
```

and regrouping gives the exact factorization

```tex
\textbf{D2g5. Quantitative finite-window cycle-space rigidity.}
```

```tex
s(c)=C_V B_G c.
```

Moreover:

1. `C_V` is invertible.

   Indeed, if `C_V d=0`, then the ordinary receiver

   ```tex
   R_d(z):=\sum_{i=1}^L \frac{d_i}{v_i-z}
   ```

   vanishes at the `L` distinct tail points `N+1,\dots,N+L`. After
   multiplication by `\prod_i (v_i-z)`, one gets a polynomial of degree at
   most `L-1` with `L` distinct zeros, hence zero; therefore `d=0`.

2. Writing

   ```tex
   \kappa(V,N):=\sigma_{\min}(C_V)>0,
   ```

   one has

   ```tex
   \|s(c)\|_2\ge \kappa(V,N)\,\|B_G c\|_2.
   ```

3. Let `Z_G:=\ker B_G` be the cycle space. On `Z_G^\perp`,

   ```tex
   \beta(G):=\sigma_{\min}(B_G|_{Z_G^\perp})>0,
   ```

   and therefore

   ```tex
   \|B_G c\|_2\ge \beta(G)\,\operatorname{dist}(c,Z_G).
   ```

Combining these estimates yields the finite-window rigidity inequality

```tex
\operatorname{dist}(c,\ker B_G)
\le
\frac{1}{\kappa(V,N)\beta(G)}\,\|s(c)\|_2.
```

So approximate local packets with tiny tail defect are quantitatively forced
toward the cycle space.

Two corollaries are immediate.

First, if `s(c)=0`, then

```tex
c\in \ker B_G.
```

Hence every exact finite local packet lies in the cycle space, and because
`B_G c=0` means zero divergence, the corresponding paired correction term is
actually identically zero.

Second, if `G` is a forest, then `\ker B_G=\{0\}`, so one gets the uniform
lower bound

```tex
\|s(c)\|_2\ge \kappa(V,N)\beta(G)\,\|c\|_2.
```

Thus finite forest packets are not only exact-dead (`D2g4`), but
quantitatively dead: they cannot even approximately annihilate the first `L`
tail samples unless the packet itself is small.

This sharpens the live branch point:

- if `\kappa(V,N)\beta(G)` stays bounded below on the relevant local windows,
  then `D2g1` collapses into the cycle space and there is no surviving local
  obstruction;
- if a local obstruction survives, it must do so through collapse of the
  stability constants `\kappa(V,N)\beta(G)`, which is exactly the right
  birthplace for the resonance branch `D2f3`.

There is also now a clean first split of this stability-collapse problem.

```tex
\textbf{D2g6. Bounded-window Cauchy stability split.}
```

Fix a bounded-size local window

```tex
V=\{v_1,\dots,v_L\}\subset (-\infty,B+1),
\qquad
x_m:=B+m,\ m=1,\dots,L,
```

and let `C_{V,B}` be the corresponding finite Cauchy matrix

```tex
\left(\frac{1}{v_i-x_m}\right)_{m=1,\dots,L}^{i=1,\dots,L}.
```

Assume:

1. `L` is fixed;
2. sample separation:

   ```tex
   \min_{i,m}|v_i-x_m|\ge \rho>0;
   ```

3. pairwise vertex separation:

   ```tex
   \min_{i\ne j}|v_i-v_j|\ge \delta>0;
   ```

4. coarse diameter control:

   ```tex
   \max_{i,m}|v_i-x_m|\le D.
   ```

Then `\kappa(V,B)=\sigma_{\min}(C_{V,B})` admits a positive lower bound
depending only on `(L,\rho,\delta,D)`.

Indeed, the Cauchy determinant formula gives

```tex
|\det C_{V,B}|
=
\frac{
\prod_{1\le i<j\le L}|v_j-v_i|
\prod_{1\le m<n\le L}|x_n-x_m|
}{
\prod_{i,m}|v_i-x_m|
}.
```

Since the sample grid is consecutive, the second product is a fixed positive
constant depending only on `L`; the numerator is bounded below by
`\delta^{L(L-1)/2}`; and the denominator is bounded above by `D^{L^2}`.
Hence

```tex
|\det C_{V,B}|\ge c_L\,\delta^{L(L-1)/2} D^{-L^2}
```

for some `c_L>0`.

On the other hand,

```tex
\|C_{V,B}\| \le \frac{L}{\rho}.
```

Using

```tex
\sigma_{\min}(C)\ge \frac{|\det C|}{\|C\|^{L-1}},
```

we obtain

```tex
\kappa(V,B)\ge
c'_L\,
\delta^{L(L-1)/2}
\rho^{\,L-1}
D^{-L^2}
>0.
```

Therefore, on bounded-size local windows, collapse of `\kappa(V,B)` forces at
least one geometric pathology:

- either the window approaches the tail sample grid:
  `\min_{i,m}|v_i-x_m|\to 0`;
- or two vertices of the window collide:
  `\min_{i\ne j}|v_i-v_j|\to 0`;
- or the window escapes so far that the crude diameter control `D` itself
  degenerates.

In the actual `D2` setting the first two are the meaningful cases: resonance
to the integer tail, or compressed support gaps.

So the stability-collapse branch now has a genuine internal split:

- `\beta`-collapse is the graph/combinatorial side;
- `\kappa`-collapse, at least on bounded-size windows, already forces
  resonance or geometric compression.

The graph side also admits a clean bounded-size barrier.

```tex
\textbf{D2g7. Bounded-size incidence stability.}
```

Let `G` be a finite oriented multigraph and let `r` be the number of vertices
in the union of its nontrivial connected components (equivalently: the
vertices touched by at least one edge of the packet). Then the nonzero
singular values of the incidence matrix `B_G` are the square roots of the
positive eigenvalues of the graph Laplacian `L_G=B_GB_G^*`.

Hence

```tex
\beta(G)=\sigma_{\min}(B_G|_{\ker(B_G)^\perp})
=\sqrt{\lambda_*(L_G)},
```

where `\lambda_*(L_G)` is the smallest positive Laplacian eigenvalue.

For a connected simple graph on `r` vertices, the algebraic connectivity is
minimized by the path graph, so

```tex
\lambda_*(L_G)\ge 2-2\cos(\pi/r),
```

and therefore

```tex
\beta(G)\ge 2\sin(\pi/(2r)).
```

Passing from a simple graph to a multigraph only increases the Laplacian in
the positive-semidefinite order, so the same lower bound remains valid for the
packet graphs arising here. In particular, if the local packet size is bounded
by `L`, then every local graph built on at most `L` active vertices satisfies

```tex
\beta(G)\ge 2\sin(\pi/(2L))>0.
```

This gives the next exact corollary.

```tex
\textbf{D2g8. No bounded-size stability collapse.}
```

If both:

- the packet size is bounded by a fixed `L`, and
- the geometric hypotheses of `D2g6` hold with uniform parameters,

then

```tex
\kappa(V,B)\beta(G)\ge c(L,\rho,\delta,D)>0.
```

So on bounded-size local windows there is no genuine stability collapse at
all.

Therefore any surviving local obstruction must do at least one of the
following:

1. force `\kappa`-collapse through resonance or compressed support geometry;
2. make the active local packet size tend to infinity;
3. combine both phenomena.

This is a strong narrowing of branch B: bounded-size packets are no longer a
source of mystery, and the only remaining routes are large packets or genuine
geometric degeneration, both already aligned with the `D2g3/D2f3` branch.

This can now be packaged as a clean drift-excluded dichotomy.

```tex
\textbf{D2g9. Drift-excluded bounded-size collapse dichotomy.}
```

Let `(V_n,G_n,c_n)` be a sequence of finite local packets such that:

```tex
\|c_n\|_2=1,
\qquad
\|s_n(c_n)\|_2\to 0,
```

and assume there are fixed constants `R_0>\eta_0>0` and `L\in \mathbb N` with

```tex
V_n\subset [N+1-R_0,\;N+1-\eta_0],
\qquad
\#V_n\le L
```

for all `n`.

Then exactly one of the following must happen:

1. **compressed-gap geometry**

   ```tex
   \delta(V_n):=\min_{i<j}|v_i^{(n)}-v_j^{(n)}|\longrightarrow 0;
   ```

2. **asymptotic cycle-space collapse**

   ```tex
   \operatorname{dist}(c_n,\ker B_{G_n})\longrightarrow 0.
   ```

Indeed, if `\inf_n \delta(V_n)>0`, then `D2g6` gives a uniform lower bound
for `\kappa(V_n,N)`, because the slab control yields uniform bounds on
`\eta(V_n)` and `R(V_n)`, while `\#V_n\le L` and `\inf \delta(V_n)>0` provide
the remaining determinant parameters. At the same time `D2g7/D2g8` give a
uniform lower bound for `\beta(G_n)` from `\#V_n\le L`. Hence

```tex
\kappa(V_n,N)\beta(G_n)\ge c(R_0,\eta_0,L,\inf\delta)>0,
```

and `D2g5` forces

```tex
\operatorname{dist}(c_n,\ker B_{G_n})
\le
\frac{\|s_n(c_n)\|_2}{\kappa(V_n,N)\beta(G_n)}
\longrightarrow 0.
```

So after excluding support drift, there is no third bounded-size mechanism.

This is the cleanest current form of branch B:

- if the packet size stays bounded and support gaps do not compress, then the
  packet is forced into the cycle space;
- therefore any genuinely surviving bounded-window obstruction must already
  create compressed-gap geometry;
- otherwise the only remaining possibility is growth of the active local
  packet size.

Equivalently, after excluding drift, any genuine local obstruction must flow
into one of the two sharp modes

```tex
\delta(V_n)\to 0
\qquad\text{or}\qquad
\#V_n\to\infty.
```

This is exactly the right entry point into the `D2g3/D2f3` resonance branch:
the first mode is compressed support geometry, and the second mode must be
combined with the earlier microcluster machinery.

The packet-growth branch can now be pushed into that same machinery.

```tex
\textbf{D2g10. Large-packet concentration reduction.}
```

Keep the drift-excluded setting of `D2g9`: suppose the active vertices satisfy

```tex
V_n\subset [N+1-R_0,\;N+1-\eta_0]
```

for fixed `R_0>\eta_0>0`, but now

```tex
\#V_n\to\infty.
```

Because this slab has fixed length `R_0-\eta_0`, partition it into unit
interval packets

```tex
I_{n,\ell}:=[N-\ell,\;N-\ell+1],\qquad \ell=0,1,\dots,\lceil R_0\rceil.
```

By pigeonhole, for every `n` there exists at least one unit interval with

```tex
\#(V_n\cap I_{n,\ell_n})
\ge
\frac{\#V_n}{\lceil R_0\rceil+1}.
```

On the other hand, the ambient support still lies in `Y_a`, and we already
have the inherited local counting estimate

```tex
\#(Y_a\cap [t-1,t+1])\ll_a \log(2+t).
```

So the only way that `\#V_n` can become large inside a fixed near-tail slab is
that, along a subsequence, some unit interval already carries a packet of
order comparable to the local logarithmic bound.

Equivalently:

- either `\#V_n` stays bounded after all, contradicting the packet-growth
  assumption;
- or the packet-growth branch necessarily produces a dense local unit packet of
  size `\gtrsim \log M_n` along a subsequence.

This is not yet identical to the threshold packet `\mathcal P_{M_n}(c,C)` of
`D2g2`, but it is already the correct entry point: once a whole unit packet is
forced to carry logarithmically many active vertices, the remaining work is to
refine that density from unit scale down to the threshold scale
`\asymp (\log M_n)/M_n^2`.

So the honest current conclusion is:

```tex
\text{packet growth}
\Longrightarrow
\text{dense local unit packet}
\Longrightarrow
\text{threshold microcluster or direct compressed-gap output.}
```

Either way, there is no separate large-packet mystery branch after drift is
excluded: packet growth already pushes the route toward the same compressed-gap
/ resonance geometry isolated in `D2g3/D2f3`.

This is the current strongest reduction of branch B.

In fact, the drift-excluded branch can now be compressed even further.

```tex
\textbf{D2g11. Drift-excluded local obstruction forces compressed gaps.}
```

Let `(V_n,G_n,c_n)` be normalized local packets with

```tex
\|c_n\|_2=1,
\qquad
\|s_n(c_n)\|_2\to 0,
```

and assume all active vertices remain in one fixed near-tail slab:

```tex
V_n\subset [N+1-R_0,\;N+1-\eta_0]
```

for some fixed `R_0>\eta_0>0`.

Suppose we are in the genuinely surviving branch, meaning that the packets do
not collapse asymptotically into cycle space:

```tex
\operatorname{dist}(c_n,\ker B_{G_n})\not\to 0.
```

Then necessarily

```tex
\delta(V_n):=\min_{i<j}|v_i^{(n)}-v_j^{(n)}|\longrightarrow 0.
```

Proof. If not, then after passing to a subsequence there is `\delta_0>0` with
`\delta(V_n)\ge \delta_0`. There are now two cases.

1. `\#V_n` is bounded along a further subsequence. Then `D2g9` applies and
   forces

   ```tex
   \operatorname{dist}(c_n,\ker B_{G_n})\to 0,
   ```

   contradicting the survival assumption.

2. `\#V_n\to\infty` along a subsequence. But all vertices lie in an interval of
   fixed length `R_0-\eta_0`, so the pigeonhole principle gives

   ```tex
   \delta(V_n)\le \frac{R_0-\eta_0}{\#V_n-1}\longrightarrow 0,
   ```

   again contradicting `\delta(V_n)\ge \delta_0`.

So the only possible conclusion is `\delta(V_n)\to 0`.

This is an important simplification:

- after excluding support drift, branch B no longer splits into
  “bounded-size packets” versus “large packets” as genuinely different
  survival mechanisms;
- bounded-size packets are killed by `D2g9` unless they already produce gap
  compression;
- large packets also automatically produce gap compression by elementary
  pigeonhole.

Hence the whole surviving drift-excluded branch B is now squeezed into one
geometric mode:

```tex
\text{surviving local obstruction}
\Longrightarrow
\delta(V_n)\to 0.
```

So packet growth is no longer an independent mystery branch at all; it is just
another route into compressed-gap geometry. The only real remaining task is to
upgrade this generic gap-collapse from `\delta(V_n)\to 0` to the sharper
threshold geometry already isolated in `D2g2/D2g3/D2f3`.

There is now one clean quantitative bridge in the bounded-size regime.

```tex
\textbf{D2g12. Quantitative bounded-size gap compression.}
```

Fix constants `R_0>\eta_0>0` and an integer `L\ge 2`. Let `M_n\to\infty`, and
for each `n` let `(V_n,G_n,c_n)` be a cycle-reduced local packet with

```tex
V_n\subset [M_n-R_0,\;M_n-\eta_0],
\qquad
\#V_n=L,
\qquad
c_n\in \ker(B_{G_n})^\perp,
\qquad
\|c_n\|_2=1.
```

Write

```tex
\delta_n:=\delta(V_n)=\min_{i<j}|v_i^{(n)}-v_j^{(n)}|,
```

and let `s_n(c_n)` denote the first `L` tail samples at the translated grid
`M_n+1,\dots,M_n+L`.

Then there exists a constant `A=A(L,R_0,\eta_0)>0` such that

```tex
\|s_n(c_n)\|_2 \ge A\,\delta_n^{L(L-1)/2}
\qquad \forall n.
```

Equivalently,

```tex
\delta_n
\le
A^{-2/(L(L-1))}
\,
\|s_n(c_n)\|_2^{\,2/(L(L-1))}.
```

Proof. For each `n`, `D2g5` gives

```tex
\|s_n(c_n)\|_2\ge \kappa(V_n,M_n)\beta(G_n),
```

because `c_n\in \ker(B_{G_n})^\perp` and `\|c_n\|_2=1`. Since
`V_n\subset [M_n-R_0,M_n-\eta_0]`, the translated sample block
`M_n+1,\dots,M_n+L` stays at distance at least `1+\eta_0` to the right of the
window, and the coarse diameter is bounded by `R_0+L`. Hence `D2g6` yields

```tex
\kappa(V_n,M_n)\ge a(L,R_0,\eta_0)\,\delta_n^{L(L-1)/2}
```

for some positive constant `a(L,R_0,\eta_0)`. On the graph side, `D2g7`
gives the uniform floor

```tex
\beta(G_n)\ge 2\sin\!\frac{\pi}{2L}=:b(L)>0.
```

Therefore

```tex
\|s_n(c_n)\|_2
\ge
a(L,R_0,\eta_0)b(L)\,\delta_n^{L(L-1)/2}.
```

Setting `A:=a(L,R_0,\eta_0)b(L)` proves the claim.

This immediately gives the sharp threshold corollary:

```tex
\textbf{D2g12a. Threshold-entry corollary.}
```

If along such a fixed-size subsequence one has

```tex
\|s_n(c_n)\|_2
=
o\!\left(
\left(\frac{\log M_n}{M_n^2}\right)^{L(L-1)/2}
\right),
```

then

```tex
\delta_n
=
o\!\left(\frac{\log M_n}{M_n^2}\right).
```

So any analytic defect estimate below that critical power already pushes the
packet into the sharp compressed-gap / ultra-near resonance branch
`D2g2/D2g3/D2f3`.

This is a real gain. The bounded-size branch is no longer controlled only by
qualitative collapse `\delta_n\to 0`; it now has an explicit defect-to-gap
law. So the remaining burden is cleaner:

- either extract such a defect rate from the analytic side;
- or accept that no bounded-size local packet can reach the sharp threshold
  regime without genuinely tiny sample defect.

There is now also a constructive model for the most dangerous bounded-size
survivor.

```tex
\textbf{D2g13. Hermite-type near-collision model adversary.}
```

Fix an integer `L\ge 2`, a translated tail block

```tex
x_m:=M+m,\qquad m=1,\dots,L,
```

and a center `u\le M-\eta_0` with some fixed `\eta_0>0`. Choose distinct real
shape parameters `\xi_1,\dots,\xi_L`, and for `h>0` define a near-collision
cluster

```tex
v_i(h):=u+h\xi_i,\qquad i=1,\dots,L.
```

Let

```tex
w_i:=\frac{1}{\prod_{j\ne i}(\xi_i-\xi_j)}
```

be the usual barycentric weights, and consider the ordinary local receiver

```tex
R_h(z):=\sum_{i=1}^L \frac{w_i}{v_i(h)-z}.
```

Then one has the exact identity

```tex
R_h(z)
=
-\frac{h^{L-1}}{\prod_{i=1}^L (z-v_i(h))}.
```

Proof. Set `t=(z-u)/h`. Then

```tex
\frac{1}{v_i(h)-z}
=
-\frac{1}{h}\frac{1}{t-\xi_i}.
```

So

```tex
R_h(z)
=
-\frac{1}{h}\sum_{i=1}^L \frac{w_i}{t-\xi_i}.
```

By the standard barycentric identity for the monic polynomial
`P(t)=\prod_{i=1}^L (t-\xi_i)`,

```tex
\sum_{i=1}^L \frac{w_i}{t-\xi_i}=\frac{1}{P(t)}.
```

Therefore

```tex
R_h(z)
=
-\frac{1}{h}\frac{1}{P((z-u)/h)}
=
-\frac{h^{L-1}}{\prod_{i=1}^L (z-v_i(h))}.
```

This model has the expected discrete moment cancellation. Expanding at
infinity gives

```tex
\sum_{i=1}^L w_i\xi_i^r=0\qquad (r=0,\dots,L-2),
\qquad
\sum_{i=1}^L w_i\xi_i^{L-1}=1.
```

So the cluster kills the first `L-1` moment layers and behaves like a
discrete Hermite atom of order `L-1`.

In particular, for the fixed sample block `x_m=M+m` one has

```tex
|R_h(x_m)|\asymp h^{L-1}
```

uniformly for all sufficiently small `h`, with constants depending only on
`(L,\eta_0,\xi_1,\dots,\xi_L)`. Indeed, every denominator
`|x_m-v_i(h)|=|m+(M-u)-h\xi_i|` stays between two positive constants once
`u\le M-\eta_0` and `h` is small.

This is a real conceptual gain:

- it gives an explicit “worst enemy” for local tail-sampling;
- it shows that near-collision packets can indeed manufacture very small local
  defects by cancelling the first `L-1` moment layers;
- and it suggests that the exponent in `D2g12` may not yet be sharp once
  `L\ge 3`, since the model enemy has size `h^{L-1}` while `D2g12` only forces
  a lower bound of order `h^{L(L-1)/2}`.

So the next hard question is now much cleaner:

```tex
\textbf{D2g13a. Paired realization obstruction.}
```

Can a genuine cycle-reduced paired packet in the `Y_a=\{x_\gamma,x_\gamma-1\}`
class approximate this Hermite-type near-collision extremizer without already
falling into the ultra-near resonance branch `D2f3`?

If the answer is no, then the constructive enemy is understood and excluded.
If the answer is yes, then we have identified the exact local shape that must
be analyzed from the arithmetic side.

There is also a very concrete equispaced specialization, which is useful as a
toy model and matches the finite-difference intuition exactly.

```tex
\textbf{D2g13b. Equispaced finite-difference specialization.}
```

Take

```tex
\xi_i=i-1,\qquad v_i(h)=u+(i-1)h,\qquad i=1,\dots,L,
```

and define

```tex
d_i:=(-1)^{i-1}\binom{L-1}{i-1}.
```

Then

```tex
d_i=(-1)^{L-1}(L-1)!\,w_i,
```

so the ordinary receiver

```tex
\widetilde R_h(z):=\sum_{i=1}^L \frac{d_i}{v_i(h)-z}
```

satisfies the exact closed form

```tex
\widetilde R_h(z)
=
(-1)^L (L-1)!\,
\frac{h^{L-1}}{\prod_{i=1}^L (z-v_i(h))}.
```

In particular, on every fixed translated tail block `x_m=M+m` one has

```tex
|\widetilde R_h(x_m)|\asymp h^{L-1}
```

uniformly for all sufficiently small `h`.

The moment identities become the standard finite-difference cancellations:

```tex
\sum_{i=1}^L d_i(i-1)^r=0
\qquad (r=0,\dots,L-2),
\qquad
\sum_{i=1}^L d_i(i-1)^{L-1}=(-1)^{L-1}(L-1)!.
```

So the equispaced binomial packet is the canonical toy version of the general
Hermite extremizer.

There is also a very concrete consecutive-pair realization, which is useful
because it writes the same enemy inside the finite-difference paired language
directly, without using the unit-shift copy `z\mapsto z+1`.

```tex
\textbf{D2g13c. Consecutive-pair finite-difference realization.}
```

Keep the equispaced data of `D2g13b`:

```tex
v_j:=x_0+jh,\qquad d_j:=(-1)^j\binom{L-1}{j},
\qquad j=0,\dots,L-1.
```

Define cumulative coefficients

```tex
c_j:=\sum_{i=0}^{j} d_i,\qquad j=0,\dots,L-2.
```

Then the binomial identity

```tex
\sum_{i=0}^{j}(-1)^i\binom{L-1}{i}
=
(-1)^j\binom{L-2}{j}
```

gives the closed form

```tex
c_j=(-1)^j\binom{L-2}{j}.
```

Now define the finite paired packet

```tex
K_h^{\mathrm{fd}}(z)
:=
\sum_{j=0}^{L-2}
c_j\left(\frac{1}{v_j-z}-\frac{1}{v_{j+1}-z}\right).
```

Then one has the exact telescoping regrouping

```tex
K_h^{\mathrm{fd}}(z)
=
\sum_{j=0}^{L-1}\frac{d_j}{v_j-z}
=
\widetilde R_h(z).
```

Indeed, the coefficient of `1/(v_0-z)` is `c_0=d_0`, the coefficient of
`1/(v_j-z)` for `1\le j\le L-2` is `c_j-c_{j-1}=d_j`, and the coefficient of
`1/(v_{L-1}-z)` is `-c_{L-2}=d_{L-1}` because
`\sum_{j=0}^{L-1} d_j=(1-1)^{L-1}=0`.

Combining with `D2g13b`, we therefore get the explicit finite-difference
paired formula

```tex
K_h^{\mathrm{fd}}(z)
=
(-1)^L (L-1)!\,
\frac{h^{L-1}}{\prod_{j=0}^{L-1}(z-v_j)}.
```

Equivalently, if one prefers denominators in the form `(v_j-z)`, this is

```tex
K_h^{\mathrm{fd}}(z)
=
\frac{(L-1)!h^{L-1}}{\prod_{j=0}^{L-1}(v_j-z)}.
```

Hence for every fixed right-tail block `x_m=N+m`, `m=1,\dots,M`, and every
small enough `h` with `x_0\le N+1-\eta`, one gets the two-sided estimate

```tex
(L-1)!\,A_M(x_0,N,L)\,h^{L-1}
\le
\|s^{(M)}(h)\|_2
\le
2^L (L-1)!\,A_M(x_0,N,L)\,h^{L-1},
```

where

```tex
A_M(x_0,N,L)
:=
\left(
\sum_{m=1}^{M}\frac{1}{(N+m-x_0)^{2L}}
\right)^{1/2}.
```

So this consecutive-pair packet is an exact finite paired enemy with defect
size

```tex
\|s^{(M)}(h)\|_2\asymp h^{L-1}.
```

This is a strong complement to `D2g12`: the general theorem only gives the
coarse lower bound `\|s\|\gtrsim \delta^{L(L-1)/2}`, while the explicit
finite-difference/Hermite enemy realizes the much larger scale `h^{L-1}`.
Therefore the exponent in `D2g12` is definitely nonsharp once `L\ge 3`, and
the real remaining issue is not whether small-defect packets exist in
principle, but whether genuine packets on the zeta-derived support can realize
this very rigid finite-difference/Hermite structure.

There is an even sharper point: this model enemy already lives naturally in
the paired class.

```tex
\textbf{D2g14. Paired Hermite-cluster realization.}
```

Keep the notation of `D2g13`, and define

```tex
K_h(z):=R_h(z)-R_h(z+1).
```

Then

```tex
K_h(z)
=
\sum_{i=1}^L
w_i\left(\frac{1}{v_i(h)-z}-\frac{1}{v_i(h)-1-z}\right),
```

so `K_h` is an exact paired correction term supported on the one-sided cluster
`\{v_1(h),\dots,v_L(h)\}` together with its shifted copy
`\{v_1(h)-1,\dots,v_L(h)-1\}`.

Using the closed form from `D2g13`, one gets

```tex
K_h(z)
=
-h^{L-1}
\left(
\frac{1}{\prod_{i=1}^L (z-v_i(h))}
-
\frac{1}{\prod_{i=1}^L (z+1-v_i(h))}
\right).
```

Hence on every fixed translated tail block

```tex
x_m:=M+m,\qquad m=1,\dots,L,
```

with `u\le M-\eta_0`, one has

```tex
|K_h(x_m)|\asymp h^{L-1}
```

uniformly for all sufficiently small `h`, with constants depending only on
`(L,\eta_0,\xi_1,\dots,\xi_L)`.

So the constructive enemy is not merely an ordinary clustered Cauchy sum. It
is already an exact local paired packet with the natural unit shift built in.

This is a strong clarification of branch B:

- the worst local survivor is a one-sided near-collision cluster in `X_a`,
  together with its forced shifted copy in `Y_a`;
- its coefficients are exactly the barycentric/Hermite weights;
- and its local defect is of order `h^{L-1}`.

Thus the next geometric bridge is already clean and explicit.

```tex
\textbf{D2g14a. Geometric realization forces one-sided microclusters.}
```

Suppose there exist indices

```tex
\gamma_1<\cdots<\gamma_L,
```

real numbers

```tex
\xi_1<\cdots<\xi_L,
```

a center `u`, a scale `h>0`, and an error parameter `\varepsilon\ge 0` such
that

```tex
\bigl|x_{\gamma_i}-(u+h\xi_i)\bigr|\le \varepsilon h
\qquad (i=1,\dots,L).
```

Then the one-sided support cluster

```tex
\{x_{\gamma_1},\dots,x_{\gamma_L}\}\subset X_a
```

has diameter

```tex
x_{\gamma_L}-x_{\gamma_1}
\le
h(\xi_L-\xi_1+2\varepsilon),
```

and therefore some consecutive one-sided gap satisfies

```tex
\min_{1\le i<L}(x_{\gamma_{i+1}}-x_{\gamma_i})
\le
\frac{\xi_L-\xi_1+2\varepsilon}{L-1}\,h.
```

Proof. The diameter bound is immediate from the triangle inequality:

```tex
x_{\gamma_L}-x_{\gamma_1}
\le
|x_{\gamma_L}-(u+h\xi_L)|
+
h(\xi_L-\xi_1)
+
|(u+h\xi_1)-x_{\gamma_1}|
\le
h(\xi_L-\xi_1+2\varepsilon).
```

Now sum the consecutive gaps:

```tex
\sum_{i=1}^{L-1}(x_{\gamma_{i+1}}-x_{\gamma_i})
=
x_{\gamma_L}-x_{\gamma_1}.
```

So at least one of them is bounded by the average, which yields the stated
gap estimate.

This gives the immediate threshold corollary.

```tex
\textbf{D2g14b. Approximate Hermite realization below threshold implies D2f3.}
```

If such clusters occur along a subsequence at heights `M_n` with

```tex
h_n=o\!\left(\frac{\log M_n}{M_n^2}\right),
```

then

```tex
\min_{1\le i<L}(x_{\gamma_{i+1}^{(n)}}-x_{\gamma_i^{(n)}})
=
o\!\left(\frac{\log M_n}{M_n^2}\right),
```

and in particular the route has already entered the ultra-near resonance /
compressed-gap branch `D2f3`.

So the geometric part of realizability is now settled: any approximate
realization of the paired Hermite model automatically produces the exact kind
of one-sided microcluster we were trying to force anyway.

The remaining issue is therefore narrower:

```tex
\textbf{D2g14c. Coefficient realization barrier.}
```

Can a genuine cycle-reduced paired packet on the real support
`Y_a=\{x_\gamma,x_\gamma-1\}` carry coefficients close to the barycentric
Hermite weights at some scale `h` while keeping the local tail defect as small
as the model enemy, without already forcing `h` into the threshold branch
`D2f3`?

There is one more exact simplification here.

```tex
\textbf{D2g15. The paired Hermite enemy is forest-supported.}
```

Consider the local pair-graph of `K_h`: its vertex set is

```tex
\{v_1(h)-1,\dots,v_L(h)-1,\ v_1(h),\dots,v_L(h)\},
```

and its edges are exactly the `L` disjoint unit pairs

```tex
v_i(h)-1 \longrightarrow v_i(h),
\qquad i=1,\dots,L.
```

So the graph is a matching, hence a forest. In particular:

```tex
\ker B_{G_h}=\{0\},
\qquad
\beta(G_h)=\sqrt{2}.
```

Proof. The incidence matrix is block-diagonal with `L` identical `2\times 1`
edge blocks

```tex
\begin{pmatrix}1\\ -1\end{pmatrix},
```

up to row permutation. Each block has singular value `\sqrt{2}`, so all
nonzero singular values of `B_{G_h}` equal `\sqrt{2}`. Since the graph is a
forest, there is no cycle space.

This has a very useful interpretation:

- the model enemy does **not** survive through cycle-space collapse;
- its graph-side stability is perfectly healthy;
- all of its small-defect power comes from pure Cauchy-side geometric
  degeneration, namely the one-sided near-collision cluster
  `v_i(h)=u+h\xi_i`.

So the constructive extremizer is even cleaner than it first looked:

```tex
\text{model enemy}
=
\text{forest packet}
+
\text{near-collision geometry}
+
\text{Hermite weights}.
```

There is no hidden combinatorial instability inside it.

This sharpens the realizability problem once more.

```tex
\textbf{D2g15a. No cycle escape for the model enemy.}
```

If a genuine local obstruction on `Y_a` approximates the paired Hermite model,
then its dangerous behavior cannot be blamed on cycle-space collapse or on
small `\beta(G)`. The only surviving mechanism is actual realization of the
one-sided near-collision geometry in `X_a`, which is exactly the compressed-gap
/ resonance direction already isolated in `D2f3`.

There is now also a clean coefficient-side expansion for this model.

```tex
\textbf{D2g16. Confluent moment expansion for near-collision clusters.}
```

Keep the one-sided cluster

```tex
v_i(h)=u+h\xi_i,\qquad i=1,\dots,L,
```

with distinct real `\xi_i`, and define for a coefficient vector
`c=(c_1,\dots,c_L)\in\mathbb C^L`

```tex
S_h(c)_m:=\sum_{i=1}^L \frac{c_i}{v_i(h)-x_m},
\qquad
x_m:=M+m,\quad m=1,\dots,L,
```

where `u\le M-\eta_0` and `h` is sufficiently small.

For each `r\ge 0`, define the discrete moments

```tex
\mu_r(c):=\sum_{i=1}^L c_i\xi_i^r.
```

Then for every fixed `m=1,\dots,L` one has the absolutely convergent expansion

```tex
S_h(c)_m
=
-\sum_{r\ge 0}
\frac{h^r\,\mu_r(c)}{(x_m-u)^{r+1}}.
```

Proof. Since `x_m-u\ge \eta_0+m\ge 1+\eta_0`, we have `|h\xi_i|<x_m-u` for all
small `h`, so

```tex
\frac{1}{u+h\xi_i-x_m}
=
-\frac{1}{x_m-u}
\frac{1}{1-\frac{h\xi_i}{x_m-u}}
=
-\sum_{r\ge 0}\frac{h^r\xi_i^r}{(x_m-u)^{r+1}}.
```

Summing over `i` gives the formula.

This has an immediate order-of-vanishing consequence.

```tex
\textbf{D2g16a. First surviving moment controls the defect order.}
```

Let `s(c)` be the smallest index with `\mu_s(c)\neq 0`. Then

```tex
\|S_h(c)\|_2 \asymp h^{s(c)}
```

as `h\to 0`, with constants depending on `(L,\eta_0,\xi_1,\dots,\xi_L,c)`.

Indeed, the expansion above gives

```tex
S_h(c)_m
=
-h^{s(c)}\frac{\mu_{s(c)}(c)}{(x_m-u)^{s(c)+1}}
+
O(h^{s(c)+1}),
```

uniformly in `m=1,\dots,L`, and the leading vector

```tex
\left((x_m-u)^{-s(c)-1}\right)_{m=1}^L
```

is nonzero.

Now the distinctness of the `\xi_i` implies a rigidity statement.

```tex
\textbf{D2g16b. Hermite weights are the unique maximal-cancellation direction.}
```

The linear map

```tex
T(c):=(\mu_0(c),\dots,\mu_{L-2}(c))
```

has one-dimensional kernel, and that kernel is exactly the barycentric line
`\mathbb C w`, where

```tex
w_i=\frac{1}{\prod_{j\ne i}(\xi_i-\xi_j)}.
```

Equivalently:

- `c` kills the first `L-1` moment layers iff `c\in \mathbb C w`;
- for such `c`, the defect order is exactly `h^{L-1}`;
- and no nonzero coefficient direction can do better.

Proof. The matrix of `T` is the `(L-1)\times L` Vandermonde block

```tex
(\xi_i^r)_{r=0,\dots,L-2}^{i=1,\dots,L},
```

which has rank `L-1` because the `\xi_i` are distinct. So `\ker T` is
one-dimensional. The barycentric weights `w` lie in the kernel by the standard
partial-fraction identity used in `D2g13`, hence span it.

This immediately yields the coefficient-side barrier we wanted.

```tex
\textbf{D2g16c. Coefficient rigidity toward Hermite weights.}
```

Fix `\varepsilon>0`. Then there exist constants `c_\varepsilon>0` and
`h_\varepsilon>0` such that for every unit vector `c\in\mathbb C^L` with

```tex
\operatorname{dist}(c,\mathbb C w)\ge \varepsilon
```

one has

```tex
\|S_h(c)\|_2\ge c_\varepsilon h^{L-2}
\qquad (0<h<h_\varepsilon).
```

Proof. On the compact set

```tex
\{c\in\mathbb C^L:\ \|c\|_2=1,\ \operatorname{dist}(c,\mathbb C w)\ge\varepsilon\},
```

suppose the claim fails. Then there exist `h_n\to 0` and unit vectors `c_n`
with `\operatorname{dist}(c_n,\mathbb C w)\ge\varepsilon` such that

```tex
\|S_{h_n}(c_n)\|_2=o(h_n^{L-2}).
```

After passing to a subsequence, `c_n\to c_\infty` with
`\|c_\infty\|_2=1` and `\operatorname{dist}(c_\infty,\mathbb C w)\ge\varepsilon`.
Now use the truncated expansion

```tex
S_h(c)_m
=
-\sum_{r=0}^{L-2}\frac{h^r\mu_r(c)}{(x_m-u)^{r+1}}
+
O(h^{L-1}).
```

Dividing by `h_n^{L-2}`, we obtain

```tex
h_n^{-(L-2)}S_{h_n}(c_n)_m
=
-\sum_{r=0}^{L-2}
h_n^{r-(L-2)}
\frac{\mu_r(c_n)}{(x_m-u)^{r+1}}
+
O(h_n).
```

Since the left side tends to `0`, the coefficients of every negative power of
`h_n` must vanish asymptotically. Therefore

```tex
\mu_r(c_n)=O(h_n^{L-2-r})\longrightarrow 0
\qquad (r=0,\dots,L-2).
```

Passing to the limit gives

```tex
\mu_r(c_\infty)=0
\qquad (r=0,\dots,L-2),
```

so `c_\infty\in \ker T=\mathbb C w`, contradicting
`\operatorname{dist}(c_\infty,\mathbb C w)\ge\varepsilon`.

Hence the stated lower bound must hold.

Finally, this transfers back to the paired model. For

```tex
K_h(c;z):=\sum_{i=1}^L c_i\left(\frac{1}{v_i(h)-z}-\frac{1}{v_i(h)-1-z}\right),
```

the same coefficient line `\mathbb C w` is the unique direction that can
produce the model defect order `h^{L-1}` on a fixed tail block. Any unit
coefficient vector separated from `\mathbb C w` gives at best order
`h^{L-2}`.

This can be made quantitative directly in the paired sampling language.

```tex
\textbf{D2g16f. Quantitative paired capture toward the Hermite line.}
```

Fix `R_0>\eta_0>0` and distinct real `\xi_1,\dots,\xi_L`. Let

```tex
v_i(h)=u+h\xi_i,\qquad i=1,\dots,L,
```

with

```tex
M-R_0\le u\le M-\eta_0,
\qquad
0<h<h_0(L,\eta_0,\xi),
```

and define the paired local receiver

```tex
K_h(c;z):=\sum_{i=1}^L c_i\left(\frac{1}{v_i(h)-z}-\frac{1}{v_i(h)-1-z}\right).
```

Sample it on the fixed right-tail block

```tex
x_m:=M+m,\qquad m=1,\dots,L,
```

and set

```tex
P_h(c):=\bigl(K_h(c;x_1),\dots,K_h(c;x_L)\bigr)\in\mathbb C^L.
```

Then there exist constants

```tex
\beta_0=\beta_0(\xi_1,\dots,\xi_L)>0,
\qquad
\gamma_0=\gamma_0(L,\eta_0,R_0,\xi_1,\dots,\xi_L)>0,
\qquad
C_0=C_0(L,\eta_0,R_0,\xi_1,\dots,\xi_L)>0
```

such that for every coefficient vector `c\in\mathbb C^L` and every sufficiently
small `h`,

```tex
\operatorname{dist}(c,\mathbb C w)
\le
C_0\left(
h + h^{-(L-2)}\|P_h(c)\|_2
\right).
```

In particular, if `\|c\|_2=1` and the paired local defect satisfies

```tex
\|P_h(c)\|_2\le C\,h^{L-1},
```

then

```tex
\operatorname{dist}(c,\mathbb C w)\le C'(L,\eta_0,R_0,\xi,C)\,h.
```

Proof. Write the one-sided sample block as in `D2g16`:

```tex
S_h(c)_m:=\sum_{i=1}^L \frac{c_i}{v_i(h)-x_m},
\qquad
x_m=M+m.
```

Then

```tex
K_h(c;x_m)=S_h(c)_m-S_h(c)_{m+1},
```

so by the confluent expansion from `D2g16`,

```tex
P_h(c)_m
=
-\sum_{r\ge 0} h^r\mu_r(c)
\left(
\frac{1}{(x_m-u)^{r+1}}
-
\frac{1}{(x_{m+1}-u)^{r+1}}
\right).
```

Define the paired moment matrix `B(u,M)\in M_{L\times (L-1)}(\mathbb C)` by

```tex
B(u,M)_{m,r}
:=
-\left(
\frac{1}{(x_m-u)^{r+1}}
-
\frac{1}{(x_{m+1}-u)^{r+1}}
\right),
\qquad
m=1,\dots,L,\ r=0,\dots,L-2.
```

Let `T(c)=(\mu_0(c),\dots,\mu_{L-2}(c))` and
`D_h=\operatorname{diag}(1,h,\dots,h^{L-2})`. Then

```tex
P_h(c)=B(u,M)D_hT(c)+\mathcal R_h(c),
```

where the remainder satisfies

```tex
\|\mathcal R_h(c)\|_2\le C_1 h^{L-1}\|c\|_2
```

for all sufficiently small `h`, with `C_1=C_1(L,\eta_0,R_0,\xi)`.

Now we need two uniform rank facts.

First, the moment map `T` has kernel exactly `\mathbb C w` by `D2g16b`, so on
the orthogonal complement of `\mathbb C w` there is a positive smallest
singular value `\beta_0>0`:

```tex
\|T(c)\|_2\ge \beta_0\,\operatorname{dist}(c,\mathbb C w).
```

Second, `B(u,M)` has full column rank for every admissible `(u,M)`.
Indeed, if `B(u,M)a=0`, then the rational function

```tex
F_a(t):=\sum_{r=0}^{L-2} a_r t^{-(r+1)}
```

takes the same value at the `L+1` distinct points
`t_m:=x_m-u=M+m-u`, `m=1,\dots,L+1`.
Hence the polynomial

```tex
Q_a(t):=\sum_{r=0}^{L-2} a_r t^{L-2-r}-C\,t^{L-1}
```

has at least `L+1` roots, where `C=F_a(t_1)`. Since `\deg Q_a\le L-1`, we get
`Q_a\equiv 0`, so `C=0` and all `a_r=0`. Therefore `B(u,M)` has rank `L-1`.

Because the admissible slab

```tex
\{u:\ M-R_0\le u\le M-\eta_0\}
```

is compact after shifting by `M`, the smallest singular value of `B(u,M)` is
uniformly bounded below:

```tex
\sigma_{\min}(B(u,M))\ge \gamma_0>0.
```

Hence

```tex
\|P_h(c)\|_2
\ge
\gamma_0 \|D_hT(c)\|_2 - C_1 h^{L-1}\|c\|_2
\ge
\gamma_0 h^{L-2}\|T(c)\|_2 - C_1 h^{L-1}\|c\|_2.
```

Using the bound on `T(c)` gives

```tex
\gamma_0\beta_0\,h^{L-2}\operatorname{dist}(c,\mathbb C w)
\le
\|P_h(c)\|_2 + C_1 h^{L-1}\|c\|_2.
```

For unit `c` this rearranges to

```tex
\operatorname{dist}(c,\mathbb C w)
\le
\frac{1}{\gamma_0\beta_0}
\left(
h^{-(L-2)}\|P_h(c)\|_2 + C_1 h
\right),
```

which is the stated estimate.

So the coefficient barrier is now fully quantitative in the paired model:
once a genuine packet realizes a near-collision support geometry, the only way
to keep the paired local defect at the Hermite scale `h^{L-1}` is to force its
coefficients into an `O(h)`-tube around the single barycentric/Hermite line.

The next step is to remove the last artificial freeze: in `D2g16f` the
normalized shape `(\xi_1,\dots,\xi_L)` is fixed in advance, while genuine
packets on `X_a` carry whatever normalized profile the actual support gives.

```tex
\textbf{D2g17. Uniform genuine-microcluster capture.}
```

Fix `L\ge 2` and `0<\rho<1/(L-1)`. Define the compact normalized shape class

```tex
\mathcal K_{L,\rho}
:=
\left\{
(\xi_1,\dots,\xi_L)\in\mathbb R^L:
0=\xi_1<\xi_2<\cdots<\xi_L=1,\
\xi_{i+1}-\xi_i\ge \rho
\right\}.
```

For each `\xi\in\mathcal K_{L,\rho}`, let `w(\xi)` be the associated
barycentric/Hermite vector.

Then there exist constants

```tex
C_{L,\rho,\eta_0,R_0}>0,\qquad
h_{L,\rho,\eta_0,R_0}>0
```

such that the following holds.

Take any genuine one-sided cluster

```tex
y_1<\cdots<y_L\subset X_a
```

with diameter

```tex
h:=y_L-y_1,
```

base point `u:=y_1`, normalized profile

```tex
\xi_i:=\frac{y_i-u}{h}\in\mathcal K_{L,\rho},
```

and drift control

```tex
M-R_0\le u\le M-\eta_0,
\qquad
0<h<h_{L,\rho,\eta_0,R_0}.
```

For any coefficient vector `c\in\mathbb C^L`, define the genuine paired packet

```tex
K_y(c;z):=\sum_{i=1}^L c_i\left(\frac{1}{y_i-z}-\frac{1}{y_i-1-z}\right),
```

and the local defect on the right-tail block

```tex
P_y(c):=\bigl(K_y(c;M+1),\dots,K_y(c;M+L)\bigr).
```

Then

```tex
\operatorname{dist}(c,\mathbb C w(\xi))
\le
C_{L,\rho,\eta_0,R_0}
\left(
h+h^{-(L-2)}\|P_y(c)\|_2
\right).
```

In particular, if `\|c\|_2=1` and

```tex
\|P_y(c)\|_2\le C h^{L-1},
```

then

```tex
\operatorname{dist}(c,\mathbb C w(\xi))
\le
C'_{L,\rho,\eta_0,R_0,C}\,h.
```

Proof. Write the exact geometry of the genuine cluster in normalized form:

```tex
y_i=u+h\xi_i.
```

Then the packet is literally of the form covered by `D2g16f`, with normalized
shape `\xi`. So it remains only to check that the constants in `D2g16f` can be
chosen uniformly over all `\xi\in\mathcal K_{L,\rho}`.

This is immediate from compactness:

- the barycentric vector `w(\xi)` depends continuously on `\xi`;
- the smallest positive singular value `\beta_0(\xi)` of the moment map on
  `(\mathbb C w(\xi))^\perp` depends continuously on `\xi`;
- the smallest singular value `\gamma_0(\xi)` of the paired moment matrix
  depends continuously on `\xi`;
- the remainder constant in the convergent expansion depends continuously on
  `\xi`.

All these quantities stay positive on `\mathcal K_{L,\rho}`, so their
minima/maxima are uniform. This yields the stated constants.

Therefore the exact-model coefficient capture already transfers to every
genuine one-sided cluster whose normalized shape avoids relative-gap collapse.

This gives the clean branch split we wanted.

```tex
\textbf{D2g17a. Genuine packet dichotomy: compressed subgap or Hermite capture.}
```

Fix `L\ge 2`, `0<\rho<1/(L-1)`, and a drift-excluded slab. Let

```tex
y_1<\cdots<y_L\subset X_a,
\qquad
h:=y_L-y_1,
```

and let `c` be a unit coefficient vector for the corresponding genuine paired
packet. Assume

```tex
\|P_y(c)\|_2\le C h^{L-1}.
```

Then exactly one of the following holds:

1. **compressed subgap:** there exists `i<L` such that

   ```tex
   y_{i+1}-y_i<\rho h;
   ```

2. **Hermite capture:** the normalized profile belongs to
   `\mathcal K_{L,\rho}` and

   ```tex
   \operatorname{dist}(c,\mathbb C w(\xi))
   \le
   C'_{L,\rho,\eta_0,R_0,C}\,h.
   ```

So the model-to-reality bridge is now explicit:

- either the genuine packet already contains a smaller compressed subgap and
  moves deeper into the resonance branch;
- or its coefficients are quantitatively forced into the Hermite line of its
  own exact local geometry.

This already has a concrete residue-level fingerprint.

```tex
\textbf{D2g18. Hermite-capture fingerprint on genuine residues.}
```

Fix `L\ge 2` and `0<\rho<1/(L-1)`. For every
`\xi\in\mathcal K_{L,\rho}`, let

```tex
\widehat w(\xi):=\frac{w(\xi)}{\|w(\xi)\|_2}.
```

Because `\xi_1<\cdots<\xi_L` are real and distinct, each coordinate of
`\widehat w(\xi)` is real and has alternating sign:

```tex
\operatorname{sgn}\widehat w_i(\xi)=(-1)^{L-i}.
```

Moreover, by compactness of `\mathcal K_{L,\rho}` there exist constants

```tex
0<m_{L,\rho}\le M_{L,\rho}<\infty
```

such that for every `\xi\in\mathcal K_{L,\rho}` and every `i=1,\dots,L`,

```tex
m_{L,\rho}\le |\widehat w_i(\xi)|\le M_{L,\rho}.
```

Now let `c\in\mathbb C^L` be a unit vector satisfying

```tex
\operatorname{dist}(c,\mathbb C w(\xi))\le \varepsilon<m_{L,\rho}/2.
```

Then there exists a unimodular phase `\omega\in\mathbb C`, `|\omega|=1`, such
that

```tex
\|c-\omega\widehat w(\xi)\|_2\le \varepsilon,
```

hence for each coordinate

```tex
\frac{m_{L,\rho}}{2}\le |c_i|\le M_{L,\rho}+\varepsilon
```

and

```tex
\Re\!\left((-1)^{L-i}\overline{\omega}\,c_i\right)\ge \frac{m_{L,\rho}}{2}.
```

So after one global phase rotation, every genuinely captured packet has:

1. strict alternating phase/sign pattern across the cluster;
2. all coefficients bounded away from `0`;
3. all coefficients of comparable size.

Combining this with `D2g17a`, we obtain the exact local residue fingerprint:

```tex
\textbf{D2g18a. Genuine local obstruction fingerprint.}
```

Fix `L`, `\rho`, and a drift-excluded slab. If a genuine paired packet on
`Y_a=\{x_\gamma,x_\gamma-1\}` has Hermite-scale defect

```tex
\|P_y(c)\|_2\le C h^{L-1},
```

then either:

1. some relative subgap is already compressed (`y_{i+1}-y_i<\rho h`), or
2. after a single global phase rotation, the local coefficient block is
   alternating and uniformly nondegenerate:

   ```tex
   \Re\!\left((-1)^{L-i}\overline{\omega}\,c_i\right)\ge c_{L,\rho}>0,
   \qquad
   |c_i|\asymp_{L,\rho} 1.
   ```

This is not yet the final contradiction, but it removes the last vague
residue-level freedom. A genuine dangerous packet can no longer have arbitrary
local coefficient texture: once it avoids immediate compressed-subgap collapse,
its residues must locally look like a phase-rotated finite-difference block.

This local fingerprint can be upgraded from signs/magnitudes to adjacent
ratios.

```tex
\textbf{D2g18b. Hermite capture forces adjacent negative ratio geometry.}
```

Fix `L\ge 2` and `0<\rho<1/(L-1)`. For
`\xi\in\mathcal K_{L,\rho}`, the normalized Hermite vector
`\widehat w(\xi)` from `D2g18` has real alternating coordinates satisfying

```tex
m_{L,\rho}\le |\widehat w_i(\xi)|\le M_{L,\rho}.
```

Therefore for every `i=1,\dots,L-1`,

```tex
-A_{L,\rho}\le \frac{\widehat w_{i+1}(\xi)}{\widehat w_i(\xi)}
\le -a_{L,\rho}<0,
```

where one may take

```tex
a_{L,\rho}:=\frac{m_{L,\rho}}{M_{L,\rho}},
\qquad
A_{L,\rho}:=\frac{M_{L,\rho}}{m_{L,\rho}}.
```

Now let `q\in\mathbb C^L` satisfy

```tex
\|q\|_2=1,
\qquad
\operatorname{dist}(q,\mathbb C\widehat w(\xi))\le \varepsilon.
```

Then there exist constants

```tex
\varepsilon_0=\varepsilon_0(L,\rho)>0,
\qquad
C_*=C_*(L,\rho)>0
```

such that for every `0<\varepsilon\le \varepsilon_0` and every
`i=1,\dots,L-1`,

```tex
\left|
\frac{q_{i+1}}{q_i}
-
\frac{\widehat w_{i+1}(\xi)}{\widehat w_i(\xi)}
\right|
\le
C_*\varepsilon.
```

In particular,

```tex
\frac{q_{i+1}}{q_i}
```

lies in the `C_*\varepsilon`-neighborhood of the negative real segment

```tex
[-A_{L,\rho},-a_{L,\rho}].
```

Proof. Choose `\lambda\in\mathbb C` with

```tex
q=\lambda \widehat w(\xi)+e,
\qquad
\|e\|_2\le \varepsilon.
```

Since `\|q\|_2=1` and `\|\widehat w(\xi)\|_2=1`, one has

```tex
1\le |\lambda|+\varepsilon,
```

so for `\varepsilon\le 1/2`,

```tex
|\lambda|\ge 1/2.
```

Also `|e_i|\le \varepsilon` for every `i`. Therefore

```tex
|q_i|
\ge
|\lambda|\,|\widehat w_i(\xi)|-|e_i|
\ge
\frac12 m_{L,\rho}-\varepsilon.
```

If

```tex
\varepsilon_0\le \frac14 m_{L,\rho},
```

then for `\varepsilon\le \varepsilon_0`,

```tex
|q_i|\ge \frac14 m_{L,\rho}>0,
```

so all adjacent ratios are well defined. Now

```tex
\frac{q_{i+1}}{q_i}
-
\frac{\widehat w_{i+1}}{\widehat w_i}
=
\frac{(\lambda \widehat w_{i+1}+e_{i+1})\widehat w_i
-\widehat w_{i+1}(\lambda \widehat w_i+e_i)}
{\widehat w_i q_i}
=
\frac{\widehat w_i e_{i+1}-\widehat w_{i+1}e_i}
{\widehat w_i q_i}.
```

Hence

```tex
\left|
\frac{q_{i+1}}{q_i}
-
\frac{\widehat w_{i+1}}{\widehat w_i}
\right|
\le
\frac{
|\widehat w_i||e_{i+1}|+|\widehat w_{i+1}||e_i|
}{
|\widehat w_i|\,|q_i|
}
\le
\frac{2M_{L,\rho}\varepsilon}{
m_{L,\rho}\cdot (\frac14 m_{L,\rho})
}
=
\frac{8M_{L,\rho}}{m_{L,\rho}^2}\,\varepsilon.
```

So one may take

```tex
C_*:=\frac{8M_{L,\rho}}{m_{L,\rho}^2}.
```

This proves the ratio estimate.

Therefore Hermite capture does not merely force alternating signs after one
global phase; it forces every adjacent residue ratio to be almost a negative
real number of controlled size.

There is now a decisive amplitude check against the actual residue decay.

```tex
\textbf{D2g19. Hermite-captured packets are amplitude-harmless.}
```

Keep the setting of `D2g17a` and `D2g18a`, and assume we are looking at a
genuine local packet extracted from the actual paired correction term

```tex
\sum_\gamma \frac{q_\gamma}{(x_\gamma-z)(x_\gamma-1-z)},
\qquad
q_\gamma=e(x_\gamma-1).
```

For a local cluster

```tex
y_1<\cdots<y_L\subset X_a,
\qquad
h:=y_L-y_1,
```

write the local coefficient block as

```tex
q^{\mathrm{loc}}=(q_1,\dots,q_L)\in\mathbb C^L,
```

and assume `\|q^{\mathrm{loc}}\|_2\neq 0`. Normalize it by

```tex
c:=\frac{q^{\mathrm{loc}}}{\|q^{\mathrm{loc}}\|_2}.
```

Suppose we are in the Hermite-capture branch of `D2g17a`, so that

```tex
\operatorname{dist}(c,\mathbb C w(\xi))\le C_0 h.
```

Then there is a constant

```tex
C_{L,\rho,\eta_0,R_0}>0
```

such that the normalized local paired defect already satisfies

```tex
\|P_y(c)\|_2\le C_{L,\rho,\eta_0,R_0}\,h^{L-1}.
```

Proof. Choose `\omega` so that
`\|c-\omega\widehat w(\xi)\|_2\ll h`, and write

```tex
c=\omega\widehat w(\xi)+r,
\qquad
\|r\|_2\ll h.
```

For the Hermite vector itself,

```tex
\|P_y(\omega\widehat w(\xi))\|_2\asymp h^{L-1}
```

by the exact model formula from `D2g13/D2g14`.

For the remainder, use the paired expansion from `D2g16f`:
the moment map `T` is bounded, the paired moment matrix is bounded on the
drift-excluded slab, and the diagonal factor contributes at worst `h^{L-2}`.
Hence

```tex
\|P_y(r)\|_2\ll h^{L-2}\|r\|_2 + h^{L-1}\|r\|_2\ll h^{L-1}.
```

So

```tex
\|P_y(c)\|_2\le \|P_y(\omega\widehat w(\xi))\|_2+\|P_y(r)\|_2
\ll h^{L-1}.
```

Now reinstate the actual amplitude. Since `q_i=e(x_{\gamma_i}-1)` and the
actual paired residues satisfy

```tex
|q_i|\ll_a y_i^{-3}\asymp_a M^{-3}
```

on a drift-excluded near-tail slab, we have

```tex
\|q^{\mathrm{loc}}\|_2\ll_{a,L} M^{-3}.
```

Therefore the actual local packet contribution obeys

```tex
\|P_y(q^{\mathrm{loc}})\|_2
=
\|q^{\mathrm{loc}}\|_2\,\|P_y(c)\|_2
\ll_{a,L,\rho,\eta_0,R_0}
M^{-3}h^{L-1}.
```

If the slab is fixed, then `h\ll 1`, hence

```tex
M\,\|P_y(q^{\mathrm{loc}})\|_2\ll M^{-2}\to 0.
```

So a Hermite-captured genuine packet is automatically `o(M^{-1})` after the
same scaling used in `D2g1`.

This yields the key corollary.

```tex
\textbf{D2g19a. Hermite capture cannot support D2g1 failure.}
```

In the bounded-size drift-excluded regime, any genuine local packet lying in
the Hermite-capture branch of `D2g17a` is too small, after reinstating the true
residue amplitudes `q_\gamma=O(M^{-3})`, to obstruct the desired
`o(M^{-1})` bound for the paired correction term.

Therefore every genuine local obstruction to `D2g1` must already lie in the
other branch of `D2g17a`, namely:

```tex
\exists\, i<L:\quad y_{i+1}-y_i<\rho h.
```

In words: once the coefficient branch is normalized correctly, Hermite capture
is harmless. The only surviving local mechanism is immediate compressed-subgap
collapse, i.e. direct entry into the resonance/compressed-gap branch.

There is also a clean counting-scale closure of the bounded-size regime.

```tex
\textbf{D2g20. Bounded-size local obstruction already forces D2f3.}
```

Fix `L_0\ge 1`. Let

```tex
\Gamma_M^{\mathrm{loc}}
\subset \Gamma
```

be a genuine local packet at height `M`, extracted from the actual paired
correction term

```tex
\sum_\gamma \frac{q_\gamma}{(x_\gamma-z)(x_\gamma-1-z)},
\qquad
|q_\gamma|\ll_a x_\gamma^{-3},
```

and assume:

1. the packet is bounded-size:

   ```tex
   \#\Gamma_M^{\mathrm{loc}}\le L_0;
   ```

2. it lives in a drift-excluded near-tail slab, so every participating
   support point satisfies `x_\gamma\asymp M`.

If along some subsequence the packet contribution is not `o(M^{-1})`, i.e.

```tex
M\left|
\sum_{\gamma\in\Gamma_M^{\mathrm{loc}}}
\frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)}
\right|
\not\to 0,
```

then after passing to a further subsequence there must exist
`\gamma(M)\in\Gamma_M^{\mathrm{loc}}` such that

```tex
\min\{|x_{\gamma(M)}-M|,\ |x_{\gamma(M)}-(M+1)|\}
=
o\!\left(\frac{\log M}{M^2}\right).
```

So every genuine bounded-size local obstruction is already inside the
ultra-near resonance branch `D2f3`.

Proof. Argue by contrapositive. Assume the packet does \emph{not} enter
`D2f3`. Then, after passing to a subsequence, there exists `c_0>0` such that
for every `\gamma\in\Gamma_M^{\mathrm{loc}}`,

```tex
\min\{|x_\gamma-M|,\ |x_\gamma-(M+1)|\}
\ge
c_0\frac{\log M}{M^2}.
```

For large `M`, this lower bound is `<1/2`, hence the other factor among
`|x_\gamma-M|` and `|x_\gamma-(M+1)|` is at least `1/2`. Therefore

```tex
\left|
\frac{1}{(x_\gamma-M)(x_\gamma-1-M)}
\right|
\ll_{c_0}
\frac{M^2}{\log M}.
```

Since also `|q_\gamma|\ll_a M^{-3}`, each single packet term satisfies

```tex
M\left|
\frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)}
\right|
\ll_{a,c_0}
\frac{1}{\log M}.
```

Summing over at most `L_0` indices gives

```tex
M\left|
\sum_{\gamma\in\Gamma_M^{\mathrm{loc}}}
\frac{q_\gamma}{(x_\gamma-M)(x_\gamma-1-M)}
\right|
\ll_{a,c_0,L_0}
\frac{1}{\log M}
\to 0,
```

contrary to the assumed non-negligible packet. Hence the contrapositive is
proved.

This closes the entire bounded-size branch:

- `D2g19a` kills the Hermite-capture coefficient mechanism;
- `D2g20` kills every `O(1)`-packet that stays at or above the threshold
  scale;
- therefore any remaining genuine local obstruction must be both
  non-Hermite and noncompact in packet size, or else already lie in `D2f3`.

Equivalently:

```tex
\textbf{D2g20a. Outside D2f3, surviving local packets must grow.}
```

If along a subsequence the local paired correction contribution is not
`o(M^{-1})` and the route stays outside `D2f3`, then for every fixed `L_0`
one has

```tex
\#\Gamma_M^{\mathrm{loc}}>L_0
```

for all sufficiently large `M` on that subsequence. In other words,

```tex
\#\Gamma_M^{\mathrm{loc}}\longrightarrow\infty.
```

So after `D2g19/D2g20`, the only live direct obstruction is a genuinely
noncompact large-packet mechanism.

This combines immediately with the earlier threshold packet reduction
`D2g2/D2g3`.

```tex
\textbf{D2g21. The only surviving direct obstruction is a logarithmic threshold microcluster.}
```

Suppose along some subsequence the paired correction term is not `o(M^{-1})`
and the route stays outside `D2f3`. Then:

1. by `D2g19a`, the obstruction cannot come from the bounded-size
   Hermite-capture branch;
2. by `D2g20a`, any surviving local packet must be noncompact, i.e.
   `\#\Gamma_M^{\mathrm{loc}}\to\infty`;
3. by `D2g2`, the threshold packet must satisfy

   ```tex
   \#\mathcal P_M(c,C)\gtrsim \log M
   ```

   for some fixed `0<c<C<\infty`;
4. by `D2g3`, one of the one-sided packets
   `\mathcal P_M^{(+)}(c,C)` or `\mathcal P_M^{(-)}(c,C)` contains
   `\gtrsim \log M` points inside an interval of length
   `\asymp (\log M)/M^2`, and therefore there are infinitely many
   consecutive one-sided gaps satisfying

   ```tex
   x_{\gamma+1}-x_\gamma \ll \frac{1}{M^2}.
   ```

So the direct branch is now completely compressed to one explicit live enemy:

```tex
\text{a noncompact logarithmic threshold microcluster, hence an }O(M^{-2})
\text{ one-sided gap branch.}
```

In particular, there is no longer any separate bounded-size local mechanism
left to analyze.

This can now be stated as a single arithmetic dichotomy.

```tex
\textbf{D2g22. Final arithmetic reduction of the direct branch.}
```

Any genuine infinite-support counterexample to the direct tail-zero receiver
problem forces at least one of the following two arithmetic scenarios along an
infinite subsequence:

1. **ultra-near integer resonance**

   ```tex
   \operatorname{dist}(x_\gamma,\mathbb Z)
   =
   o\!\left(\frac{\log x_\gamma}{x_\gamma^2}\right);
   ```

2. **microscopic one-sided zero gaps**

   ```tex
   x_{\gamma+1}-x_\gamma\ll \frac{1}{x_\gamma^2}.
   ```

Since `x_\gamma=(a/\pi)\gamma`, the second alternative is equivalent to

```tex
\gamma_{n+1}-\gamma_n\ll_a \frac{1}{\gamma_n^2}.
```

Proof. If the route enters `D2f3`, we are in the first case by definition.
If not, then `D2g21` applies and forces the second case.

So the direct route is no longer blocked by a vague analytic residue cloud.
It is blocked only by an explicit arithmetic geometry of the zeta zero set:
either ultra-near resonance to the integer lattice after scaling, or
infinitely many microscopic consecutive gaps on the critical line.

This yields the cleanest current closure criterion for the direct branch.

```tex
\textbf{D2g23. Conditional closure of the direct route.}
```

Assume one can rule out both of the following arithmetic scenarios:

1. there is no infinite subsequence of ordinates with

   ```tex
   \operatorname{dist}(x_\gamma,\mathbb Z)
   =
   o\!\left(\frac{\log x_\gamma}{x_\gamma^2}\right);
   ```

2. there is no infinite subsequence of consecutive critical-line gaps with

   ```tex
   \gamma_{n+1}-\gamma_n\ll \frac{1}{\gamma_n^2}.
   ```

Then there is no genuine infinite-support counterexample to the direct
tail-zero receiver problem.

Proof. By `D2g22`, any genuine infinite-support counterexample forces at least
one of these two scenarios. So if both are excluded, the counterexample
cannot exist.

This is not yet a full proof of `PO2`, because the two arithmetic exclusions
are themselves still open on the active route. But it is a real endpoint
reduction: the direct analytic residue problem has now been completely pushed
into two explicit arithmetic geometry statements about the zeta zero set.

The faster remaining half of this endpoint reduction is the integer-resonance
side, and it too can be rewritten in a sharper arithmetic form.

```tex
\textbf{D2g24. Integer resonance is a super-accurate near-progression branch.}
```

Assume there exists an infinite subsequence of scaled ordinates with

```tex
\operatorname{dist}(x_\gamma,\mathbb Z)
=
o\!\left(\frac{\log x_\gamma}{x_\gamma^2}\right).
```

Then there exist distinct integers `m_\nu\to\infty` and critical ordinates
`\gamma_\nu` such that

```tex
x_{\gamma_\nu}=m_\nu+\varepsilon_\nu,
\qquad
\varepsilon_\nu=o\!\left(\frac{\log m_\nu}{m_\nu^2}\right),
```

equivalently

```tex
\gamma_\nu
=
\frac{\pi}{a}m_\nu
+ 
o\!\left(\frac{\log m_\nu}{m_\nu^2}\right).
```

So the integer-resonance branch is not just “many scaled ordinates happen to
be close to integers”. It is an infinite near-arithmetic progression of
critical-line zeros with super-microscopic perturbation around the lattice

```tex
\frac{\pi}{a}\mathbb Z.
```

Proof. For each resonant `x_\gamma`, choose a nearest integer `m(x_\gamma)`.
Because the error is `o(1)`, it is eventually `<1/2`, so `m(x_\gamma)` is
uniquely defined. Since `x_\gamma\to\infty`, these integers tend to infinity,
and by passing to a subsequence we may assume them strictly increasing.
Writing

```tex
x_{\gamma_\nu}=m_\nu+\varepsilon_\nu
```

gives the first formula. Multiplying by `\pi/a` yields the second.

This identifies the exact arithmetic target hidden inside the direct residue
problem:

- exact affine progression theorems of Putnam / Li--Radziwi{\l}{\l} already
  kill the zero-error case;
- the live missing input is now a \emph{stability upgrade}: can critical-line
  zeros lie infinitely often within
  `o((\log T)/T^2)` of one fixed arithmetic progression?

So the integer-resonance branch is already a sharply quantified
near-lattice-zero problem, not a vague approximation statement.

```tex
\textbf{D2g24a. Conditional closure via near-progression exclusion.}
```

If one can prove that no infinite sequence of critical-line zeros satisfies

```tex
\gamma_\nu
=
\frac{\pi}{a}m_\nu
+ 
o\!\left(\frac{\log m_\nu}{m_\nu^2}\right)
```

with integers `m_\nu\to\infty`, then the integer-resonance branch of `D2g22`
is excluded. Combined with any exclusion of the microscopic-gap branch, this
would close the direct route by `D2g23`.

This near-progression branch has one more clean reformulation through the
zero-counting function.

```tex
\textbf{D2g24b. Integer resonance forces unit jumps of }S(T)\textbf{ on supertiny windows.}
```

Let

```tex
h:=\frac{\pi}{a}.
```

Assume there are integers `m_\nu\to\infty` and critical ordinates
`\gamma_\nu` such that

```tex
\gamma_\nu = h m_\nu + \delta_\nu,
\qquad
\delta_\nu=o\!\left(\frac{\log m_\nu}{m_\nu^2}\right).
```

Set `T_\nu:=h m_\nu` and `u_\nu:=|\delta_\nu|`. Then
`u_\nu=o((\log T_\nu)/T_\nu^2)` and the interval

```tex
[T_\nu-u_\nu,\ T_\nu+u_\nu]
```

contains a critical-line zero. Hence

```tex
N(T_\nu+u_\nu)-N(T_\nu-u_\nu)\ge 1.
```

Now use the Riemann--von Mangoldt decomposition

```tex
N(T)=\frac{\theta(T)}{\pi}+1+S(T),
```

where `\theta'(T)=\frac12\log(T/2\pi)+O(T^{-1})`. Then

```tex
N(T_\nu+u_\nu)-N(T_\nu-u_\nu)
=
\frac{\theta(T_\nu+u_\nu)-\theta(T_\nu-u_\nu)}{\pi}
+
S(T_\nu+u_\nu)-S(T_\nu-u_\nu).
```

Because `u_\nu=o((\log T_\nu)/T_\nu^2)`, the smooth part satisfies

```tex
\theta(T_\nu+u_\nu)-\theta(T_\nu-u_\nu)
=
O(u_\nu\log T_\nu)
=
o(1).
```

Therefore

```tex
S(T_\nu+u_\nu)-S(T_\nu-u_\nu)\ge 1-o(1),
```

and in particular, for all sufficiently large `\nu`,

```tex
S(T_\nu+u_\nu)-S(T_\nu-u_\nu)\ge \frac12.
```

So the integer-resonance branch is equivalent to a very sharp local
oscillation statement:

```tex
\text{on infinitely many windows of length }o\!\left(\frac{\log T}{T^2}\right),
\text{ the argument term }S(T)\text{ must jump by size }\asymp 1.
```

This is a much cleaner target than the raw near-progression statement. The
main term of `N(T)` is far too smooth on that scale; all the burden is pushed
onto the local oscillation of `S(T)`.

```tex
\textbf{D2g24c. Conditional closure via supertiny }S\textbf{-jump exclusion.}
```

If one can prove that there are no infinitely many windows

```tex
[T-u,T+u],
\qquad
u=o\!\left(\frac{\log T}{T^2}\right),
```

on which

```tex
S(T+u)-S(T-u)\ge \frac12,
```

then the integer-resonance branch of `D2g24` is impossible.

There is also a clean Fourier-theoretic sufficient criterion for killing this
branch, and it can be written in a completely explicit dyadic-block form.

```tex
\textbf{D2g25. Shrinking-target criterion via Fej\'er kernel.}
```

Let

```tex
\alpha:=\frac{a}{\pi},
\qquad
\mathcal N(T,2T]:=\#\{\gamma:\ T<\gamma\le 2T\},
```

and for `0<\varepsilon\le 1/4` define

```tex
A_\alpha(T,\varepsilon)
:=
\#\{\gamma:\ T<\gamma\le 2T,\ \|\alpha\gamma\|\le \varepsilon\},
```

as well as the dyadic exponential sums

```tex
S_\alpha(j;T):=\sum_{T<\gamma\le 2T} e(j\alpha\gamma),
\qquad
e(x):=e^{2\pi i x}.
```

Set

```tex
H:=\left\lfloor \frac{1}{2\varepsilon}\right\rfloor.
```

Then there exists an absolute constant `C>0` such that for every `T\ge 2`,

```tex
A_\alpha(T,\varepsilon)
\le
C\,\varepsilon\,\mathcal N(T,2T]
+
C\,\varepsilon\sum_{j=1}^{H-1}|S_\alpha(j;T)|.
```

Proof. Introduce the Fej\'er kernel

```tex
F_H(x)
:=
\sum_{|j|<H}\left(1-\frac{|j|}{H}\right)e(jx)
=
\frac1H\left(\frac{\sin(\pi Hx)}{\sin(\pi x)}\right)^2.
```

It is nonnegative. If `\|x\|\le \varepsilon`, then by the choice of `H` one
has `H\|x\|\le 1/2`. Hence `0\le \pi H\|x\|\le \pi/2`, and the elementary
estimates

```tex
\sin u\ge \frac{2}{\pi}u
\qquad (0\le u\le \pi/2),
\qquad
|\sin(\pi x)|\le \pi \|x\|
```

give

```tex
|\sin(\pi Hx)|\ge 2H\|x\|.
```

Therefore

```tex
F_H(x)
=
\frac1H\left(\frac{\sin(\pi Hx)}{\sin(\pi x)}\right)^2
\ge
\frac1H\left(\frac{2H\|x\|}{\pi\|x\|}\right)^2
=
\frac{4}{\pi^2}H.
```

So

```tex
\mathbf 1_{\{\|x\|\le \varepsilon\}}
\le
\frac{\pi^2}{4H}F_H(x).
```

Summing this with `x=\alpha\gamma` over `T<\gamma\le 2T` yields

```tex
A_\alpha(T,\varepsilon)
\le
\frac{\pi^2}{4H}\sum_{T<\gamma\le 2T}F_H(\alpha\gamma).
```

Expanding `F_H` gives

```tex
\sum_{T<\gamma\le 2T}F_H(\alpha\gamma)
\le
\mathcal N(T,2T]
+
2\sum_{j=1}^{H-1}\left(1-\frac{j}{H}\right)|S_\alpha(j;T)|.
```

Since `H\asymp 1/\varepsilon`, we obtain

```tex
A_\alpha(T,\varepsilon)
\le
C\,\varepsilon\,\mathcal N(T,2T]
+
C\,\varepsilon\sum_{j=1}^{H-1}|S_\alpha(j;T)|.
```

This is the required shrinking-target bridge.

For the branch relevant to `D2g24`, take

```tex
\varepsilon(T)=o\!\left(\frac{\log T}{T^2}\right).
```

Since classically

```tex
\mathcal N(T,2T]\ll T\log T,
```

the first term is already

```tex
\varepsilon(T)\mathcal N(T,2T]
=
o(1).
```

So only the high-frequency exponential sums remain.

```tex
\textbf{D2g26. High-frequency exponential-sum criterion.}
```

If

```tex
\varepsilon(T)\sum_{1\le j\le \lfloor 1/(2\varepsilon(T))\rfloor}
|S_\alpha(j;T)|
=
o(1),
```

then

```tex
A_\alpha(T,\varepsilon(T))=o(1).
```

Because `A_\alpha(T,\varepsilon(T))` is an integer, it follows that for all
sufficiently large `T`,

```tex
A_\alpha(T,\varepsilon(T))=0.
```

Hence there are no infinitely many zeros with

```tex
\|\alpha\gamma\|\le \varepsilon(\gamma),
\qquad
\varepsilon(T)=o\!\left(\frac{\log T}{T^2}\right).
```

This excludes the integer-resonance / near-progression branch.

Thus the live burden is now completely explicit:

```tex
\text{control }S_\alpha(j;T)\text{ for }j\lesssim \frac{1}{\varepsilon(T)}.
```

For our target scale, this means frequencies up to

```tex
j\lesssim \frac{T^2}{\log T}.
```

```tex
\textbf{D2g26a. Exceptional/nonexceptional split.}
```

The Ford--Zaharescu picture suggests the tactical fork:

1. if `\alpha=a/\pi` lies in the exceptional set

   ```tex
   \alpha=\frac{r\log p}{2\pi q},
   ```

   then one should exploit the explicit resonant density defect near the
   corresponding rational points;

2. if `\alpha` is nonexceptional, then the natural live target is the
   high-frequency estimate in `D2g26`.

So `D2g25/D2g26` is the right theorem packet: it converts the
integer-resonance branch into one explicit shrinking-target Fourier problem.

The next useful step is to strip `D2g26` down to the simplest sufficient
numerical thresholds.

```tex
\textbf{D2g27. Simple sufficient criteria for }D2g26\textbf{.}
```

Let

```tex
H(T):=\left\lfloor \frac{1}{2\varepsilon(T)}\right\rfloor.
```

Then any one of the following is sufficient to exclude the
integer-resonance branch.

### (i) Mean-`L^1` criterion

If

```tex
\frac{1}{H(T)}
\sum_{1\le j\le H(T)} |S_\alpha(j;T)|
=
o(1),
```

then `D2g26` holds.

Indeed,

```tex
\varepsilon(T)\sum_{1\le j\le H(T)} |S_\alpha(j;T)|
\asymp
\bigl(\varepsilon(T)H(T)\bigr)\,
\frac{1}{H(T)}\sum_{1\le j\le H(T)} |S_\alpha(j;T)|
=
O(1)\cdot o(1)
=
o(1).
```

### (ii) `L^2` criterion

If

```tex
\sum_{1\le j\le H(T)} |S_\alpha(j;T)|^2
=
o\!\bigl(H(T)\bigr),
```

then `D2g26` holds.

By Cauchy--Schwarz,

```tex
\sum_{1\le j\le H(T)} |S_\alpha(j;T)|
\le
H(T)^{1/2}
\left(
\sum_{1\le j\le H(T)} |S_\alpha(j;T)|^2
\right)^{1/2}
=
o\!\bigl(H(T)\bigr),
```

so (i) applies.

### (iii) Uniform criterion

If

```tex
\sup_{1\le j\le H(T)} |S_\alpha(j;T)|=o(1),
```

then `D2g26` holds.

Indeed,

```tex
\sum_{1\le j\le H(T)} |S_\alpha(j;T)|
\le
H(T)\sup_{1\le j\le H(T)} |S_\alpha(j;T)|
=
o\!\bigl(H(T)\bigr),
```

so again (i) applies.

For our shrinking-target scale

```tex
\varepsilon(T)=o\!\left(\frac{\log T}{T^2}\right),
\qquad
H(T)\asymp \frac{T^2}{\log T},
```

these become:

1. mean-`L^1` cancellation

   ```tex
   \frac{\log T}{T^2}
   \sum_{j\le T^2/\log T} |S_\alpha(j;T)|
   \to 0;
   ```

2. second-moment cancellation

   ```tex
   \sum_{j\le T^2/\log T} |S_\alpha(j;T)|^2
   =
   o\!\left(\frac{T^2}{\log T}\right);
   ```

3. the extremely strong uniform bound

   ```tex
   \sup_{j\le T^2/\log T}|S_\alpha(j;T)|\to 0.
   ```

So the live burden can now be read at three strengths. The realistic next
target is not the uniform criterion, but the mean or `L^2` one.

```tex
\textbf{D2g27a. Operational form of the shrinking-target brick.}
```

To close the integer-resonance branch, it is enough to prove either

```tex
\frac{1}{H(T)}\sum_{j\le H(T)} |S_\alpha(j;T)|=o(1)
```

or

```tex
\sum_{j\le H(T)} |S_\alpha(j;T)|^2=o(H(T)),
\qquad
H(T)\asymp \frac{T^2}{\log T}.
```

This is the cleanest quantitative version of the current arithmetic endpoint.

Now the remaining live coefficient question is extremely narrow:

```tex
\textbf{D2g16d. Real support coefficient barrier.}
```

Can a genuine local packet on the real support `Y_a=\{x_\gamma,x_\gamma-1\}`
carry coefficients asymptotically close to this single Hermite line
`\mathbb C w` at the same time as it realizes the required one-sided
near-collision geometry?

Equivalently: the only genuinely dangerous local model left is now explicit,
and it is already a paired object. So the route has become even more concrete:

- the support geometry part is done: realization already means one-sided
  microclustering;
- what remains is the coefficient/defect part;
- and any successful realization below threshold is already absorbed by
  `D2f3`.

There is also a valid but more global meta-reduction in terms of the tail
sampling operator

```tex
\mathcal T_N e :=
\left(
\sum_{y\in Y}\frac{e(y)}{y-(N+m)}
\right)_{m\ge 1}.
```

If one already has a one-sided tail-zero rigidity theorem for receivers whose
support is bounded above, then the full paired problem would follow from the
following extraction statement:

```tex
\textbf{D2h. Bounded-above extraction meta-reduction.}
```

Every nonzero element of `\ker \mathcal T_N` on the paired support class
should yield another nonzero element of `\ker \mathcal T_N` with support
bounded above.

This reduction is logically correct, but it is not currently the fastest live
route. The reason is structural: `D2h` asks for global support surgery that
preserves the entire infinite tail of sampling equations, whereas the direct
mainline `D2g1/D2f3` already works on the exact analytic shape of those
equations. No concrete extraction mechanism is visible at present, and local
search did not reveal any ready-made extremal-support principle for this
Cauchy-tail kernel.

So `D2h` should be kept as a legitimate backup reduction, but not promoted
above the sharper active split `D2g1` versus `D2f3`.

Conversely, any failure of this clean first-order picture must be carried by
infinitely many ultra-near resonances.

```tex
\textbf{D2f3. Ultra-near resonance obstruction.}
```

Any genuine infinite-support counterexample to `D2f1` must produce infinitely
many integers `m` for which some support point of `Y_a` approaches `N+m`
at scale at most `\ll (\log m)/m^2`.

This is now the sharpest honest reduction on the direct route: either prove
the no-resonance asymptotic lemma and continue from static moments, or prove
that such an ultra-near resonance regime is impossible for
`Y_a=\{x_\gamma,x_\gamma-1\}`.

There is now a more support-sensitive refinement of this direct tower.
Write the receiver in paired-pole form

```tex
R(z)=\sum_\gamma \frac{a_\gamma}{x_\gamma-z}
      -\sum_\gamma \frac{b_\gamma}{x_\gamma-1-z}.
```

After dividing by the first `k` tail zeros `N+1,\dots,N+k`, one still has a
paired-pole representation

```tex
R_k(z)
=
\sum_\gamma \frac{a_\gamma^{(k)}}{x_\gamma-z}
-
\sum_\gamma \frac{b_\gamma^{(k)}}{x_\gamma-1-z},
```

with

```tex
a_\gamma^{(k)}
=
\frac{a_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)},
\qquad
b_\gamma^{(k)}
=
\frac{b_\gamma}{\prod_{j=1}^k (x_\gamma-N-j-1)}.
```

These two coefficient towers are not symmetric. Factoring out the same
denominator from both members of each pair gives

```tex
b_\gamma^{(k)}
=
\theta_{k,\gamma}
\frac{b_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)},
\qquad
\theta_{k,\gamma}
:=
\frac{x_\gamma-N-1}{x_\gamma-N-k-1}.
```

For every fixed `\gamma`,

```tex
\theta_{k,\gamma}\longrightarrow 0
\qquad (k\to\infty).
```

So repeated tail-zero division asymptotically suppresses the shifted pole
`x_\gamma-1` relative to the leading pole `x_\gamma` inside each pair.

This produces a sharper direct theorem target:

```tex
\textbf{D3. Asymptotic one-sided decoupling.}
```

Can one normalize the divisor tower `R_k` so that a nonzero subsequential limit
survives and lives on the one-sided support `X_a=\{x_\gamma\}` only?

If yes, the direct `PO2` problem would reduce from the paired support
`Y_a=\{x_\gamma,x_\gamma-1\}` to a one-sided critical-line support class, where
the earlier arithmetic obstructions are already much stronger.

Thus the active direct route is now split very concretely:

- either prove `D2` directly as a rigidity statement for the whole paired
  support;
- or prove `D3`, meaning that divisor exhaustion forces a one-sided limit and
  then attack that limit with the already-existing critical-line barriers.

There is now a sharper internal split inside `D3`.

```tex
\textbf{D3a. Finite-packet suppression.}
```

For every fixed finite packet `F\subset\Gamma`,

```tex
\sup_{\gamma\in F} |\theta_{k,\gamma}|\longrightarrow 0
\qquad (k\to\infty).
```

So after any normalization `s_k`, the shifted part on a fixed finite packet
dies provided the normalized packet coefficients stay bounded:

```tex
\widetilde R_k(z)
:=
s_k R_k(z)
=
\sum_\gamma \frac{\alpha_\gamma^{(k)}}{x_\gamma-z}
\;-\;
\sum_\gamma \theta_{k,\gamma}\frac{\beta_\gamma^{(k)}}{x_\gamma-1-z},
```

where

```tex
\alpha_\gamma^{(k)}
:=
s_k\frac{a_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)},
\qquad
\beta_\gamma^{(k)}
:=
s_k\frac{b_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)}.
```

Thus the one-sided decoupling mechanism is genuinely present, but only
packetwise.

```tex
\textbf{D3b. No-escape / tightness brick.}
```

This packetwise suppression is **not** uniform in `\gamma`, so it does not by
itself imply a global one-sided limit. In fact:

- for fixed `\gamma`, `\theta_{k,\gamma}\to 0`;
- if
  ```tex
  \frac{x_{\gamma(k)}-N-1}{k}\to c\in (1,\infty),
  ```
  then
  ```tex
  \theta_{k,\gamma(k)}\to \frac{c}{c-1};
  ```
- if
  ```tex
  \frac{x_{\gamma(k)}-N-1}{k}\to\infty,
  ```
  then
  ```tex
  \theta_{k,\gamma(k)}\to 1.
  ```

So divisor exhaustion only suppresses the shifted member of each pair on
fixed low-lying packets; high-index mass can still survive with essentially no
decoupling. Therefore the real `D3` wall is now:

```tex
\textbf{D3b1.}
```

Can one choose a normalization and subsequence for which the normalized
coefficient mass does not escape to scales `x_\gamma\asymp k` or
`x_\gamma\gg k`?

Equivalently, the live theorem target is a tightness statement for the
normalized direct tower.

This gives a clean conditional one-sided extraction lemma.

```tex
\textbf{D3c. Conditional one-sided extraction.}
```

Assume there exist a normalization `s_k>0` and a subsequence `k_\nu` such
that:

1. the normalized coefficients satisfy a uniform `\ell^1` bound
   ```tex
   \sup_\nu \sum_\gamma
   \bigl(|\alpha_\gamma^{(\nu)}|+|\beta_\gamma^{(\nu)}|\bigr)<\infty;
   ```
2. they are tight:
   for every `\varepsilon>0` there exists a finite packet `F` with
   ```tex
   \sup_\nu \sum_{\gamma\notin F}
   \bigl(|\alpha_\gamma^{(\nu)}|+|\beta_\gamma^{(\nu)}|\bigr)<\varepsilon;
   ```
3. for every fixed `\gamma`,
   ```tex
   \alpha_\gamma^{(\nu)}\to \alpha_\gamma;
   ```
4. some limit coefficient is nonzero.

Then

```tex
\widetilde R_{k_\nu}(z)
\longrightarrow
\sum_\gamma \frac{\alpha_\gamma}{x_\gamma-z}
```

locally uniformly on compact subsets of
`\mathbb C\setminus (X_a\cup (X_a-1))`.

Indeed, one splits the sums into a finite packet `F` and its complement.
On `F`, the shifted part vanishes because `\sup_{\gamma\in F}|\theta_{k_\nu,\gamma}|\to 0`.
Outside `F`, the tails are uniformly small by tightness and the compact-set
distance to the pole set. Thus the only genuine missing ingredient in `D3` is
not compactness or Montel, but the no-escape/tightness statement.

So `D3` has now reduced to a very sharp dichotomy:

- either prove `D3b1` and get a one-sided limit;
- or accept that the direct divisor tower may leak its mass to high-index
  poles, in which case `D3` does not close and the active burden returns
  entirely to `D2`.

There is now a strong obstruction against the natural compactness version of
`D3`.

```tex
\textbf{D3d. Uniform-\ell^1\ obstruction.}
```

Assume the direct receiver is an infinite-support counterexample, so at least
one of the paired coefficient families `\{a_\gamma\}` or `\{b_\gamma\}` is
nonzero on an unbounded set of indices. Let `s_k>0` be any normalization and
write

```tex
\alpha_\gamma^{(k)}
:=
s_k\frac{a_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)},
\qquad
\beta_\gamma^{(k)}
:=
s_k\frac{b_\gamma}{\prod_{j=1}^k (x_\gamma-N-j)}.
```

If

```tex
\sup_k \sum_\gamma
\bigl(|\alpha_\gamma^{(k)}|+|\beta_\gamma^{(k)}|\bigr)<\infty,
```

then for every fixed `\gamma`,

```tex
\alpha_\gamma^{(k)}\longrightarrow 0,
\qquad
\beta_\gamma^{(k)}\longrightarrow 0.
```

Indeed, for any fixed support point `x` one has

```tex
\prod_{j=1}^k (x-N-j)
=
(-1)^k\frac{\Gamma(k+N+1-x)}{\Gamma(N+1-x)}.
```

Hence boundedness of a single normalized coefficient with nonzero numerator
forces

```tex
s_k
=
O\!\bigl(\Gamma(k+N+1-x)\bigr).
```

Now use the unboundedness of the nonzero support: for every `M>0` there exists
a support point `y>N+1+M` with nonzero numerator. Applying the previous bound
to that `y` gives

```tex
s_k
=
O(\Gamma(k-M)).
```

Therefore, for any fixed support point `x`,

```tex
\left|
s_k\frac{1}{\prod_{j=1}^k (x-N-j)}
\right|
\ll
\frac{\Gamma(k-M)}{\Gamma(k+N+1-x)}
\asymp
k^{-M-N-1+x}.
```

Since `M` is arbitrary, choosing `M>x-N-1` forces the right-hand side to tend
to `0`. Multiplying by the fixed coefficient `a_\gamma` or `b_\gamma` proves
the claim.

This kills the planned compactness extraction:

```tex
\textbf{D3c is dead for infinite support.}
```

The whole point of `D3c` was to obtain a nonzero one-sided limit on `X_a`
from a normalized tower with uniform `\ell^1` control and tightness. But the
obstruction above shows that under exactly this natural compactness regime,
every fixed packet coefficient tends to zero. So no nonzero pointwise limit on
the one-sided support can survive.

Thus the route status sharpens again:

- `D3a` remains a true finite-packet phenomenon;
- `D3c` is killed as a method for producing a nonzero one-sided limit from an
  infinite-support counterexample;
- the active direct burden shifts back to `D2`, unless a radically different
  non-`\ell^1` extraction mechanism is identified.

There is now exactly such a radically different extraction mechanism.

```tex
\textbf{D3e. \ell^2-Gibbs tower on direct coefficients.}
```

The direct divisor tower is diagonal on coefficients, not only in the backup
Hilbert model but already in the native paired Cauchy class itself. If

```tex
R(z)=\sum_{y\in Y_a}\frac{e(y)}{y-z},
```

and `R(\lambda)=0` for some tail integer `\lambda>N`, then

```tex
\frac{R(z)}{z-\lambda}
=
\sum_{y\in Y_a}\frac{e(y)}{y-\lambda}\frac{1}{y-z}.
```

Iterating at `\lambda_j=N+j` gives

```tex
R_k(z)
=
\sum_{y\in Y_a}
\frac{e^{(k)}(y)}{y-z},
\qquad
e^{(k)}(y):=
\frac{e(y)}{\prod_{j=1}^k (y-\lambda_j)}.
```

Since the inherited direct coefficients satisfy `e\in \ell^1(Y_a)` and hence
also `e\in \ell^2(Y_a)`, one may normalize in `\ell^2(Y_a)`:

```tex
u_k(y):=
\frac{e^{(k)}(y)}
{\left(\sum_{v\in Y_a}|e^{(k)}(v)|^2\right)^{1/2}},
```

and define discrete probability measures

```tex
\nu_k(y):=|u_k(y)|^2
=
\frac{|e(y)|^2\prod_{j=1}^k |y-\lambda_j|^{-2}}
{\sum_{v\in Y_a}|e(v)|^2\prod_{j=1}^k |v-\lambda_j|^{-2}}.
```

So the true non-`\ell^1` reformulation of `D3b1` is:

```tex
\textbf{D3e1.}
```

Can one prove that the family `\{\nu_k\}` is tight on the discrete support
`Y_a`?

This has a clean functional-analytic consequence.

```tex
\textbf{D3e2. Tightness implies precompactness in }\ell^2(Y_a).
```

If the probability measures `\nu_k(y)=|u_k(y)|^2` are tight, then the unit
vectors `u_k` are precompact in `\ell^2(Y_a)`. The proof is standard: for any
`\varepsilon>0`, tightness gives a finite packet `E\subset Y_a` with

```tex
\sup_k \sum_{y\notin E}|u_k(y)|^2<\varepsilon^2;
```

the projections of `u_k` to the finite-dimensional space `\mathbb C^E` are
precompact; and the tails outside `E` are uniformly small. Hence every
subsequence of `u_k` contains a further subsequence converging strongly in
`\ell^2(Y_a)`.

There is then a direct passage back to Cauchy transforms.

```tex
\textbf{D3e3. \ell^2 coefficient limits give locally uniform transform limits.}
```

For any compact set `K\Subset \mathbb C\setminus Y_a`, the kernel family

```tex
\kappa_y(z):=\frac{1}{y-z}
```

lies in `\ell^2(Y_a)` uniformly in `z\in K`, because the support points
`y\in Y_a` escape to `+\infty` and

```tex
\sum_{y\in Y_a}\frac{1}{|y-z|^2}<\infty
```

uniformly on `K`. Therefore, if `u_{k_\nu}\to u` strongly in `\ell^2(Y_a)`,
then

```tex
\sum_{y\in Y_a}\frac{u_{k_\nu}(y)}{y-z}
\longrightarrow
\sum_{y\in Y_a}\frac{u(y)}{y-z}
```

locally uniformly on compact subsets of `\mathbb C\setminus Y_a`.

Finally, the finite-packet suppression from `D3a` now interacts correctly with
this `\ell^2` normalization. If `u_{k_\nu}` is tight, then after passing to a
strongly convergent subsequence, the contribution of the shifted member
`x_\gamma-1` on every fixed packet dies because `\theta_{k_\nu,\gamma}\to 0`,
while the tail outside that packet is small in `\ell^2` by tightness. So the
new live theorem target is:

```tex
\textbf{D3e4. Anchor-block criterion.}
```

Find a finite packet `E\subset Y_a` and `\eta>0` such that

```tex
\inf_k \sum_{y\in E}\nu_k(y)\ge \eta.
```

Equivalently, prove tightness of the discrete Gibbs family `\{\nu_k\}`.

This revives `D3`, but in a genuinely new form:

- `D3d` killed only the uniform-`\ell^1` compactness extraction;
- `D3e` is a different, `\ell^2`-normalized Gibbs route;
- the exact open brick is now a finite anchor-block theorem for `\nu_k`.

This finite-anchor version now also meets a direct obstruction.

```tex
\textbf{D3f. No finite anchor block on unbounded support.}
```

Let

```tex
W_k(y):=
|e(y)|^2\prod_{j=1}^k |y-\lambda_j|^{-2},
\qquad
\nu_k(y)=\frac{W_k(y)}{\sum_{v\in Y_a}W_k(v)}.
```

Take any two fixed support points `y>y'` with `e(y)e(y')\neq 0`. Then

```tex
\frac{W_k(y)}{W_k(y')}
=
\frac{|e(y)|^2}{|e(y')|^2}
\prod_{j=1}^k
\left|\frac{y'-\lambda_j}{y-\lambda_j}\right|^2.
```

Using

```tex
\prod_{j=1}^k (x-\lambda_j)
=
(-1)^k\frac{\Gamma(k+N+1-x)}{\Gamma(N+1-x)},
```

this becomes

```tex
\frac{W_k(y)}{W_k(y')}
=
C(y,y')
\frac{\Gamma(k+N+1-y')^2}{\Gamma(k+N+1-y)^2},
```

where

```tex
C(y,y')
:=
\frac{|e(y)|^2}{|e(y')|^2}
\left|\frac{\Gamma(N+1-y)}{\Gamma(N+1-y')}\right|^2.
```

By the standard Gamma-ratio asymptotic
`\Gamma(k+a)/\Gamma(k+b)\sim k^{a-b}` (DLMF §5.11),
one gets

```tex
\frac{W_k(y)}{W_k(y')}
\sim
C(y,y')\,k^{2(y-y')}
\qquad (k\to\infty).
```

Hence every fixed support point farther to the right eventually dominates every
fixed support point to its left.

Now let `E\subset Y_a` be any finite packet, and let

```tex
M_E:=\max E.
```

If the counterexample has unbounded nonzero support, choose a support point
`y_*>M_E` with `e(y_*)\neq 0`. Then for every `y\in E`,

```tex
\frac{W_k(y)}{W_k(y_*)}\longrightarrow 0,
```

so

```tex
\nu_k(E)
=
\frac{\sum_{y\in E}W_k(y)}{\sum_{v\in Y_a}W_k(v)}
\le
\frac{\sum_{y\in E}W_k(y)}{W_k(y_*)}
\longrightarrow 0.
```

Therefore:

```tex
\textbf{D3e4 is false for every infinite-support counterexample.}
```

No fixed finite anchor block can carry uniformly positive Gibbs mass.
Equivalently, the probability measures `\nu_k` are not tight on `Y_a`.

This kills the new `\ell^2` extraction route as a path to a one-sided limit:

- `D3e1` remains a correct coefficient reformulation;
- `D3e2` and `D3e3` remain true conditional implications;
- but `D3e4` fails on any unbounded nonzero support, so the route never
  reaches its own compactness input.

So the `D3` diagnosis is now brutally sharp:

- finite-packet suppression is true;
- uniform-`\ell^1` compactness is dead;
- finite-anchor `\ell^2` Gibbs tightness is dead;
- the active direct burden returns entirely to `D2`.

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

There is, however, one more clean sharpening inside this sparse danger.

```tex
\textbf{Critical-line affine-lattice exclusion.}
```

If an infinite affine unit lattice sits inside the **real** part of `Y_a`, then
after undoing the scaling `x_\gamma=a\gamma/\pi` it gives an infinite vertical
arithmetic progression of zeta zeros on the critical line:

```tex
\gamma=\gamma_0+\frac{\pi}{a}n,
\qquad
\zeta\!\left(\frac12+i\gamma\right)=0
\qquad (n\ge 0).
```

This is already ruled out by the known arithmetic-progression theorems for
critical-line zeros. Putnam proved the absence of infinite arithmetic
progressions of positive zeros on `\zeta(\tfrac12+it)`, and Li--Radziwi{\l}{\l}
showed more generally that in every vertical arithmetic progression on the
critical line, at least one-third of the points are not zeros.

So the exact sparse danger does **not** live on the real axis of `Y_a`.
Any surviving affine-lattice mechanism must therefore come from points of
`Y_a` with nonzero imaginary part, i.e. from genuinely off-critical zeros.

This is a meaningful narrowing:

1. the critical-line lattice branch is already dead;
2. the only remaining sparse affine-lattice danger is the off-critical branch;
3. that remaining branch is automatically conditional on RH failing in the
   first place, which makes it much less attractive as the next critical-path
   move.

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

#### New external backend candidate: Cauchy-de Branges rather than Carlson

There is now a more native external literature match for the direct receiver
than either the finite-pole De Micheli--Viano bridge or the rotated
Pila--Yoshino gap. The actual `PO2` object is a **discrete Cauchy transform**
on a complex support:

```tex
R(z)=\sum_{y\in Y_a}\frac{e(y)}{y-z},
\qquad
Y_a=\{x_\gamma,\ x_\gamma-1\}.
```

Recent work of Baranov, Abakumov and Belov studies exactly this genre of
objects:

- Cauchy-de Branges spaces are built from discrete Cauchy transforms on
  complex supports;
- Krein-type theorems are proved for **ratios** of discrete Cauchy transforms;
- localization theorems study when the zeros of all Cauchy transforms are
  forced to stay near the support.

This is much closer in spirit to our current receiver than:

1. De Micheli--Viano, whose explicit theorem packet is finite-pole;
2. Pila/Yoshino, whose boundary orientation is transposed relative to `H_a`.

So the second analytic route should now be sharpened again. The next honest
theorem-sized probe is:

```tex
\textbf{Cauchy-de Branges backend probe.}
```

Check whether the actual structured class generated by `Y_a` and the inherited
`O(\gamma^{-3})` residues falls into a Cauchy-de Branges framework where one
can import one of the following two consequences.

There is a concrete compatibility point here: the localization results in this
literature are stated for Cauchy transforms with `\ell^2` data, while our live
receiver coefficients inherited from `PO2` satisfy

```tex
c_\gamma,d_\gamma=O(\gamma^{-3}),
```

hence belong to `\ell^2` a fortiori under the classical zero-counting law.
So if the geometric hypotheses on the support are met, the coefficient class is
already stronger than what this backend asks for.

The two desired consequences are:

1. a **localization** principle saying that a tail of zeros on the integers
   forces an attraction set of the support near that integer tail;
2. a **Krein-type / ordering** principle for ratios of discrete Cauchy
   transforms that would turn eventual shift equality into global equality.

If either import lands, it attacks the true receiver directly rather than
through a surrogate transport theorem.

So the second analytic route now has a clean three-step operational packet:

```tex
\textbf{CB1. Support admissibility.}
```

Verify whether the structured support

```tex
Y_a=\{x_\gamma,\ x_\gamma-1\}
```

with the inherited `\ell^2` residue class sits inside one of the admissible
discrete-support frameworks of the Cauchy-de Branges literature.

This now looks essentially positive.

First, after merging any coincident points of `Y_a` into a single support point
with summed residue, the actual pole support is a discrete set `T_a\subset\CC`
with pairwise distinct points and `|t|\to\infty`.

Second, we already know from the `\xi`-side geometry that `T_a` lies in a
fixed strip:

```tex
\Re t\ge -1,
\qquad
|\Im t|\le \frac{a}{2\pi}.
```

Third, the counting law

```tex
n_{Y_a}(R)\asymp \frac{R\log R}{a}
```

implies finite convergence exponent. In particular,

```tex
\sum_{t\in T_a}\frac{1}{|t|^{2}+1}<\infty.
```

Therefore the natural Cauchy-de Branges spectral datum with unit weights

```tex
\mu_a:=\sum_{t\in T_a}\delta_t
```

already satisfies the basic summability requirement

```tex
\sum_{t\in T_a}\frac{\mu_a(\{t\})}{|t|^2+1}<\infty.
```

Choosing any canonical product `A_a` with simple zero set `T_a`, we land in a
space `\mathcal H(T_a,A_a,\mu_a)` of the exact type treated in the
Baranov--Abakumov--Belov framework. Moreover, because the `PO2` coefficients
obey `e(t)=O(|t|^{-3})`, the receiver actually satisfies

```tex
e\in \ell^2(T_a,\mu_a),
```

so the coefficient class is comfortably inside the native Hilbert-space input
of that theory.

Thus the honest status of `CB1` is no longer “unknown”. It is:

```tex
\textbf{CB1a. Krein/ordering admissibility is essentially positive.}
```

What remains is not support admissibility itself, but whether the available
localization/ordering theorems apply to a tail of prescribed real zeros in the
way `PO2` needs.

```tex
\textbf{CB2. Tail-zero localization.}
```

Translate the eventual integer-tail vanishing

```tex
R(m)=0\qquad (m>N)
```

into the language of zero localization for discrete Cauchy transforms:
does a whole tail of real zeros force a corresponding attraction set of the
support near that tail?

Here one new obstruction must already be written down explicitly. The
localization paper of Abakumov--Baranov--Belov assumes that the support `T` is
**power separated**:

```tex
\operatorname{dist}(t_n,T\setminus\{t_n\})\ge C|t_n|^{-N}.
```

For the actual zeta-derived support `Y_a=\{x_\gamma,\ x_\gamma-1\}` we do not
currently have such a theorem. It would amount to a polynomial lower bound on
all mutual gaps between the scaled ordinates `x_\gamma` and their shifted copy,
which is far stronger than anything presently frozen in `PO2`.

So the second analytic branch now splits again:

```tex
\textbf{CB2a. Krein/ordering branch.}
```

This remains genuinely live because the 2018 Cauchy-de Branges Krein theory
only needs the strip/finite-exponent geometry already available in case `\Pi`.

Moreover, the tail-zero structure itself has a clean entire divider:

```tex
E_N(z):=\Gamma(N+1-z)^{-1}.
```

Since `1/\Gamma` is entire with simple zeros at the nonpositive integers,
`E_N` is entire with simple zero set exactly

```tex
\{N+1,N+2,\dots\}.
```

So if the ambient entire function

```tex
F_a(z):=A_a(z)R(z)
```

vanishes on the integer tail, then the quotient

```tex
\widetilde F_a(z):=\frac{F_a(z)}{E_N(z)}
```

is again entire. This gives the first concrete theorem-shaped entry point into
the ordering machinery: factor out the common tail-zero set exactly, then ask
whether the quotient class defines a `*`-closed nearly invariant subspace
without common zeros, to which the strip-case ordering theorem can apply.

Thus the live Krein/ordering packet should now be read as:

```tex
\textbf{CB2a1. } *\textbf{-symmetry of the ambient } \mathcal H(T_a,A_a,\mu_a);
```

```tex
\textbf{CB2a2. exact tail-zero factorization by } E_N(z)=\Gamma(N+1-z)^{-1};
```

```tex
\textbf{CB2a3. nearly-invariant quotient subspace and ordering applicability.}
```

The first of these subtargets now looks essentially positive too.

Indeed, the zero set of `\xi(1/2-iz)` is stable under complex conjugation,
because `\xi(\bar s)=\overline{\xi(s)}`. Therefore

```tex
\gamma\in\mathcal Z_+\Longrightarrow \bar\gamma\in\mathcal Z_+,
\qquad
x_{\bar\gamma}=\overline{x_\gamma},
```

and the merged support

```tex
T_a=\{x_\gamma,\ x_\gamma-1\}
```

is invariant under `t\mapsto \bar t`.

Choose symmetric weights `\mu_a(\{t\})=1` and choose the canonical product
`A_a` with zero set `T_a` in a conjugation-symmetric normalization, so that

```tex
A_a^*(z):=\overline{A_a(\bar z)}=A_a(z).
```

Then for

```tex
f(z)=A_a(z)\sum_{t\in T_a}\frac{c_t}{z-t}
```

one has

```tex
f^*(z)
=
\overline{f(\bar z)}
=
A_a(z)\sum_{s\in T_a}\frac{\overline{c_{\bar s}}}{z-s},
```

after reindexing by `s=\bar t`. Since the involution

```tex
c\mapsto c^\sharp,\qquad c^\sharp_s:=\overline{c_{\bar s}},
```

preserves `\ell^2(T_a,\mu_a)`, the ambient Cauchy-de Branges space is
`*`-closed at the natural support/coefficient level.

So the honest status is now:

```tex
\textbf{CB2a1 is essentially positive under the natural symmetric choice of }
(T_a,\mu_a,A_a).
```

This means the live Krein/ordering wall has narrowed again. The next actual
hard point inside branch `CB2a` is no longer `*`-symmetry. It is:

```tex
\textbf{CB2a3. Can the tail-zero quotient class be organized into a nontrivial
nearly invariant `*`-closed subspace without common zeros?}
```

There is now a useful intermediate receiver before taking the quotient.
Define the ambient Cauchy-de Branges space

```tex
\mathcal H_a:=\mathcal H(T_a,A_a,\mu_a),
```

and the tail-zero subspace

```tex
\mathcal H_a^{\mathrm{tail}}
:=
\{f\in \mathcal H_a:\ f(m)=0\ \forall m>N\}.
```

Under the `PO2` counterexample hypothesis this space is nontrivial, because
`F_a(z)=A_a(z)R(z)` belongs to it and is not identically zero.

This subspace already has the three formal properties one wants:

1. it is **closed**, being the intersection of kernels of the bounded
   evaluation functionals `f\mapsto f(m)`;
2. it is `*`-closed, because the tail integers are real and the ambient space
   is `*`-closed;
3. it is **nearly invariant**: if `w_0` is any point outside the common-zero
   set of `\mathcal H_a^{\mathrm{tail}}` and outside the tail integers, then
   for every `f\in \mathcal H_a^{\mathrm{tail}}` with `f(w_0)=0` one has
   `f/(z-w_0)\in\mathcal H_a` by the ambient division property, and this
   quotient still vanishes at every integer `m>N` because `w_0\neq m`.

So the live issue in `CB2a3` is no longer whether a natural candidate subspace
exists. It does. The real question is subtler:

```tex
\textbf{CB2a3'.}
```

Can one combine this tail-zero subspace with either

- the exact common-zero factor `E_N(z)=\Gamma(N+1-z)^{-1}`, or
- Remark 5.3 on nearly invariant subspaces with the same common zeros,

to produce the **second comparable subspace** needed for the strip-case
ordering theorem to force a contradiction?

There is now a further refinement. The exact wording of Theorem 1.4 and
Remark 5.3 from the 2018 Cauchy-de Branges paper shows that the bookkeeping
role of `E_N` is weaker than it first appeared:

- Theorem 1.4 orders nearly invariant `*`-closed subspaces **without common
  zeros** in the strip case.
- Remark 5.3 says the same proof extends to nearly invariant subspaces having
  the **same** sets of common zeros (counted with multiplicities).

So explicit division by `E_N` is not the conceptual bottleneck. One may divide
by `E_N` to pass to a no-common-zero model if this is technically convenient,
but the ordering theorem can also be applied directly once two candidate
subspaces are known to carry the same tail-zero set.

This sharpens the live wall inside the Krein branch:

```tex
\textbf{CB2a3a.}
```

The common-zero package is formally benign: the tail-zero set
`\{N+1,N+2,\dots\}` can be handled either by explicit factorization through
`E_N` or directly via Remark 5.3.

```tex
\textbf{CB2a3b.}
```

The actual missing ingredient is the construction of a **second**
nontrivial nearly invariant `*`-closed tail-zero subspace from the `PO2`
counterexample data. Without this second subspace, ordering is vacuous: the
theorem only says any two such subspaces are comparable, but a single natural
subspace `\mathcal H_a^{\mathrm{tail}}` gives no contradiction by itself.

There is now a more concrete internal candidate for this second subspace.
Take any nonzero `F\in \mathcal H_a^{\mathrm{tail}}`. Since
`\mathcal H_a^{\mathrm{tail}}` is `*`-closed, at least one of

```tex
G_0:=F+F^*,
\qquad
\widetilde G_0:=\frac{F-F^*}{i}
```

is nonzero, belongs to `\mathcal H_a^{\mathrm{tail}}`, and is `*`-symmetric.
Fix such a nonzero `G_0` with `G_0^*=G_0`. Because `G_0(m)=0` for every
`m>N`, repeated division by real tail zeros stays inside the ambient space:

```tex
G_k(z):=\frac{G_0(z)}{\prod_{j=1}^k (z-(N+j))},
\qquad k\ge 0.
```

Each `G_k` lies in `\mathcal H_a`, is `*`-symmetric, and vanishes on every
integer `m>N+k`. This produces a natural chain of tail-zero functions already
inside the ambient Cauchy-de Branges space.

If one can now ensure the technical hypotheses needed for the standard
construction `H_G`,

```tex
H_{G_k}:=\operatorname{Span}\left\{\frac{G_k(z)}{z-\lambda}: G_k(\lambda)=0\right\},
```

then each `H_{G_k}` is a nearly invariant subspace; and because `G_k^*=G_k`,
these subspaces are natural candidates for `*`-closed companions generated by
the same `PO2` counterexample data.

So the live wall sharpens once more:

```tex
\textbf{CB2a3c.}
```

Can one promote the division chain `G_k` to an actual chain of nontrivial
nearly invariant `*`-closed subspaces `H_{G_k}` in the strip case, and show
that at least two of them are genuinely distinct so that the ordering theorem
becomes non-vacuous?

This is a better theorem target than the earlier abstract request for "some
second subspace", because the candidate is now internal and receiver-native:
it comes directly from tail-zero division in `\mathcal H_a`, not from an
external interpolation theorem.

There is also a first structural consequence available almost for free once the
spaces `H_{G_k}` are known to be legitimate nearly invariant subspaces.
Put

```tex
a_k:=N+k+1,
\qquad
G_k(z)=(z-a_k)G_{k+1}(z).
```

Take any zero `\lambda` of `G_{k+1}`.

- If `\lambda\neq a_k`, then `\lambda` is also a zero of `G_k`, so
  `G_k/(z-\lambda)\in H_{G_k}` by definition; this function vanishes at
  `a_k`, hence division invariance of `H_{G_k}` gives
  ```tex
  \frac{G_k(z)}{(z-\lambda)(z-a_k)}=\frac{G_{k+1}(z)}{z-\lambda}\in H_{G_k}.
  ```
- If `\lambda=a_k` is also a zero of `G_{k+1}`, then
  `G_k/(z-a_k)=G_{k+1}\in H_{G_k}` already, and one divides further at `a_k`
  as many times as needed.

Thus, modulo the legitimacy of each `H_{G_k}`, one gets a natural descending
chain

```tex
H_{G_{k+1}}\subset H_{G_k}\qquad (k\ge 0).
```

So the existential part of "find a second subspace" is no longer the real
issue either. The live obstruction sharpens yet again:

```tex
\textbf{CB2a3d.}
```

Show that this chain is **strict** for at least one step, or equivalently that
tail-zero division eventually changes the associated `H_G`-subspace in a
provable way. In practice this is now a multiplicity-exhaustion problem at the
first few tail integers, not a search for an unrelated companion subspace.

There is now a sharper algebraic skeleton behind this strictness problem.
Let

```tex
\mathcal A_k
:=
\operatorname{span}_{\mathrm{fin}}
\left\{
\frac{G_k(z)}{z-\lambda}:\ \lambda\in Z(G_k)
\right\},
```

so that `H_{G_k}` is the closure of `\mathcal A_k` in the ambient
Cauchy-de Branges norm whenever the construction is legitimate.

For any finite combination

```tex
f(z)=\sum_{\lambda\in Z(G_k)} c_\lambda \frac{G_k(z)}{z-\lambda},
```

define the algebraic coefficient-sum functional

```tex
L_k(f):=\sum_{\lambda} c_\lambda.
```

This is well defined on `\mathcal A_k`, because the family
`\{G_k(z)/(z-\lambda)\}_{\lambda\in Z(G_k)}` is linearly independent on finite
combinations: if

```tex
\sum_{\lambda\in F} c_\lambda \frac{G_k(z)}{z-\lambda}\equiv 0,
```

then dividing by the nonzero entire function `G_k` and taking residues at the
simple poles shows `c_\lambda=0` for all `\lambda\in F`.

Now let `a_k=N+k+1`. Each generator of `\mathcal A_{k+1}` has the form

```tex
\frac{G_{k+1}(z)}{z-\mu}
=
\frac{G_k(z)}{(z-a_k)(z-\mu)}
=
\frac{1}{a_k-\mu}
\left(
\frac{G_k(z)}{z-a_k}-\frac{G_k(z)}{z-\mu}
\right),
```

so every such generator lies in `\mathcal A_k` and has coefficient sum zero.
Conversely, any finite combination in `\mathcal A_k` with zero coefficient sum
can be rewritten against the distinguished pole `a_k` and therefore belongs to
`\mathcal A_{k+1}`. Thus

```tex
\mathcal A_{k+1}
=
\ker L_k \cap \mathcal A_k.
```

There is also an asymptotic expression for `L_k`. For finite combinations,

```tex
\frac{f(z)}{G_k(z)}
=
\sum_{\lambda}\frac{c_\lambda}{z-\lambda}
=
\frac{1}{z}\sum_{\lambda} c_\lambda + O(z^{-2}),
\qquad z\to\infty,
```

so

```tex
L_k(f)=\lim_{z\to\infty} z\,\frac{f(z)}{G_k(z)}.
```

This produces a very concrete strictness mechanism:

```tex
\textbf{CB2a3e.}
```

Can `L_k` be extended to a nonzero bounded linear functional on the closed
space `H_{G_k}`?

If yes, then `\ker L_k` is a proper closed hyperplane in `H_{G_k}` containing
`H_{G_{k+1}}`, while

```tex
L_k\!\left(\frac{G_k(z)}{z-a_k}\right)=1,
```

so one gets

```tex
H_{G_{k+1}}\subsetneq H_{G_k}.
```

This does **not** close `PO2` by itself, but it isolates the true analytic
brick inside the backup Krein branch: boundedness of the first asymptotic
coefficient functional, rather than the mere existence of a second subspace.

There is now a corrected conditional theorem behind this mechanism.
The earlier informal version had two sign/orientation mistakes:

- the tail-zero chain must be
  ```tex
  G_k(z)=\frac{G_0(z)}{P_k(z)},
  \qquad
  P_k(z):=\prod_{j=1}^k (z-(N+j)),
  ```
  not `G_0(z)P_k(z)`;
- the needed vertical jet is a negative-power expansion for `A/G_0` along
  `iy`, not a positive-power one.

So the honest theorem-shape is:

```tex
\textbf{CB2a3e1.}
```

Let the ambient Cauchy-de Branges space be

```tex
\mathcal H(T,A,\mu)
=
\left\{
f(z)=A(z)\sum_n \frac{a_n\mu_n^{1/2}}{z-t_n}:\ a\in \ell^2
\right\},
```

with `T=\{t_n\}` contained in a horizontal strip `|\Im t_n|\le h`, and assume
the weighted moments

```tex
M_r^2:=\sum_n \mu_n |t_n|^{2r}<\infty
\qquad (0\le r\le k+1).
```

Fix the division chain

```tex
G_k(z)=\frac{G_0(z)}{P_k(z)},
\qquad
P_k(z)=\sum_{m=0}^k p_m^{(k)} z^m
=\prod_{j=1}^k (z-(N+j)).
```

Assume that along the imaginary axis one has the vertical jet

```tex
\frac{A(iy)}{G_0(iy)}
=
\beta_0+\frac{\beta_1}{iy}+\cdots+\frac{\beta_k}{(iy)^k}
+o(|y|^{-k}).
```

Then, for

```tex
Q_k(z):=\frac{A(z)}{G_k(z)}=P_k(z)\frac{A(z)}{G_0(z)},
```

one gets a polynomial asymptotic

```tex
Q_k(iy)
=
q_0^{(k)}+q_1^{(k)}(iy)+\cdots+q_k^{(k)}(iy)^k+o(1),
```

with explicit coefficients

```tex
q_r^{(k)}
=
\sum_{n=0}^{k-r} p_{r+n}^{(k)}\,\beta_n
\qquad (0\le r\le k).
```

For

```tex
f(z)=A(z)\sum_n \frac{a_n\mu_n^{1/2}}{z-t_n},
```

define the moment functionals

```tex
\Lambda_r(f):=\sum_n a_n\mu_n^{1/2} t_n^r.
```

By Cauchy-Schwarz, each `\Lambda_r` is bounded on `\mathcal H(T,A,\mu)`:

```tex
|\Lambda_r(f)|
\le
M_r \|f\|_{\mathcal H}.
```

Moreover, for `f\in \mathcal A_k` one has

```tex
L_k(f)
=
\sum_{r=0}^k q_r^{(k)} \Lambda_r(f).
```

Indeed, along `z=iy` one expands

```tex
\frac{z}{z-t}
=
1+\frac{t}{z}+\cdots+\frac{t^k}{z^k}
+\frac{t^{k+1}}{z^k(z-t)},
```

so

```tex
\frac{z\,f(iy)}{A(iy)}
=
\Lambda_0(f)+\frac{\Lambda_1(f)}{iy}+\cdots+\frac{\Lambda_k(f)}{(iy)^k}
+O\!\left(\|f\|_{\mathcal H}|y|^{-(k+1)}\right).
```

Multiplying by `Q_k(iy)` and taking the constant term gives
`\sum_{r=0}^k q_r^{(k)}\Lambda_r(f)`. On the other hand, for

```tex
f(z)=\sum_{\lambda} c_\lambda \frac{G_k(z)}{z-\lambda}\in \mathcal A_k,
```

one has

```tex
\frac{z\,f(z)}{G_k(z)}
=
\sum_{\lambda} c_\lambda \frac{z}{z-\lambda}
\longrightarrow
\sum_{\lambda} c_\lambda
=
L_k(f).
```

Hence `L_k` agrees on `\mathcal A_k` with the bounded functional

```tex
\widetilde L_k(f):=\sum_{r=0}^k q_r^{(k)} \Lambda_r(f),
```

and therefore extends continuously to the closed space `H_{G_k}`.
Consequently,

```tex
H_{G_{k+1}}\subsetneq H_{G_k}.
```

This is a real theorem inside the backup branch. But it is still conditional:
to use it in `PO2`, one would still have to verify the strip moments and the
vertical jet for the actual ambient data and the actual `G_0`.

There is now a more route-native reading of this same criterion.
In the actual `PO2` backup branch, the starting generator `G_0` is not an
arbitrary outer quotient but a `*`-symmetric element of the ambient
Cauchy-de Branges space, obtained from a tail-zero witness
`F\in \mathcal H_a^{\mathrm{tail}}` by taking

```tex
G_0=F+F^*
\qquad\text{or}\qquad
G_0=\frac{F-F^*}{i}.
```

Therefore one has the genuine Cauchy representation

```tex
\frac{G_0(z)}{A(z)}
=
\sum_n \frac{b_n}{z-t_n},
\qquad
b_n:=a_n\mu_n^{1/2},
```

and the natural asymptotic object is not initially `A/G_0`, but

```tex
z\,\frac{G_0(z)}{A(z)}.
```

Under the same strip and moment hypotheses, one gets the expansion

```tex
z\,\frac{G_0(iy)}{A(iy)}
=
\alpha_0+\frac{\alpha_1}{iy}+\cdots+\frac{\alpha_m}{(iy)^m}
+O(|y|^{-m-1}),
```

where

```tex
\alpha_r=\sum_n b_n t_n^r.
```

Indeed, this is just the direct Cauchy expansion

```tex
\frac{z}{z-t}
=
1+\frac{t}{z}+\cdots+\frac{t^m}{z^m}
+\frac{t^{m+1}}{z^m(z-t)},
```

summed against the coefficients `b_n`, with the remainder controlled by the
moment bound at order `m+1`.

This exposes the true route-specific subtarget:

```tex
\textbf{CB2a3e2.}
```

Determine the first nonzero moment

```tex
\alpha_s=\sum_n b_n t_n^s.
```

If `s` is the smallest index with `\alpha_s\neq 0`, then

```tex
z\,\frac{G_0(iy)}{A(iy)}
\asymp
\frac{\alpha_s}{(iy)^s},
```

so

```tex
\frac{A(iy)}{G_0(iy)}
\asymp
(iy)^{s+1}.
```

Consequently, for

```tex
Q_k(z):=\frac{A(z)}{G_k(z)}=P_k(z)\frac{A(z)}{G_0(z)},
```

the leading asymptotic degree is not generically `k`, but

```tex
k+s+1.
```

In the generic case `\alpha_0\neq 0`, one gets degree `k+1`; if
`\alpha_0=0`, the bridge shifts upward and one needs correspondingly more
moment functionals `\Lambda_r` in the boundedness theorem for `L_k`.

So the actual route-specific backup brick is sharper than the abstract jet
criterion:

```tex
\alpha_0(G_0)\stackrel{?}{=}0,
\qquad
\alpha_1(G_0)\stackrel{?}{=}0.
```

This does not change the active critical path, which remains direct `D2/D3`.
But it makes the backup branch far less vague: the first real computational
question there is to identify the first nonzero moment of
`z\,G_0/A`.

However, this observation comes with an important logical correction.
A strict descending chain

```tex
H_{G_{k+1}}\subsetneq H_{G_k}
```

is still perfectly compatible with the strip-case ordering theorem: Theorem 1.4
asserts total order, not collapse. So `CB2a3d` is **not** by itself a closure
lemma for `PO2`. It is only a preparatory interface statement.

The genuine contradiction would still have to come from an additional bridge,
for example:

- a localization/attraction theorem that reads the changing tail-zero chain and
  forces an impossible support-attraction pattern; or
- a second construction producing two candidate subspaces that are not already
  locked into the same nested chain.

This means the honest status is now:

```tex
\textbf{CB2a3d}
```

is useful only as input to

```tex
\textbf{CB3a.}
```

Can the strict tail-zero subspace chain be converted into an
ordered-attraction contradiction for the actual support `T_a`?

At present this is exactly where the Krein branch meets the previously
recorded localization obstruction: the 2022 localization paper orders
attraction sets for measures in the localization class, but our import of that
class is still blocked by the missing power-separation control on `Y_a`.

This obstruction is now sharper after re-reading the exact theorem package of
the 2022 paper. The setup there is not merely "assume localization"; the paper
explicitly fixes throughout a **power separated** support sequence `T`, then
defines localization for `H(T,A,\mu)` in that regime, proves Theorem 1.1 only
for such `T`, and derives the attraction-set ordering theorem (Theorem 1.3)
inside the same framework.

So there is currently no imported theorem saying that our special tail-zero
chain alone weakens the power-separation requirement. The known attraction-set
machinery still lives strictly on the other side of the same arithmetic wall.

So unless this gap is weakened for our very special tail-zero chain, the
receiver-native Krein route remains structurally attractive but not yet
proof-bearing.

At the current evidence level the honest strategic verdict is therefore:

```tex
\textbf{CB3a is blocked by the same power-separation wall.}
```

This demotes the Krein/ordering branch from active critical path to
well-motivated backup. The fastest live route for `PO2` returns to the direct
receiver:

```tex
P,Q\in \mathcal C_a,\qquad
P(m)=Q(m+1)\ \forall m>N
\Longrightarrow
P(z)=Q(z+1).
```

That is, after all these reductions, the direct structured shift-uniqueness
problem is again the main theorem-sized target rather than the
localization/Krein backend.

```tex
\textbf{CB2b. Localization branch.}
```

This is **not** a routine next lemma, because it imports the extra power
separation hypothesis, which is not currently available for `Y_a`.

```tex
\textbf{CB3. Ordered-attraction contradiction.}
```

Combine any such attraction result with the already-recorded death of the
critical-line affine-lattice branch. If the ordered-attraction machinery still
forces a real-axis support component, `PO2` closes. If it allows only an
off-critical attraction set, then the first route is reduced all the way down
to a purely off-critical obstruction and branch 2 still wins as the active
path.

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

#### External pole-recovery analogue: the direct wall is now an adaptation wall

There is already a close external theorem pattern for the minimal receiver.
De Micheli--Viano prove that, for a suitable Carlson-type class of functions
meromorphic in a half-plane, the positions and residues of the poles can be
recovered from samples on the positive real axis (in their formulation, on the
positive half-integers), and the function can then be reconstructed by an
interpolation formula that explicitly includes the poles.

This does **not** solve our wall as stated, but it sharpens it further. The
actual direct target is no longer "some uniqueness theorem for `\mathcal C_a`".
It is now an adaptation problem:

```tex
\textbf{Pole-recovery adaptation target.}
```

Adapt a meromorphic interpolation / pole-recovery theorem from a generic
Carlson-type half-plane class to the actual receiver

```tex
R(z)=P(z)-Q(z+1)=\sum_{y\in Y_a}\frac{e(y)}{y-z},
\qquad
Y_a=\{x_\gamma,\ x_\gamma-1\},
```

with the special input

```tex
R(m)=0\qquad \forall m>N.
```

If such an adaptation lands, then the conclusion is immediate: the pole
recovery theorem forces all residues to vanish, hence `e\equiv 0`, hence
`P(z)=Q(z+1)` identically.

So the direct route is now best read as three concrete subchecks:

1. verify that the actual receiver `R` lies in an admissible meromorphic
   half-plane class with the needed growth;
2. replace the paper's positive half-integer sampling set by our tail-integer
   set (or reduce one to the other by a harmless shift/rescaling);
3. check that the theorem tolerates the structured real pole set
   `Y_a=\{x_\gamma,x_\gamma-1\}` and our `\ell^1` residue class.

At the current information level, this is the cleanest external bridge to the
minimal shift-uniqueness receiver. It does not prove `PO2`, but it converts
the remaining wall into a sharply testable adaptation problem rather than a
free-form uniqueness guess.

#### The adaptation wall already splits into one easy side and one hard side

The De Micheli--Viano bridge is not uniformly hard. Once written against the
actual receiver `R(z)=\sum_{y\in Y_a} e(y)/(y-z)`, the checks separate rather
cleanly:

```tex
\textbf{A1. Grid normalization.}
```

Their theorem is stated for samples on the positive half-integers, whereas our
input is

```tex
R(m)=0\qquad (m>N,\ m\in\mathbb N).
```

This part is harmless: after the shift

```tex
S(z):=R\!\left(z-\frac12\right),
```

one has

```tex
S\!\left(n+\frac12\right)=R(n),
```

so the sample lattice mismatch is only a translation, not a structural wall.

```tex
\textbf{A2. Meromorphic class and growth.}
```

This wall is now sharper than before, and it splits into two very different
subchecks.

```tex
\textbf{A2a. Soft class hypotheses look compatible.}
```

Because `e\in\ell^1(Y_a)`, the receiver is a simple-pole Cauchy transform.
After the translation

```tex
R_N(z):=R\!\left(z+N+\frac12\right),
```

the positive half-integer sample values vanish identically, so the weighted
sample condition in the De Micheli--Viano theorem packet is automatic:

```tex
\sum_{n\ge 0}\frac{|R_N(n+\frac12)|}{n+1}=0.
```

Moreover, away from the shifted pole set one still has sectorial
`R_N(z)=O(|z|^{-1})`, and provided no shifted pole lies on the imaginary axis,
the boundary trace `t\mapsto R_N(it)` is still an `L^2` sum of simple Cauchy
atoms. So the soft growth/integrability side does not look like the real
obstruction.

```tex
\textbf{A2b. The actual hard wall is finite poles versus the real receiver.}
```

The external theorem packet we are trying to import is written for one simple
pole in the right half-plane, with the authors explicitly noting that the
extension to several first-order poles is straightforward. This is therefore a
finite-pole theorem shape.

Our actual shifted receiver is not of that type:

```tex
R_N(z)=\sum_{y\in Y_a}\frac{e(y)}{(y-N-\frac12)-z},
\qquad
Y_a=\{x_\gamma,\ x_\gamma-1\},
```

and the pole set is countably infinite. Since `x_\gamma=a\gamma/\pi` has
unbounded real part, infinitely many shifted poles still remain in
`\Re z>0`. So the bridge is not "just a Carlson bound check". The genuine
adaptation target is now an infinite-pole extension for an `\ell^1`
simple-Cauchy class.

This also kills the most tempting normalization shortcut. It is true in
general that a large real translation can push a **finite** right-half-plane
pole set into the left half-plane, thereby reducing a meromorphic sampling
problem to an analytic Carlson-type one. But our actual support is not
right-bounded:

```tex
x_\gamma=\frac{a\gamma}{\pi}\to+\infty
\qquad (\gamma\in\mathcal Z_+),
```

so for every fixed translation parameter `M` the shifted set

```tex
\{x_\gamma-M-\tfrac12,\ x_\gamma-M-\tfrac32\}
```

still contains infinitely many points with positive real part. Therefore the
analytic De Micheli--Viano branch cannot be reached by a one-time shift. Any
route through that paper must either:

1. genuinely extend the finite-pole meromorphic theorem to our infinite-pole
   `\ell^1` Cauchy class; or
2. be abandoned as a critical-path tool.

```tex
\textbf{A3. Tail-to-full sample reduction collapses only as a grid issue.}
```

The external theorem reads the **full** sample sequence on the positive
half-integers, while our input is only

```tex
R(m)=0\qquad \forall m>N.
```

But for the actual receiver this is not a genuine wall. Define the translated
function

```tex
R_N(z):=R\!\left(z+N+\frac12\right).
```

Then for every integer `n\ge 0`,

```tex
R_N\!\left(n+\frac12\right)=R(n+N+1)=0.
```

So tail vanishing on integers becomes full vanishing on the positive
half-integer grid after one fixed translation. At the level of sample geometry,
the former tail/full gap really does collapse.

But this does **not** finish admissibility by itself, because the same
translation also moves the entire infinite pole set. So `A3` is no longer a
hard wall, but its collapse must now be read under the new `A2b` obstruction.

```tex
\textbf{A4. Sample-pole collisions.}
```

The theorem also silently assumes that the sampling lattice does not hit the
poles. For our support this means we must understand whether

```tex
x_\gamma\in \mathbb N
\qquad\text{or}\qquad
x_\gamma-1\in\mathbb N
```

can occur for the active values of `a`. The shifted lattice
`n+\tfrac12` helps operationally, but the collision issue still has to be
written down and controlled explicitly.

Under the active hypothesis itself, there are also no collisions on the
sampled tail: if `R(m)=0` is a finite value for every `m>N`, then those tail
integers are automatically not poles. After the same translation, the sampled
positive half-integers for `R_N` are likewise pole-free.

So the adaptation picture is now genuinely sharper:

- `A1` is easy;
- `A2a` looks compatible;
- `A2b` is the real new wall;
- `A3` collapses as sampling geometry only;
- `A4` is controlled on the active hypothesis at least on the sampled tail.

There is still one useful lesson from the finer `A2` split. If an eventual
infinite-pole extension is pursued, the remaining analytic work should itself
be split into:

```tex
\textbf{A2c. }L^2\text{ control on the imaginary axis;}
\qquad
\textbf{A2d. weighted }L^2\text{ control for }h(k;z)\text{ if the consistency
branch is used.}
```

For a simple Cauchy transform with `\ell^1` residues, the bare bound
`R(\sigma+iy)=O(|y|^{-1})` is enough for the unweighted `L^2` part, while the
weighted `L^2` control for

```tex
h(k;iy)=\Bigl(iy-k-\frac12\Bigr)R(\sigma+iy)
```

would require one more cancellation moment, namely decay of size
`O(|y|^{-2})`. This is useful only after the finite-vs-infinite pole wall is
honestly addressed; it is not itself a way around `A2b`.

At the current information level, the fastest direct attack is therefore no
longer "verify the admissible class" as a routine check. The honest target is
now:

```tex
\textbf{decide whether the De Micheli--Viano bridge extends from finite-pole
meromorphic functions to our infinite-pole `\ell^1` Cauchy class.}
```

If yes, this becomes a powerful direct receiver. If not, the external
pole-recovery bridge should be removed from the critical path and treated only
as a diagnostic analogy.

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

## D2g16e. First real-support computational radar

This step is not theorem content; it is a reconnaissance check for the new
coefficient barrier `D2g16d`.

Using the script
`q3.lean.aristotle/scripts/d2g16_real_packet_scan.py`,
we sampled actual zeta-zero ordinates `\gamma_n` via `mpmath.zetazero(n)` and
formed the real support
`X_a=\{x_\gamma=a\gamma/\pi\}`.
For each consecutive window of length `L=2,3,4`, we built the local one-sided
Cauchy sample matrix against the nearest right-tail block and computed:

- the smallest singular value `\sigma_{\min}`;
- the corresponding optimal unit coefficient vector;
- its distance to the Hermite/barycentric line of that exact window.

First scan (`n\le 120`) gives the following picture.

- For `a=0.5`, the best windows already align strongly with the Hermite line:
  overlaps are about `0.998` for `L=2`, `0.991--0.994` for `L=3`, and
  `0.987--0.991` for `L=4`.
- For `a=1`, the same phenomenon persists:
  overlaps are about `0.99` for `L=2`, `0.976--0.989` for `L=3`, and
  `0.943--0.983` for `L=4`.
- For `a=2`, the best windows are less dense and have much larger arithmetic
  deviation; the overlaps drop to roughly `0.978--0.982` for `L=2`,
  `0.959--0.981` for `L=3`, and `0.943--0.955` for `L=4`.

This is already a useful signal:

- the numerically best local packets do **not** suggest an alternative
  coefficient law;
- instead, the small-defect windows are pulled toward the Hermite line exactly
  when the support geometry looks closest to a microcluster;
- when the geometry becomes visibly less cluster-like, the Hermite overlap
  deteriorates in the expected direction.

So the current live coefficient barrier sharpens again:

> to defeat `D2g16d`, a genuine packet on `Y_a=\{x_\gamma,x_\gamma-1\}` would
> need not only a one-sided microcluster in `X_a`, but a microcluster whose
> local optimal coefficients remain close to the Hermite line at the same time.

The next step is therefore clear:
push the radar from qualitative overlap to a quantitative theorem-shape, i.e.
prove that in the genuine paired class, small local defect plus microcluster
geometry forces coefficient closeness to `\mathbb C w` with an explicit rate.
