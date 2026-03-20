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
