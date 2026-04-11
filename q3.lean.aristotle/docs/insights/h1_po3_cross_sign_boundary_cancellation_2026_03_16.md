# `PO3` cross-sign boundary cancellation (2026-03-16)

## Status

Direct successor to `P2` in lane `A`.

Operationally closed on 2026-03-18 as the Door-1 boundary gate.
This note remains the source artifact for why the mixed block is now treated as
bulk-exact, boundary-cancelled, and cap-only at worst.

`P2` already froze the right cross-sign posture:

- primary lemma:
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- admissible fallback:
  `\mathcal D_{a,N}^{+-}
   =\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- route-kill:
  any residual outside named boundary/cap channels.

So `P3` is now very sharp:

```tex
\text{kill the cross-sign boundary channel.}
```

## Mandatory research synthesis

The required research pass for this blocker points in one direction rather than
opening a new branch.

1. Local oracle recall again pulls the route back to `Main_closure.tex`: the
   old filtered classifier still records `M^{+-}(a)` as the calibration block
   and explicitly says that no extra section-boundary defect should survive
   once `\widetilde Q_{M,N}` is used correctly.
2. The frozen `h1_four_block_bulk_2026_03_08.md` note says the same thing in
   operator language: filtered bulk is exact first, and section-boundary
   bookkeeping is not allowed to leak back in at the bulk stage.
3. The Day-2 `(+,-)` cancellation ledger already singled out
   `\mathcal D_{a,\partial}^{+-}=0` as the strongest structural guess, with
   cap-only as the only admissible corrected fallback.
4. The worker contract for `P3` therefore should not ask for a new
   classification tree; it should ask for one exact boundary-cancellation lemma
   and one cap-only corollary.
5. External sanity-check material on Toeplitz/Hankel finite sections supports
   exactly this style of theorem packaging: boundary, commutator, and cap
   corrections are natural operator channels, while basis-hunt language is not
   a theorem shape.

So the honest `P3` plan is now:

- attack one exact boundary-cancellation lemma;
- allow only cap-only survival on the `(+,-)` side;
- treat any non-cap cross-sign boundary residue as a route-kill or
  near-route-kill event.

## Refined source map (2026-03-18)

The 2026-03-18 research refresh makes the `P3` support stack more exact.

### 1. `Main_closure.tex` still gives the primary filtered receiver

The main manuscript still points to the same mixed-block calibration story:

- `full/sections/Main_closure.tex` — `eq:H1-filtered-bulk-plus-minus`
- `full/sections/Main_closure.tex` — `prop:H1-raw-entry-reduction`
- `full/sections/Main_closure.tex` — `prop:H1-filtered-q-blocks`
- `full/sections/Main_closure.tex` — `cor:H1-bulk-symmetry-reduction`

Operational reading:

- `(+,-)` is still the filtered calibration block;
- once `\widetilde Q_{M,N}` is used correctly, no extra section-boundary
  defect should survive as theorem content;
- any leftover mixed-block channel therefore has to be cap-only or route-kill.

### 2. The reviewed H1 skeleton confirms the theorem map

`docs/reviewed_notes/2026_03_08_h1_theorem_skeleton_review.md` keeps the same
order:

- raw entry reduction first;
- filtered consequence second;
- finite cap last.

That is exactly the `P2 -> P3 -> cap-only fork` posture, not a return to a
free-floating remainder classifier.

### 3. The old four-block note still survives as consequence-layer support

`docs/insights/h1_four_block_bulk_2026_03_08.md` remains useful in one narrow
sense:

- it still freezes the filtered consequence language for `(+,+)`, `(+,-)`,
  `(-,+)`, `(-,-)`;
- it still says that no extra section-boundary bookkeeping belongs inside the
  filtered mixed block once `\widetilde Q_{M,N}` is the comparison object.

So the old four-block note is not the active frontier, but it still supports
`PO3a`.

### 4. External sanity-check keeps supporting asymmetry, not symmetry

The external foundation stack now reads cleanly:

- paired-operator language supports the special status of the mixed block;
- Toeplitz/Hankel operator language supports same-sign boundary/commutator
  residue as the natural surviving channel;
- nothing in that stack argues for a genuinely new mixed-block boundary term.

So `P3` still points in one direction:

```tex
\mathcal D_{a,\partial}^{+-}=0
\quad\text{or at worst}\quad
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

## Exact target

The primary `PO3` statement should be

```tex
\textbf{PO3a.}\qquad \mathcal D_{a,\partial}^{+-}=0.
```

Equivalent theorem fork:

```tex
\textbf{PO3b.}\qquad \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

Preferred stronger version:

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0,
```

but `PO3` itself should not require that stronger statement.

## Why this is next

Without `PO3`, the cross-sign side still carries a named dynamic correction,
and then the asymmetry of the whole route remains incomplete.

The intended asymmetry is:

- `(+,-)` should collapse to exactness or cap-only;
- `(++)` is the only place where a same-sign boundary operator may survive.

So `PO3` is the gate that stops the same-sign boundary story from leaking into
the calibration block.

## Best existing support

### 1. Day-2 cancellation ledger already said this

The cross-sign cancellation ledger fixed the strong expectation

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So `P3` is not a new speculation. It is the formalization of the strongest
already-frozen asymmetric guess.

### 2. Worker-ingested `P2` sharpened the handoff

The worker report made the handoff explicit:

- `P2` kills bulk;
- `P3` kills boundary;
- leftover, if any, is cap-only.

That is exactly the receiver this note should preserve.

### 3. Numerical story still points the same way

The whole moving-boundary / prefix-holdout pathology concentrates in `(++)`,
not in `(+,-)`.

So any surviving cross-sign boundary term is already suspicious and should be
treated as a near-route-kill, not as a routine weakened theorem.

### 4. Macro place of `P3`

`P3` is not an isolated micro-lemma anymore.
It is the boundary half of Door 1 in the compressed route

```tex
\text{Door 1} \to \text{Door 2} \to \text{Door 3} \to H2^f \to H3^f \to H4^f.
```

That is good news: if `P3` lands, Door 1 is very close to closure, and the
whole route becomes visibly asymmetric in the intended way.

## Proof-facing packet

### PO3.1. Boundary cancellation lemma

The narrowest local theorem target is

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

This should be attacked directly, not through new basis language and not
through finite-section numerics.

### PO3.2. Cap-only corollary

If `PO3.1` lands, then the cross-sign tail block reduces to

```tex
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

This is the correct pre-`PO5` endpoint for the `(+,-)` side.

### PO3.3. Final `(+,-)` theorem fork

After `PO3`, the acceptable `(+,-)` theorem outputs are only:

1. exact cross-sign identity;
2. cap-only corrected cross-sign identity.

Nothing else should survive.

### PO3.4. Symmetry handoff

If `PO3a` lands on `(+,-)`, the `(-,+)` block should not become a new theorem
problem.

The expected handoff is:

```tex
\mathcal D_{a,\partial}^{-+}=0
```

by conjugation / self-adjoint symmetry, so the cross-sign side closes as one
package rather than two unrelated lemmas.

## Reusable lemma list

The reusable `P3` packet is now:

1. `PO3a`:
   ```tex
   \mathcal D_{a,\partial}^{+-}=0.
   ```
2. `PO3b`:
   ```tex
   \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
   ```
3. `PO3c`:
   ```tex
   \mathcal D_{a,\partial}^{-+}=0
   ```
   by symmetry once `PO3a` is in place.

## Route-kill condition

The current reset is effectively dead if `PO3` leaves

```tex
\mathcal D_{a,\partial}^{+-}\neq 0
```

as a genuinely non-cap cross-sign boundary term.

Operationally:

```text
any surviving non-cap cross-sign boundary residue is a route-kill or near-route-kill.
```

The reason for “near-route-kill” wording is just caution about wording
discipline; mathematically the intended route no longer wants such a term.

## What `PO3` must not do

- no same-sign `(++)` theorem work;
- no compression bookkeeping;
- no augmented-cap positivity;
- no weakening back into “some structured cross-sign correction”.

## Handoff after `PO3`

If `PO3` lands, the cross-sign branch is essentially done. The next honest
steps are then:

1. `PO4`: identify the same-sign boundary term `H_a^{\mathrm{ss}}`;
2. `PO5`: separate the finite cap term `C_a^{\mathrm{cap}}`;
3. `PO6`: descend to finite filtered sections with no extra mystery channel.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one exact boundary-cancellation lemma for `\mathcal D_{a,\partial}^{+-}`;
- one cap-only corollary for the final `(+,-)` side.

## Exact proof packet after the 2026-04-11 audit

The audit closes one ambiguity cleanly: the missing brick is not an undefined
"mixed boundary miracle", but one exact boundary-algebra membership lemma.

### Frozen source stack

The minimal stack is now:

1. `full/sections/Main_closure.tex` — `prop:H1-raw-entry-reduction`;
2. `full/sections/Main_closure.tex` — `prop:H1-filtered-q-blocks`;
3. `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` — `L3'`
   explicit filtered residual formula;
4. `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` —
   `L3'''''` sign-pure boundary lemma;
5. `docs/insights/h1_boundary_cap_reset_2026_03_14.md` — the structural split
   `\mathcal D_{a,N}=H_{a,N}+C_{a,N}`.

These are enough to freeze the real theorem receiver.

### Exact receiver

From `PO2` we already have the mixed filtered residual in exact four-term form:

```tex
R_{mn}^{+-}(a)
=
\delta_{m,-n}(a)
+ \delta_{m+1,-n}(a)
+ \delta_{m,-(n+1)}(a)
+ \delta_{m+1,-(n+1)}(a),
```

with `\delta_{r,s}(a)=w_{r,s}(a)-\kappa(a)q_{r,s}`.

So `PO3a` is no longer a vague cancellation wish. It reduces to proving that
the boundary part of the infinite-tail defect is sign-pure.

### Exact missing lemma

The next theorem attempt should now be stated as:

```tex
\textbf{PO3a-formula.}\qquad
H_{a,N}\in\mathcal B,
```

where `\mathcal B` is the boundary algebra generated by
`P_+`, `P_-`, `\Delta_+`, `\Delta_-`, and tail operators acting only on the
positive or only on the negative side.

Then the sign-pure boundary lemma gives immediately

```tex
P_+H_{a,N}P_-=0,
```

hence

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So the actual `PO3a` chain is now frozen as:

```tex
H_{a,N}\in\mathcal B
\Longrightarrow
P_+H_{a,N}P_-=0
\Longrightarrow
\mathcal D_{a,\partial}^{+-}=0
\Longrightarrow
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

### What is still missing mathematically

The current stack does **not** yet prove the membership
`H_{a,N}\in\mathcal B`.

That is the honest live blocker.
In other words:

- we already know what the cancellation mechanism would be;
- we do **not** yet have the explicit mixed-boundary formula that places the
  boundary operator inside the sign-pure algebra.

### Route-kill criterion

The route is no longer killed by "any nonzero mixed residue".
It is killed by the sharper event:

```tex
\text{the explicit boundary formula for }H_{a,N}
\text{ requires a genuine cross-sign generator outside }\mathcal B.
```

Equivalently, if after isolating the boundary layer one is forced to keep a
term with nonzero `P_+(\cdot)P_-` that is not finite cap, then `PO3a` fails in
the intended Door-1 sense.

### Control consequence

The proof-packet audit is therefore complete.
The next honest local task is not another search, but a direct attack on
`PO3a-formula`: derive an explicit formula for `H_{a,N}` and prove that every
boundary generator is sign-pure.

## Proof skeleton for the live `PO3a` attack

The next proof attempt should now be written as a rigid five-step packet rather
than a generic "boundary cancellation" search.

### `PO3a.1` Bulk-boundary decomposition

Construct a decomposition

```tex
S_{a,\infty,N}=U_{a,N}+B_{a,N},
```

where `U_{a,N}` is the bulk piece already matched by
`\kappa(a)\Delta_N^*Q_\infty\Delta_N`, and `B_{a,N}` is the genuine boundary
correction.

The intended identity is

```tex
U_{a,N}^*G_g[a]U_{a,N}
=
\kappa(a)\Delta_N^*Q_\infty\Delta_N.
```

Then

```tex
H_{a,N}
=
B_{a,N}^*G_g[a]B_{a,N}
+ U_{a,N}^*G_g[a]B_{a,N}
+ B_{a,N}^*G_g[a]U_{a,N}.
```

So the boundary layer is generated entirely by the correction `B_{a,N}`.

There is now also one exact algebraic starting identity behind this step.
Define the raw sign-pure synthesis `T_{a,\infty,N}` on the algebraic tail basis
by

```tex
T_{a,\infty,N} z^n=\chi_n[a],
\qquad
T_{a,\infty,N} z^{-n}=\chi_{-n}[a]
\qquad (n>N).
```

Then the already frozen `PO1` / `Main_closure` formulas give on basis vectors

```tex
I_0^{(a)}S_{a,\infty,N} z^n=\chi_n[a]+\chi_{n+1}[a],
\qquad
I_0^{(a)}S_{a,\infty,N} z^{-n}=\chi_{-n}[a]+\chi_{-(n+1)}[a],
```

while

```tex
\Delta_N z^n=z^n+z^{n+1},
\qquad
\Delta_N z^{-n}=z^{-n}+z^{-(n+1)}.
```

So one has the exact tail-level factorization

```tex
I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N.
```

This is the right entry point for `PO3a.1`: the sign geometry is already
clean at the antiderivative level, so any boundary term must appear only when
passing back from the Volterra-antiderivative side to the actual defect
operator. In particular, the live source of `H_{a,N}` is no longer "some
mixed tail combinatorics", but the Volterra undoing of the raw sign-pure
filtered synthesis.

This suggests one exact next candidate formula for the boundary layer.
Let `D_a` denote the derivative on the Volterra domain with left endpoint
basepoint `-a`. Formally one has

```tex
D_a I_0^{(a)} = I,
\qquad
I_0^{(a)} D_a = I - R_a,
\qquad
R_a := \mathbf 1\otimes \operatorname{ev}_{-a}.
```

So the only obstruction to exact inversion is the rank-one endpoint projector
`R_a`. In the current bridge language this means:

```tex
\text{candidate source of }H_{a,N}
\;=\;
\text{endpoint-evaluation defects created when undoing }I_0^{(a)}.
```

This is not yet a proved theorem in the current packet, but it is now the
first honest candidate formula to test in `PO3a.2`.

There is also one exact orthogonality observation behind this candidate.
Because

```tex
\chi_n[a](t)=(2a)^{-1/2}e^{\pi i n t/a},
\qquad
\mathbf 1=\sqrt{2a}\,\chi_0[a],
```

the constant function is orthogonal to every nonzero Fourier mode on `[-a,a]`.
Since the raw tail syntheses `T_{a,\infty,N}^\pm` use only modes `\pm n` with
`n>N\ge 0`, one has exactly

```tex
T_{a,\infty,N}^{+*}\mathbf 1=0,
\qquad
T_{a,\infty,N}^{-*}\mathbf 1=0.
```

So any boundary brick in which the endpoint projector `R_a` lands on the left
raw-synthesis side dies immediately after pulling back to the tail.

This does not finish `PO3a.2`, but it sharpens the local problem:

```tex
\text{the only surviving endpoint bricks can come from the domain-side
evaluation functionals, not from a constant left output.}
```

The domain-side evaluation is also explicit. Since

```tex
\chi_{\pm n}[a](-a)=(2a)^{-1/2}(-1)^n
\qquad (n\ge 1),
```

the endpoint functional on the raw tail synthesis splits exactly as

```tex
\operatorname{ev}_{-a}\circ T_{a,\infty,N}
=
\ell_{+,N}P_+ + \ell_{-,N}P_-,
```

where

```tex
\ell_{+,N}(z^n)=(2a)^{-1/2}(-1)^n,
\qquad
\ell_{-,N}(z^{-n})=(2a)^{-1/2}(-1)^n,
```

and both functionals vanish on the opposite sign subspace.
Hence

```tex
R_a T_{a,\infty,N}
=
\mathbf 1\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)
```

is already sign-split on the domain side.

So the `PO3a.2` boundary-expansion problem narrows further:

```tex
\text{the only possible mixed leakage must come from the left vectors created
after }G_g[a]\text{ acts on the constant output.}
```

This gives one more exact candidate reduction. Set

```tex
v_{a,N}:=T_{a,\infty,N}^*G_g[a]\mathbf 1.
```

Because

```tex
\mathbf 1=\sqrt{2a}\,\chi_0[a],
```

the components of `v_{a,N}` are exactly the zero-mode couplings of the raw
Weil matrix:

```tex
\langle v_{a,N},z^r\rangle
=
\sqrt{2a}\,w_{r,0}(a)
\qquad (|r|>N).
```

Using the frozen raw formula for `w_{rs}(a)` and `\alpha_0=0`, this becomes

```tex
w_{r,0}(a)
=
\frac{2(-1)^r}{a}
\sum_{\gamma\in\Gamma}
\frac{\sin^2(a\gamma)}
{(\gamma+\alpha_r)\gamma}.
```

So `PO3a.3` is now concentrated on one very concrete arithmetic object:
the sign behavior of the zero-mode coupling vector `r\mapsto w_{r,0}(a)`.

There is also one exact symmetry already visible at this level. Since the zero
set of `\xi(1/2-iz)` is symmetric under `\gamma\mapsto-\gamma`, pairing the
terms in

```tex
w_{r,0}(a)
=
\frac{2(-1)^r}{a}
\sum_{\gamma\in\Gamma}
\frac{\sin^2(a\gamma)}
{(\gamma+\alpha_r)\gamma}
```

gives

```tex
w_{r,0}(a)
=
\frac{4(-1)^r}{a}
\sum_{\gamma>0}
\frac{\sin^2(a\gamma)}
{\gamma^2-\alpha_r^2}.
```

Hence

```tex
w_{-r,0}(a)=w_{r,0}(a),
```

so the vector `v_{a,N}` is reflection-even across the positive and negative
tail. This is the first exact structure theorem on the live `PO3a.3` object.

But it is still weaker than the needed sign-purity. Evenness of the left vector
alone does not imply that a rank-one endpoint brick built from
`v_{a,N}` and `\ell_{+,N}P_+ + \ell_{-,N}P_-` lies in the sign-pure boundary
algebra `\mathcal B`; genuine cross-sign pieces can still survive a priori.

Then every first-order endpoint brick generated by
`R_a T_{a,\infty,N}=\mathbf 1\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)`
must be built from the vector `v_{a,N}` on the left and the sign-split
functionals `\ell_{+,N}P_+`, `\ell_{-,N}P_-` on the right, together with the
adjoint companion terms.

So the sharp local `PO3a.3` test becomes:

```tex
\text{is the relevant part of }v_{a,N}
\text{ itself sign-pure (or at least sign-split in a way compatible with }
\ell_{+,N}P_+ + \ell_{-,N}P_- )?
```

This is still not a proof, but it replaces the previous vague boundary cloud by
one concrete vector-level object.

So the exact next local theorem-target is now cleaner than before:

```tex
\text{either prove a stronger one-sided purity/sign law for }
\sum_{\gamma>0}\frac{\sin^2(a\gamma)}{\gamma^2-\alpha_r^2},
\text{ or show that the full first-order endpoint expansion cancels its
cross-sign part after adjoining the adjoint companion terms.}
```

There is also an exact obstruction lemma at this stage. Let

```tex
K_v:=v\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-),
\qquad
v=v_+ + v_-,
\qquad
v_\pm:=P_\pm v.
```

Relative to the decomposition
`\mathcal H_N=\mathcal H_{+,N}\oplus\mathcal H_{-,N}`, the block form is

```tex
K_v=
\begin{pmatrix}
v_+\otimes \ell_{+,N} & v_+\otimes \ell_{-,N} \\
v_-\otimes \ell_{+,N} & v_-\otimes \ell_{-,N}
\end{pmatrix}.
```

Since `\ell_{+,N}` and `\ell_{-,N}` are nonzero, the sign-pure boundary lemma
implies:

```tex
K_v\in\mathcal B
\Longrightarrow
v_+=0
\text{ and }
v_-=0
\Longrightarrow
K_v=0.
```

So a nonzero first-order endpoint brick of the form
`v\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)` can never belong to the sign-pure
boundary algebra by itself.

Combined with the reflection-evenness of `v_{a,N}`, this has a sharp
consequence:

```tex
\text{either }v_{a,N}=0,
\text{ or `PO3a` cannot be closed by a lone first-order endpoint brick;}
```

any surviving route must use exact cancellation with the adjoint companion
terms (or a stronger structural collapse of the full boundary packet).

There is a further finite-section rigidity if one allows exactly that
companion-term cancellation. Fix a finite tail window `N<r\le M`, and let

```tex
u_{+,M,N}
:=
\frac{1}{\sqrt{2a}}\sum_{r=N+1}^{M}(-1)^r e_r^+,
\qquad
u_{-,M,N}
:=
\frac{1}{\sqrt{2a}}\sum_{r=N+1}^{M}(-1)^r e_r^-,
```

so that on the compressed window these are the Riesz vectors of
`\ell_{+,N}P_+` and `\ell_{-,N}P_-`.

If the surviving first-order packet on that window is exactly the symmetric
companion pair

```tex
K_v^{(M)} + (K_v^{(M)})^*,
\qquad
K_v^{(M)}:=P_{M,N}\,v\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)\,P_{M,N},
```

then its mixed block has the form

```tex
P_+\bigl(K_v^{(M)} + (K_v^{(M)})^*\bigr)P_-
=
x_M\otimes u_{-,M,N} + u_{+,M,N}\otimes y_M,
```

where `x_M:=P_+P_{M,N}v` and `y_M:=P_-P_{M,N}v`.

For this sum of two rank-one operators to vanish, linear algebra forces
`x_M` to be proportional to `u_{+,M,N}` and `y_M` to be proportional to
`u_{-,M,N}`. So exact first-order companion cancellation implies:

```tex
x_M \in \mathbb C\,u_{+,M,N},
\qquad
y_M \in \mathbb C\,u_{-,M,N}.
```

Applied to `v=v_{a,N}` and using the reflection-evenness of its coordinates,
this becomes the concrete alternating-tail rigidity condition

```tex
w_{r,0}(a)=c_{a,N,M}(-1)^r
\qquad (N<r\le M),
```

for some scalar `c_{a,N,M}` depending on the window.

Equivalently, the paired zero-sum

```tex
\sum_{\{\gamma,-\gamma\}\subset \Gamma}
\frac{\sin^2(a\gamma)}{\gamma^2-\alpha_r^2}
```

would have to be constant in `r` on every compressed window where such a
first-order cancellation is claimed.

So the next arithmetic wall is now brutally explicit:

```tex
\text{can the zero-mode column }r\mapsto w_{r,0}(a)
\text{ ever become windowwise proportional to }(-1)^r
\text{ on arbitrarily long tails?}
```

At first glance one might try to turn this into a Stieltjes-type monotonicity
argument in the variable `\lambda=\alpha_r^2`. But that would require treating
the paired sum as a positive measure over real `\gamma^2`, and the current raw
formula does **not** justify that: in this project `\gamma` runs over the zeros
of `\xi(1/2-iz)` in the complex plane, not over an a priori positive real set.

So the honest conclusion is sharper and more modest:

```tex
\text{the `\gamma\leftrightarrow-\gamma` pairing gives exact evenness,}
\text{ but not a positive Stieltjes transform.}
```

Hence the Stieltjes/monotonicity route is currently a killed subroute, not an
active theorem. The live arithmetic target remains only the alternating-tail
rigidity itself:

```tex
\text{can the paired quotient sum above really be constant in }r
\text{ on long compressed windows?}
```

There is one more exact consequence once this is read at the operator level
rather than for a single window. If the same first-order companion cancellation
is required on every compression `P_{M,N}` of one fixed infinite-tail defect,
then the window constants must glue.

Indeed, if for every `M>N+1` one has

```tex
w_{r,0}(a)=c_{a,N,M}(-1)^r
\qquad (N<r\le M),
```

then for `M_2>M_1>N+1` the overlap `N<r\le M_1` forces

```tex
c_{a,N,M_2}=c_{a,N,M_1}.
```

So there is a single scalar `c_{a,N}` such that

```tex
w_{r,0}(a)=c_{a,N}(-1)^r
\qquad \forall r>N.
```

But `w_{r,0}(a)` is an off-diagonal raw entry with fixed second index `0`, and
the frozen raw Suzuki packet already records decaying off-diagonal tails. Hence

```tex
w_{r,0}(a)\to 0
\qquad (r\to+\infty),
```

which forces `c_{a,N}=0`. Therefore:

```tex
\text{nontrivial first-order companion cancellation on all compressions }
\Longrightarrow
w_{r,0}(a)=0 \text{ for every } r>N.
```

This is a very sharp route squeeze. It shows that the nonzero alternating-tail
scenario can survive only as a one-window artifact; it cannot support the full
infinite-tail operator identity.

So the surviving first-order route is now reduced to a scalar tail-zero
question for one fixed meromorphic profile. Set

```tex
H_a(z)
:=
\sum_{\gamma\in\Gamma}
\frac{\sin^2(a\gamma)}{\gamma(\gamma+z)}.
```

Then the raw zero-mode column is exactly

```tex
w_{r,0}(a)=\frac{2(-1)^r}{a}H_a(\alpha_r),
\qquad
\alpha_r=\frac{\pi r}{a}.
```

Therefore the operator-level squeeze above gives:

```tex
\text{full first-order companion cancellation}
\Longrightarrow
H_a(\alpha_r)=0
\qquad \forall r>N.
```

So the next exact local theorem-target can be stated as:

```tex
\textbf{Arithmetic-progression uniqueness target.}
```

Can a meromorphic function of the explicit Cauchy type `H_a(z)` vanish on the
entire tail progression

```tex
\alpha_r=\frac{\pi r}{a}
\qquad (r>N)
```

without being identically zero?

This is now the cleanest scalar form of the live first-order `PO3a` wall.

There is also an exact rescaling bridge back to the old `PO2` receiver
language. Set

```tex
\widetilde H_a(w):=H_a\!\left(\frac{\pi}{a}w\right),
\qquad
y_\gamma:=-\frac{a}{\pi}\gamma.
```

Then

```tex
\widetilde H_a(w)
=
\sum_{\gamma\in\Gamma}
\frac{\sin^2(a\gamma)}{\gamma(\gamma+\pi w/a)}
=
\sum_{\gamma\in\Gamma}
\frac{a^2}{\pi^2}\frac{\sin^2(a\gamma)}{y_\gamma(y_\gamma-w)}.
```

So after defining

```tex
e_a(y_\gamma):=\frac{a^2}{\pi^2}\frac{\sin^2(a\gamma)}{y_\gamma},
```

we get the exact simple Cauchy form

```tex
\widetilde H_a(w)=\sum_{\gamma\in\Gamma}\frac{e_a(y_\gamma)}{y_\gamma-w}.
```

And since `\alpha_r=\pi r/a`, the tail-zero condition becomes

```tex
\widetilde H_a(r)=0
\qquad \forall r>N.
```

Therefore the surviving first-order `PO3a` wall is not a brand-new scalar
uniqueness problem after all. It embeds directly into the already isolated
`PO2` hard wall:

```tex
\text{simple Cauchy transform vanishing on the integer tail.}
```

The honest caveat is that the rescaled support

```tex
Y_a:=\left\{-\frac{a}{\pi}\gamma:\gamma\in\Gamma\right\}
```

is a complex zero set, not an a priori one-sided real support. So the old
one-sided rigidity theorem is not enough by itself. But the general
`PO2` Cauchy-tail injectivity target is now the correct consumer for this
first-order `PO3a` reduction.

Moreover, the direct divisor closure from the `PO2` receiver route transfers
verbatim. If `\widetilde H_a(r)=0` for all `r>N`, then for every `k\ge 1`

```tex
\widetilde H_{a,k}(w)
:=
\frac{\widetilde H_a(w)}{\prod_{j=1}^k (w-(N+j))}
```

still has the same simple Cauchy form

```tex
\widetilde H_{a,k}(w)
=
\sum_{\gamma\in\Gamma}
\frac{e_a(y_\gamma)}
{\prod_{j=1}^k (y_\gamma-(N+j))}
\frac{1}{y_\gamma-w},
```

and vanishes on the shifted tail `w>N+k`.

So the first-order `PO3a` wall now inherits the full direct-receiver package:

```tex
\text{simple Cauchy class}
\Longrightarrow
\text{tail-zero divisor closure}
\Longrightarrow
\text{tail injectivity target}.
```

This is a genuine structural gain: the remaining hard part is no longer the
shape of the receiver, only the uniqueness problem for its complex support.

There is one more exact structural gain coming from the same zero symmetry.
Since `\Gamma` is closed under `\gamma\mapsto-\gamma`, the rescaled support
`Y_a` is closed under `y\mapsto-y`. Moreover

```tex
e_a(-y_\gamma)
=
-e_a(y_\gamma),
```

because `\sin^2(a\gamma)` is even while the divisor `y_\gamma` is odd. Hence
the rescaled receiver is actually even in the external variable:

```tex
\widetilde H_a(-w)=\widetilde H_a(w).
```

Choose one representative `\gamma` from each pair `\{\gamma,-\gamma\}` and set

```tex
\lambda_\gamma:=y_\gamma^2.
```

Then pairing the two simple poles gives the exact collapse

```tex
\frac{e_a(y_\gamma)}{y_\gamma-w}
\;+\;
\frac{e_a(-y_\gamma)}{-y_\gamma-w}
=
\frac{2a^2}{\pi^2}\,
\frac{\sin^2(a\gamma)}{\lambda_\gamma-w^2}.
```

So there is a second exact receiver reformulation:

```tex
\widetilde H_a(w)=J_a(w^2),
```

where

```tex
J_a(z)
:=
\frac{2a^2}{\pi^2}
\sum_{\gamma\in\Gamma^\sharp}
\frac{\sin^2(a\gamma)}{\lambda_\gamma-z},
```

and `\Gamma^\sharp` is any transversal of the involution
`\gamma\leftrightarrow-\gamma`.

Therefore the integer-tail vanishing of `\widetilde H_a` is equivalent to a
square-tail vanishing problem:

```tex
J_a(r^2)=0
\qquad \forall r>N.
```

So the live first-order `PO3a` wall is actually narrower than the generic
`PO2` target. It lands in a very special subclass:

```tex
\text{simple Cauchy transform on the squared support }
\Lambda_a:=\{\lambda_\gamma:\gamma\in\Gamma^\sharp\},
```

with zeros on the quadratic tail `\{(N+1)^2,(N+2)^2,\dots\}`.

This is also a genuine density change, not just a cosmetic rewrite. Let

```tex
n_{\Lambda_a}(R):=\#\{\lambda_\gamma\in\Lambda_a:\ |\lambda_\gamma|\le R\}.
```

Since

```tex
\lambda_\gamma=y_\gamma^2=\frac{a^2}{\pi^2}\gamma^2,
```

and the classical zero-counting law gives

```tex
N_\xi(T)\asymp T\log T,
```

one gets

```tex
n_{\Lambda_a}(R)\asymp \sqrt R\,\log R.
```

So the squared support has exponent of convergence `1/2`:

```tex
\sum_{\lambda\in\Lambda_a}\frac{1}{|\lambda|^\sigma}
\begin{cases}
<\infty,& \sigma>\frac12,\\
=\infty,& \sigma=\frac12 \text{ heuristically at the logarithmic threshold.}
\end{cases}
```

This is exactly the same order as the sample set `\{m^2\}`. So the
first-order `PO3a` wall is no longer a dense-support / sparse-sample mismatch
of the old integer-tail type; after squaring, it becomes a density-matched
problem on two order-`1/2` sets.

This squared receiver also inherits its own direct divisor closure. If
`J_a(r^2)=0` for all `r>N`, then for every `k\ge 1`

```tex
J_{a,k}(z)
:=
\frac{J_a(z)}{\prod_{j=1}^k (z-(N+j)^2)}
```

still has the same simple Cauchy form

```tex
J_{a,k}(z)
=
\frac{2a^2}{\pi^2}
\sum_{\gamma\in\Gamma^\sharp}
\frac{\sin^2(a\gamma)}
{\prod_{j=1}^k (\lambda_\gamma-(N+j)^2)}
\frac{1}{\lambda_\gamma-z},
```

and vanishes on the shifted square tail `z>(N+k)^2` along the samples
`z=r^2`.

So the strongest honest receiver now available for the first-order `PO3a`
route is:

```tex
\text{even simple Cauchy class}
\Longrightarrow
\text{quadratic tail-zero divisor closure}
\Longrightarrow
\text{square-tail injectivity target}.
```

The same caveat remains honest: the squared support `\Lambda_a` is still a
complex support, not a one-sided real support. So this does not yet prove
injectivity. But it does cut the live burden further: the first-order route no
longer feeds the full generic `PO2` wall, only its even square-support
subclass.

The quadratic divisor tower also admits an exact static avatar via Newton
divided differences. Let

```tex
s_j:=(N+j)^2,
\qquad
u_k(\lambda):=\frac{1}{\prod_{j=1}^k (\lambda-s_j)}.
```

For the basic Cauchy kernel

```tex
g_\lambda(z):=\frac{1}{\lambda-z},
```

the standard Newton identity on distinct nodes gives

```tex
[g_\lambda; s_1,\dots,s_k]
=
\frac{1}{\prod_{j=1}^k(\lambda-s_j)}
=
u_k(\lambda),
```

where `[\,\cdot\,; s_1,\dots,s_k]` denotes the `(k-1)`-st divided difference.

Therefore the full quadratic divisor tower of `J_a` is encoded by one fixed
static transform:

```tex
[J_a; s_1,\dots,s_k]
=
\frac{2a^2}{\pi^2}
\sum_{\gamma\in\Gamma^\sharp}
\frac{\sin^2(a\gamma)}{\prod_{j=1}^k(\lambda_\gamma-s_j)}
=
\frac{2a^2}{\pi^2}
\sum_{\gamma\in\Gamma^\sharp}\sin^2(a\gamma)\,u_k(\lambda_\gamma).
```

Equivalently, if

```tex
J_{a,k}(z)
:=
\frac{J_a(z)}{\prod_{j=1}^k(z-s_j)},
```

then its residue coefficients are exactly the divided-difference weights
`u_k(\lambda_\gamma)`.

So the square-tail route has acquired the precise analogue of the earlier
forward-difference avatar:

```tex
\text{quadratic tail-zero tower}
\Longleftrightarrow
\text{vanishing of Newton divided differences of one fixed receiver } J_a.
```

In particular, if `J_a(s_j)=0` for every `j\ge 1`, then every initial divided
difference also vanishes:

```tex
[J_a; s_1,\dots,s_k]=0
\qquad \forall k\ge 1.
```

So the remaining uniqueness wall can now be read in two equivalent ways:

1. injectivity from the square-tail values `J_a((N+j)^2)=0`;
2. injectivity from the full vanishing of the initial Newton-profile of `J_a`.

This is not yet a proof, but it replaces the moving quadratic divisor tower by
one fixed nonuniform-grid interpolation object.

The finite-support version of this squared wall is already dead.

```tex
\textbf{Finite-support square-tail injectivity.}
```

Let

```tex
J(z)=\sum_{m=1}^M \frac{b_m}{\lambda_m-z},
```

where the support points `\lambda_1,\dots,\lambda_M` are distinct and avoid
the square nodes `s_j=(N+j)^2`. If

```tex
J(s_j)=0
\qquad (j=1,\dots,M),
```

then `b_1=\cdots=b_M=0`.

Indeed, multiplying by the common denominator gives

```tex
P(z):=\prod_{m=1}^M(\lambda_m-z)\,J(z),
```

which is a polynomial of degree at most `M-1`. The assumptions imply

```tex
P(s_j)=0
\qquad (j=1,\dots,M).
```

Since the `s_j` are distinct, `P` has at least `M` distinct zeros. Therefore
`P\equiv 0`, hence `J\equiv 0`, and taking residues at each `\lambda_m` gives
`b_m=0`.

Equivalently, the square-Cauchy matrix

```tex
C^{\mathrm{sq}}_{jm}:=\frac{1}{\lambda_m-s_j},
\qquad 1\le j,m\le M,
```

is invertible.

So the first-order `PO3a` wall has now been sharpened all the way down to its
genuine infinite-support core:

```tex
\text{even square-support square-tail injectivity}
=
\text{purely infinite-support wall.}
```

There is also a clean entire divider for this squared sample set. Since

```tex
\frac{\sin(\pi\sqrt z)}{\pi\sqrt z}
=
\prod_{m=1}^\infty \left(1-\frac{z}{m^2}\right),
```

the tail-zero set `\{(N+1)^2,(N+2)^2,\dots\}` admits the exact entire factor

```tex
E_N^{\mathrm{sq}}(z)
:=
\prod_{m=N+1}^\infty \left(1-\frac{z}{m^2}\right)
=
\frac{\sin(\pi\sqrt z)}{\pi\sqrt z}
\prod_{m=1}^N \left(1-\frac{z}{m^2}\right)^{-1}.
```

Therefore, whenever `J_a(r^2)=0` for all `r>N`, the quotient

```tex
U_a(z):=\frac{J_a(z)}{E_N^{\mathrm{sq}}(z)}
```

is again meromorphic with the same pole support `\Lambda_a`.

So the first-order `PO3a` wall has not only a quadratic divisor tower but also
an exact whole-tail factorization by a canonical square-lattice entire
function. This does not yet give injectivity, but it sharpens the analytic
shape of the remaining problem: the unresolved uniqueness theorem is now for a
complex-support simple Cauchy transform after removal of a low-density
order-`1/2` square-tail divisor, rather than after removal of the denser
integer-tail Gamma divisor.

### `PO3a.2` Boundary expansion

Expand the boundary correction in finite sign-pure form:

```tex
B_{a,N}
=
\sum_r |b_{r,+}\rangle\langle \eta_{r,+}|
+ \sum_s |b_{s,-}\rangle\langle \eta_{s,-}|,
```

with every `b_{r,+}` supported in the positive tail channel and every
`b_{s,-}` supported in the negative tail channel.

This is the first genuinely nontrivial local brick: the route needs an
explicit boundary expansion, not merely the abstract split
`\mathcal D_{a,N}=H_{a,N}+C_{a,N}`.

The most plausible current explicit form is therefore:

```tex
H_{a,N}
\in
\operatorname{alg}
\bigl(
P_+,\,
P_-,\,
T_{a,\infty,N}^+,\,
T_{a,\infty,N}^-,\,
R_a,\,
R_a^*
\bigr),
```

where `T_{a,\infty,N}^\pm` are the positive/negative raw syntheses and
`R_a=\mathbf 1\otimes \operatorname{ev}_{-a}` is the endpoint projector coming
from the Volterra undoing defect.

So the sharp local test for `PO3a.2` is no longer "find any boundary
expansion", but the narrower question:

```tex
\text{does every surviving endpoint-evaluation brick remain sign-pure after the }
P_+ / P_- \text{ split?}
```

### `PO3a.3` Kernel sign-preservation on boundary generators

Show that the kernel action preserves the sign purity of the boundary
generators:

```tex
G_g[a]\,b_{r,+}\in \mathcal G_+,
\qquad
G_g[a]\,b_{s,-}\in \mathcal G_-,
```

for the corresponding sign-pure generator families `\mathcal G_\pm`.

This is the real cancellation mechanism behind `PO3a`: once the surviving
boundary generators never cross signs, the mixed block cannot be produced by
the boundary layer.

### `PO3a.4` Boundary algebra membership

From `PO3a.2` and `PO3a.3`, conclude

```tex
H_{a,N}\in\mathcal B.
```

This is the exact missing lemma frozen above as `PO3a-formula`.

### `PO3a.5` Mixed block dies

Apply the sign-pure boundary lemma:

```tex
P_+H_{a,N}P_-=0.
```

Hence

```tex
\mathcal D_{a,\partial}^{+-}=0,
```

and therefore

```tex
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

## Honest difficulty map

The route is now narrow enough that the difficulty split should be frozen
explicitly:

- `PO3a.5` is already formal once `H_{a,N}\in\mathcal B` is available;
- `PO3a.4` is a closure step, not the real obstacle;
- the genuine hard bricks are `PO3a.2` and `PO3a.3`:
  explicit boundary expansion and sign-preservation on the surviving boundary
  generators.

So the next local attack should focus there, not on the final mixed-block
implication.
