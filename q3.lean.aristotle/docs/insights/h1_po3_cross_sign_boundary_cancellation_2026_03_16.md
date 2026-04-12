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

### Exact filtered pullback of the raw defect

There is now also one exact algebraic rewriting of the filtered defect itself.

Let the two-sided raw tail basis be written as

```tex
e_r:=z^r,
\qquad
|r|>N,
```

and define the raw defect coefficients by

```tex
\delta_{r,s}(a):=w_{r,s}(a)-\kappa(a)q_{r,s}.
```

Let `\mathcal R_{a,N}^{\mathrm{raw}}` be the operator (or sesquilinear form)
on the raw tail model space with matrix entries

```tex
\langle \mathcal R_{a,N}^{\mathrm{raw}}e_s,e_r\rangle
:=
\delta_{r,s}(a).
```

Write the two-sided filtered shift on the raw tail basis as

```tex
\Delta_N e_r
=
e_r+e_{r+\operatorname{sgn}(r)},
\qquad
|r|>N,
```

so that on positive and negative modes this is exactly the old rules

```tex
\Delta_N z^n=z^n+z^{n+1},
\qquad
\Delta_N z^{-n}=z^{-n}+z^{-(n+1)}.
```

Then the filtered tail defect is exactly the filtered pullback of the raw
defect:

```tex
\boxed{
\mathcal D_{a,N}
=
\Delta_N^*\,\mathcal R_{a,N}^{\mathrm{raw}}\,\Delta_N.
}
```

Equivalently, for every sign pair `\sigma,\tau\in\{+,-\}` and every `m,n>N`,

```tex
\bigl\langle \mathcal D_{a,N}e_{\varepsilon_\tau n},
e_{\varepsilon_\sigma m}\bigr\rangle
=
\bigl\langle
\mathcal R_{a,N}^{\mathrm{raw}}\Delta_N e_{\varepsilon_\tau n},
\Delta_N e_{\varepsilon_\sigma m}
\bigr\rangle,
```

which expands exactly to the four-term stencil already frozen in `PO2`.

#### Proof

For the mixed block, this is exactly `L3'` from `PO2`:

```tex
R_{mn}^{+-}(a)
=
\delta_{m,-n}(a)
+ \delta_{m+1,-n}(a)
+ \delta_{m,-(n+1)}(a)
+ \delta_{m+1,-(n+1)}(a).
```

But

```tex
\Delta_N e_m=e_m+e_{m+1},
\qquad
\Delta_N e_{-n}=e_{-n}+e_{-(n+1)},
```

so by the definition of `\mathcal R_{a,N}^{\mathrm{raw}}`,

```tex
\bigl\langle
\mathcal R_{a,N}^{\mathrm{raw}}\Delta_N e_{-n},
\Delta_N e_m
\bigr\rangle
```

expands to the same four displayed terms. The same argument works for every
sign pair, because both `\textup{prop:H1-raw-entry-reduction}` and
`\textup{prop:H1-filtered-q-blocks}` were stated for all
`\sigma,\tau\in\{+,-\}`. Hence every filtered block of `\mathcal D_{a,N}` is
obtained from the corresponding block of `\mathcal R_{a,N}^{\mathrm{raw}}` by
the same two-sided stencil, which is exactly the operator identity

```tex
\mathcal D_{a,N}=\Delta_N^*\,\mathcal R_{a,N}^{\mathrm{raw}}\,\Delta_N.
```
∎

### Concrete meaning of the difference

This removes one layer of fog completely.

For every sign pair `\sigma,\tau\in\{+,-\}` and every `m,n>N`, the filtered
Suzuki entry and the filtered model entry are both produced by the same
two-sided four-term stencil:

```tex
M_{mn}^{\sigma\tau}(a)
=
\sum_{\epsilon_1,\epsilon_2\in\{0,1\}}
w_{\varepsilon_\sigma(m+\epsilon_1),\,\varepsilon_\tau(n+\epsilon_2)}(a),
```

```tex
\kappa(a)\,\widetilde q_{mn}^{\sigma\tau}
=
\sum_{\epsilon_1,\epsilon_2\in\{0,1\}}
\kappa(a)\,q_{\varepsilon_\sigma(m+\epsilon_1),\,\varepsilon_\tau(n+\epsilon_2)}.
```

Subtracting gives

```tex
\bigl(\mathcal D_{a,N}\bigr)_{mn}^{\sigma\tau}
=
\sum_{\epsilon_1,\epsilon_2\in\{0,1\}}
\delta_{\varepsilon_\sigma(m+\epsilon_1),\,\varepsilon_\tau(n+\epsilon_2)}(a),
```

with no extra correction term and no hidden second mechanism. In other words:

```tex
\text{first subtract raw coefficients, then apply the common filter.}
```

So the real lower-shell task is not to guess the filtered defect directly. It
is to split the raw defect

```tex
\mathcal R_{a,N}^{\mathrm{raw}}
=
\mathcal R_{a,N}^{\mathrm{bulk}}
\,+\,
\mathcal R_{a,N}^{\partial}
\,+\,
\mathcal R_{a,N}^{\mathrm{cap}},
```

and then pull that split through `\Delta_N`.

This is exactly where the finite row/column machinery becomes relevant. If the
raw boundary part `\mathcal R_{a,N}^{\partial}` is supported on finitely many
rows and columns, then `\Delta_N^*\mathcal R_{a,N}^{\partial}\Delta_N` is still
a finite row/column boundary operator, because left and right multiplication by
the one-step tail filter only enlarges the support by one adjacent index.

Therefore the corrected-column reduction and the compressed receiver packet
apply after the pullback:

```tex
\text{raw boundary defect with finite row/column support}
\Longrightarrow
\text{filtered boundary defect with a finite mixing matrix}.
```

So the concrete `PO3a` burden is now fully explicit:

1. identify the raw coefficient difference `\delta_{r,s}(a)`;
2. show that, after removing the bulk and cap channels, the remaining raw
   defect has finite row/column support or an equivalent endpoint-word form;
3. feed that finite boundary operator into the corrected-column reduction, and
   then into the finite mixing matrix `A+B+M`.

### Finite raw support survives the filter

The previous paragraph can be sharpened into one exact transport lemma.

Let

```tex
I_N:=\{r\in\mathbb Z:\ |r|>N\}
```

be the two-sided tail index set, and let

```tex
\mathcal B_{a,N}^{\mathrm{raw}}
```

be any operator on the raw tail basis `\{e_r:r\in I_N\}` with matrix entries
`b_{r,s}`. Assume there exist finite sets

```tex
R,\ C\subset I_N
```

such that

```tex
b_{r,s}=0
\qquad
\text{whenever } r\notin R \text{ and } s\notin C.
```

Define the one-step thickening of these sets by

```tex
R^\sharp
:=
R
\cup
\{r\in I_N:\ r+\operatorname{sgn}(r)\in R\},
```

```tex
C^\sharp
:=
C
\cup
\{s\in I_N:\ s+\operatorname{sgn}(s)\in C\}.
```

Then the filtered pullback

```tex
\mathcal B_{a,N}^{\mathrm f}
:=
\Delta_N^*\,\mathcal B_{a,N}^{\mathrm{raw}}\,\Delta_N
```

again has finite row/column support:

```tex
\boxed{
\langle \mathcal B_{a,N}^{\mathrm f}e_s,e_r\rangle=0
\quad
\text{whenever } r\notin R^\sharp \text{ and } s\notin C^\sharp.
}
```

#### Proof

For every `r,s\in I_N`,

```tex
\Delta_N e_r=e_r+e_{r+\operatorname{sgn}(r)},
\qquad
\Delta_N e_s=e_s+e_{s+\operatorname{sgn}(s)}.
```

So the filtered matrix entry is

```tex
\bigl\langle \mathcal B_{a,N}^{\mathrm f}e_s,e_r\bigr\rangle
=
\sum_{\epsilon_1,\epsilon_2\in\{0,1\}}
b_{\,r+\epsilon_1\operatorname{sgn}(r),\,
   s+\epsilon_2\operatorname{sgn}(s)}.
```

If this sum is nonzero, then at least one summand is nonzero. By the support
hypothesis on `\mathcal B_{a,N}^{\mathrm{raw}}`, that nonzero summand forces

```tex
r+\epsilon_1\operatorname{sgn}(r)\in R
\qquad\text{or}\qquad
s+\epsilon_2\operatorname{sgn}(s)\in C.
```

If `\epsilon_1=0`, then `r\in R\subset R^\sharp`. If `\epsilon_1=1`, then
`r+\operatorname{sgn}(r)\in R`, hence `r\in R^\sharp` by definition. The same
argument on the column index gives `s\in C^\sharp`.

Therefore a nonzero filtered entry can occur only when

```tex
r\in R^\sharp
\qquad\text{or}\qquad
s\in C^\sharp,
```

which is exactly the claimed row/column support statement. ∎

### Immediate consequence for `PO3a`

Apply the lemma to the raw boundary part

```tex
\mathcal R_{a,N}^{\partial}
```

in the decomposition

```tex
\mathcal R_{a,N}^{\mathrm{raw}}
=
\mathcal R_{a,N}^{\mathrm{bulk}}
\,+\,
\mathcal R_{a,N}^{\partial}
\,+\,
\mathcal R_{a,N}^{\mathrm{cap}}.
```

If `\mathcal R_{a,N}^{\partial}` has finite row/column support, then the
filtered boundary operator

```tex
H_{a,N}
:=
\Delta_N^*\,\mathcal R_{a,N}^{\partial}\,\Delta_N
```

also has finite row/column support. So the corrected-column reduction applies
directly to `H_{a,N}`, and the mixed block of `H_{a,N}` is forced into the
finite cancellation frame

```tex
P_+H_{a,N}P_-
=
E_+\,(A+B+M)\,E_-^*.
```

Hence the raw-support problem and the finite mixing problem are now genuinely
the same step:

```tex
\text{raw finite row/column support}
\Longrightarrow
\text{filtered finite mixing matrix}.
```

So the honest `PO3a` burden can be read one step lower:

```tex
\text{describe the raw defect }\mathcal R_{a,N}^{\mathrm{raw}}
\text{, then pull it through }\Delta_N.
```

In particular, if the raw defect already splits into bulk, boundary, and cap
channels in a class that is stable under left/right multiplication by the
one-sided filtered shifts `\Delta_+,\Delta_-`, then the filtered defect
inherits the same split automatically.

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

## `PO3a-core` — exact mixed-block expansion

There is now a sharper abstract theorem packet sitting strictly between the
sign-pure slogan

```tex
H_{a,N}\in \mathcal B
```

and the concrete zero-mode / square-tail reductions below. It does not prove
`PO3a` by itself, but it shows exactly which coefficients must be killed once a
finite sign-split boundary expansion is available.

### Abstract setup

Let

```tex
\mathcal H=\mathcal H_+\oplus \mathcal H_-,
\qquad
P_+,P_-
```

be the orthogonal sign projectors, let `G=G^*` be bounded and self-adjoint,
and write

```tex
S=U+B.
```

Assume the bulk is already matched:

```tex
U^*GU=\kappa\,\Delta^*Q\Delta.
```

Define the boundary defect

```tex
H:=S^*GS-\kappa\,\Delta^*Q\Delta.
```

Assume also that the boundary correction has a finite sign-split rank-one
expansion

```tex
B=
\sum_{\sigma\in\{+,-\}}\sum_{r=1}^{R_\sigma}
|b_{r,\sigma}\rangle\langle \eta_{r,\sigma}|,
\qquad
\eta_{r,\sigma}\in\mathcal H_\sigma.
```

### Theorem `PO3a-core`

Under the setup above,

```tex
\boxed{
P_+HP_-
=
\sum_{r=1}^{R_-}
|P_+U^*Gb_{r,-}\rangle\langle \eta_{r,-}|
\;+\;
\sum_{r=1}^{R_+}
|\eta_{r,+}\rangle\langle P_-U^*Gb_{r,+}|
\;+\;
\sum_{r=1}^{R_+}\sum_{s=1}^{R_-}
\langle b_{r,+},Gb_{s,-}\rangle
|\eta_{r,+}\rangle\langle \eta_{s,-}|.
}
```

#### Proof

Expand

```tex
S^*GS
=
U^*GU+U^*GB+B^*GU+B^*GB.
```

Since `U^*GU=\kappa\,\Delta^*Q\Delta`, one has

```tex
H=U^*GB+B^*GU+B^*GB,
```

hence

```tex
P_+HP_-
=
P_+U^*GBP_-+P_+B^*GUP_-+P_+B^*GBP_-.
```

For the first term,

```tex
U^*GB
=
\sum_{\sigma,r}|U^*Gb_{r,\sigma}\rangle\langle \eta_{r,\sigma}|,
```

so

```tex
P_+U^*GBP_-
=
\sum_{\sigma,r}|P_+U^*Gb_{r,\sigma}\rangle\langle P_-\eta_{r,\sigma}|.
```

Because `\eta_{r,+}\in\mathcal H_+` and `\eta_{r,-}\in\mathcal H_-`, only
`\sigma=-` survives:

```tex
P_+U^*GBP_-
=
\sum_{r=1}^{R_-}|P_+U^*Gb_{r,-}\rangle\langle \eta_{r,-}|.
```

For the second term,

```tex
B^*
=
\sum_{\sigma,r}|\eta_{r,\sigma}\rangle\langle b_{r,\sigma}|,
```

so

```tex
P_+B^*GUP_-
=
\sum_{\sigma,r}|P_+\eta_{r,\sigma}\rangle\langle b_{r,\sigma},GUP_-\cdot\rangle.
```

Again only `\sigma=+` survives, and self-adjointness of `G` gives

```tex
\langle b_{r,+},GUP_-\cdot\rangle
=
\langle P_-U^*Gb_{r,+},\cdot\rangle.
```

Hence

```tex
P_+B^*GUP_-
=
\sum_{r=1}^{R_+}
|\eta_{r,+}\rangle\langle P_-U^*Gb_{r,+}|.
```

For the third term,

```tex
B^*GB
=
\sum_{\sigma,\tau}\sum_{r,s}
\langle b_{r,\sigma},Gb_{s,\tau}\rangle
|\eta_{r,\sigma}\rangle\langle \eta_{s,\tau}|,
```

so after projecting by `P_+` on the left and `P_-` on the right only the
`\sigma=+,\tau=-` block remains:

```tex
P_+B^*GBP_-
=
\sum_{r=1}^{R_+}\sum_{s=1}^{R_-}
\langle b_{r,+},Gb_{s,-}\rangle
|\eta_{r,+}\rangle\langle \eta_{s,-}|.
```

Summing the three displayed identities yields the formula. ∎

### Corollary `PO3a-kill`

If

```tex
P_+U^*Gb_{r,-}=0
\qquad \forall r,
```

```tex
P_-U^*Gb_{r,+}=0
\qquad \forall r,
```

and

```tex
\langle b_{r,+},Gb_{s,-}\rangle=0
\qquad \forall r,s,
```

then

```tex
P_+HP_-=0.
```

So `PO3a` is reduced to killing exactly three families of cross-sign
coefficients:

1. bulk leakage from minus-boundary generators into `\mathcal H_+`;
2. bulk leakage from plus-boundary generators into `\mathcal H_-`;
3. pure boundary-to-boundary cross-sign pairings.

This is stronger operationally than the raw slogan `H_{a,N}\in\mathcal B`.
Once the explicit boundary expansion is available, `PO3a` is no longer an
abstract algebra-membership problem but a concrete vanishing problem for these
three coefficient families.

### Theorem `PO3a-finite reduction`

There is a further exact sharpening: once the boundary channels themselves are
known to live in finite-dimensional cap spaces, the mixed-block vanishing
reduces to one finite matrix identity.

Assume the sign-split families

```tex
\{\eta_{r,+}\}_{r=1}^{R_+}\subset\mathcal H_+,
\qquad
\{\eta_{s,-}\}_{s=1}^{R_-}\subset\mathcal H_-
```

are linearly independent, and define the finite boundary-cap spaces

```tex
E_+:=\operatorname{span}\{\eta_{r,+}\},
\qquad
E_-:=\operatorname{span}\{\eta_{s,-}\}.
```

Let `Q_\pm` be the orthogonal projectors onto `E_\pm`, and choose dual systems

```tex
\{\eta_{r,+}^\vee\}\subset E_+,
\qquad
\{\eta_{s,-}^\vee\}\subset E_-,
```

with

```tex
\langle \eta_{r,+}^\vee,\eta_{r',+}\rangle=\delta_{rr'},
\qquad
\langle \eta_{s',-},\eta_{s,-}^\vee\rangle=\delta_{s's}.
```

Now define the two bulk-to-boundary leakage families

```tex
u_s^-:=P_+U^*Gb_{s,-}\in\mathcal H_+,
\qquad
v_r^+:=P_-U^*Gb_{r,+}\in\mathcal H_-,
```

and the cross-sign boundary matrix

```tex
M_{rs}:=\langle b_{r,+},Gb_{s,-}\rangle.
```

Then:

1. if `P_+HP_-=0`, automatically

```tex
u_s^-\in E_+ \quad \forall s,
\qquad
v_r^+\in E_- \quad \forall r;
```

2. conversely, once these leakage vectors are known to lie in the cap spaces,
   the condition `P_+HP_-=0` is equivalent to the finite matrix identity

```tex
\boxed{
A+B+M=0,
}
```

where

```tex
A_{rs}:=\langle \eta_{r,+}^\vee,u_s^-\rangle,
\qquad
B_{rs}:=\langle v_r^+,\eta_{s,-}^\vee\rangle,
\qquad
M_{rs}:=\langle b_{r,+},Gb_{s,-}\rangle.
```

#### Proof

Write

```tex
P_+HP_-=X+Y+Z,
```

with

```tex
X:=\sum_s |u_s^-\rangle\langle \eta_{s,-}|,
\qquad
Y:=\sum_r |\eta_{r,+}\rangle\langle v_r^+|,
\qquad
Z:=\sum_{r,s}M_{rs}|\eta_{r,+}\rangle\langle \eta_{s,-}|.
```

If `P_+HP_-=0`, then applying `(I-Q_+)` on the left and `Q_-` on the right
kills `Y` and `Z`, leaving

```tex
\sum_s |(I-Q_+)u_s^-\rangle\langle \eta_{s,-}|=0.
```

Linear independence of `\{\eta_{s,-}\}` gives `(I-Q_+)u_s^-=0`, hence
`u_s^-\in E_+`. The same argument with `Q_+` on the left and `(I-Q_-)` on the
right gives `v_r^+\in E_-`.

Now assume `u_s^-\in E_+` and `v_r^+\in E_-`. Expanding in the dual bases gives

```tex
u_s^-=\sum_r A_{rs}\eta_{r,+},
\qquad
v_r^+=\sum_s B_{rs}\eta_{s,-}.
```

So

```tex
X=\sum_{r,s}A_{rs}|\eta_{r,+}\rangle\langle \eta_{s,-}|,
\qquad
Y=\sum_{r,s}B_{rs}|\eta_{r,+}\rangle\langle \eta_{s,-}|,
\qquad
Z=\sum_{r,s}M_{rs}|\eta_{r,+}\rangle\langle \eta_{s,-}|.
```

Therefore

```tex
P_+HP_-=
\sum_{r,s}(A_{rs}+B_{rs}+M_{rs})|\eta_{r,+}\rangle\langle \eta_{s,-}|.
```

Because the rank-one bricks `|\eta_{r,+}\rangle\langle \eta_{s,-}|` are
linearly independent, this vanishes exactly when `A+B+M=0`. ∎

So `PO3a` has now been reduced one step further:

```tex
\text{first force the leakage vectors into the finite cap spaces;}
\qquad
\text{then solve one finite matrix cancellation problem }A+B+M=0.
```

### Theorem `PO3a-row-column reduction`

There is also a more concrete special case that turns the abstract finite-rank
packet into an explicit algorithm on boundary rows and columns.

Fix a basis `\{e_\nu\}_{\nu\in I}` adapted to the sign splitting

```tex
\mathcal H=\mathcal H_+\oplus\mathcal H_-,
```

meaning every basis vector already lies in one sign sector. Assume the boundary
correction matrix `B=(B_{\mu\nu})` has finite row/column support: there exist
finite sets `R,C\subset I` such that

```tex
B_{\mu\nu}=0
\qquad
\text{whenever }\mu\notin R\text{ and }\nu\notin C.
```

For each `r\in R`, define the row functional

```tex
\rho_r:=\sum_{\nu\in I}\overline{B_{r\nu}}\,e_\nu,
```

so that `\langle \rho_r,x\rangle=\sum_\nu B_{r\nu}x_\nu`. For each `c\in C`,
define the column vector

```tex
\kappa_c:=Be_c=\sum_{\mu\in I}B_{\mu c}e_\mu.
```

Then `B` has the exact finite decomposition

```tex
\boxed{
B=
\sum_{r\in R}|e_r\rangle\langle \rho_r|
\;+\;
\sum_{c\in C}|\kappa_c\rangle\langle e_c|
\;-\;
\sum_{r\in R}\sum_{c\in C}B_{rc}|e_r\rangle\langle e_c|.
}
```

#### Proof

Compare matrix coefficients in the basis `\{e_\nu\}`. The first sum contributes

```tex
\langle e_\mu,|e_r\rangle\langle \rho_r|e_\nu\rangle
=
\delta_{\mu r}B_{r\nu},
```

hence `\mathbf 1_{\mu\in R}B_{\mu\nu}` after summing over `r`. The second sum
contributes

```tex
\langle e_\mu,|\kappa_c\rangle\langle e_c|e_\nu\rangle
=
B_{\mu c}\delta_{c\nu},
```

hence `\mathbf 1_{\nu\in C}B_{\mu\nu}` after summing over `c`. The double sum
subtracts exactly `\mathbf 1_{\mu\in R,\nu\in C}B_{\mu\nu}`. So the total
coefficient is

```tex
\mathbf 1_{\mu\in R}B_{\mu\nu}
+
\mathbf 1_{\nu\in C}B_{\mu\nu}
-
\mathbf 1_{\mu\in R,\nu\in C}B_{\mu\nu},
```

which equals `B_{\mu\nu}` in all four cases
`(\mu\in R/\notin R,\ \nu\in C/\notin C)`. ∎

Now split the row and column vectors by sign:

```tex
\rho_r=\rho_r^++\rho_r^-,
\qquad
\kappa_c=\kappa_c^++\kappa_c^-,
```

with `\rho_r^\pm=P_\pm\rho_r` and `\kappa_c^\pm=P_\pm\kappa_c`. Because the
basis is sign-adapted, each `e_r,e_c` also carries a fixed sign. Hence every
rank-one brick in the decomposition of `B` can be rewritten as one of finitely
many sign-split generators

```tex
|e_r\rangle\langle \rho_r^\sigma|,
\qquad
|\kappa_c^\sigma\rangle\langle e_c|,
\qquad
|e_r\rangle\langle e_c|.
```

So in the finite row/column regime, `PO3a` becomes completely constructive:

1. extract the finite sets `R,C`;
2. form the row data `\rho_r` and column data `\kappa_c`;
3. split them by sign;
4. feed the resulting finite generator list into `PO3a-finite reduction`;
5. compute the finite mixed matrix `A+B+M`.

This is the strongest currently available “operator-to-finite-matrix”
translation for `PO3a`: once the boundary layer is known to live on finitely
many rows and columns, the mixed-block question is literally a finite linear
algebra problem.

### Theorem `PO3a-corrected-column reduction`

There is also a cleaner equivalent version of the row/column packet in which
the overlap subtraction is absorbed directly into corrected column vectors.

Keep the same sign-adapted basis `\{e_\nu\}_{\nu\in I}` and the same finite
row/column support assumption:

```tex
B_{\mu\nu}=0
\qquad
\text{whenever }\mu\notin R\text{ and }\nu\notin C.
```

Define the row bras by

```tex
\langle \rho_r|
:=
\sum_{\nu\in I} B_{r\nu}\,\langle e_\nu|,
\qquad r\in R,
```

and define the corrected column kets by

```tex
|d_c\rangle
:=
B|e_c\rangle
-\sum_{r\in R} B_{rc}|e_r\rangle,
\qquad c\in C.
```

Then

```tex
\boxed{
B
=
\sum_{r\in R}|e_r\rangle\langle \rho_r|
\;+\;
\sum_{c\in C}|d_c\rangle\langle e_c|.
}
```

#### Proof

Compute the `(\mu,\nu)` matrix coefficient of the first sum:

```tex
\left\langle e_\mu,
\sum_{r\in R}|e_r\rangle\langle \rho_r|,
e_\nu\right\rangle
=
\mathbf 1_{\mu\in R} B_{\mu\nu}.
```

For the second sum,

```tex
\left\langle e_\mu,
\sum_{c\in C}|d_c\rangle\langle e_c|,
e_\nu\right\rangle
=
\mathbf 1_{\nu\in C}\langle e_\mu,d_\nu\rangle.
```

But by definition of `d_\nu`,

```tex
\langle e_\mu,d_\nu\rangle
=
B_{\mu\nu}-\mathbf 1_{\mu\in R}B_{\mu\nu}.
```

So the total coefficient is

```tex
\mathbf 1_{\mu\in R}B_{\mu\nu}
+
\mathbf 1_{\nu\in C}
\bigl(B_{\mu\nu}-\mathbf 1_{\mu\in R}B_{\mu\nu}\bigr).
```

If `\mu\in R`, this is `B_{\mu\nu}`. If `\mu\notin R` and `\nu\in C`, this is
again `B_{\mu\nu}`. If `\mu\notin R` and `\nu\notin C`, it is `0`, and the
support assumption gives `B_{\mu\nu}=0`. Hence the decomposition is exact. ∎

Now split the row data by sign:

```tex
\langle \rho_r|
=
\langle \rho_r^+|+\langle \rho_r^-|,
\qquad
\langle \rho_r^\sigma|:=\langle \rho_r|P_\sigma.
```

Because the basis is sign-adapted, every `e_c` already has a fixed sign
`\tau(c)\in\{+,-\}`. So the corrected-column decomposition produces a finite
sign-pure generator list with right vectors drawn from

```tex
\{\rho_r^+\}_{r\in R},
\qquad
\{\rho_r^-\}_{r\in R},
\qquad
\{e_c\in\mathcal H_+\}_{c\in C},
\qquad
\{e_c\in\mathcal H_-\}_{c\in C}.
```

Choosing bases `\eta_{1,+},\dots,\eta_{m_+,+}` of the plus span and
`\eta_{1,-},\dots,\eta_{m_-,-}` of the minus span, every right vector in the
decomposition expands in one of these two bases. Absorbing the coefficients
into the left vectors gives

```tex
B
=
\sum_{r=1}^{m_+}|b_{r,+}\rangle\langle \eta_{r,+}|
\;+\;
\sum_{s=1}^{m_-}|b_{s,-}\rangle\langle \eta_{s,-}|.
```

So the mixed block again reduces to one finite matrix identity `A+B+M=0` as in
`PO3a-finite reduction`.

Operationally this is the cleanest receiver for actual calculations:

1. extract the finite row set `R` and column set `C`;
2. form the row bras `\rho_r`;
3. form the corrected columns `d_c`;
4. compress the right vectors into sign-pure bases
   `\{\eta_{r,+}\}`, `\{\eta_{s,-}\}`;
5. compute the leakage matrices `A,B` and the cross-pairing matrix `M`;
6. check `A+B+M=0`.

### Theorem `PO3a-compressed matrix receiver`

The corrected-column packet can be compressed one step further into a literal
finite matrix receiver.

Keep the setup of `PO3a-corrected-column reduction`. Form the finite plus and
minus raw right-generator lists:

```tex
\{g_1^+,\dots,g_{n_+}^+\}
:=
\{\rho_r^+:r\in R,\ \rho_r^+\neq 0\}
\cup
\{e_c:c\in C,\ e_c\in\mathcal H_+\},
```

```tex
\{g_1^-,\dots,g_{n_-}^-\}
:=
\{\rho_r^-:r\in R,\ \rho_r^-\neq 0\}
\cup
\{e_c:c\in C,\ e_c\in\mathcal H_-\}.
```

Attach to each raw right generator its raw left partner:

- if `g_m^+=\rho_r^+`, set `\lambda_m^+:=e_r`;
- if `g_m^+=e_c`, set `\lambda_m^+:=d_c`;
- if `g_n^-=\rho_r^-`, set `\lambda_n^-:=e_r`;
- if `g_n^-=e_c`, set `\lambda_n^-:=d_c`.

Then

```tex
B
=
\sum_{m=1}^{n_+}|\lambda_m^+\rangle\langle g_m^+|
\;+\;
\sum_{n=1}^{n_-}|\lambda_n^-\rangle\langle g_n^-|.
```

Now let

```tex
E_+:=\operatorname{span}\{g_m^+\},
\qquad
E_-:=\operatorname{span}\{g_n^-\},
```

and choose orthonormal bases

```tex
\eta_1^+,\dots,\eta_{m_+}^+ \text{ of }E_+,
\qquad
\eta_1^-,\dots,\eta_{m_-}^- \text{ of }E_-.
```

Write

```tex
g_m^+=\sum_{i=1}^{m_+} C_{im}^+\eta_i^+,
\qquad
g_n^-=\sum_{j=1}^{m_-} C_{jn}^-\eta_j^-,
```

and define the compressed left vectors

```tex
b_i^+:=\sum_{m=1}^{n_+}\overline{C_{im}^+}\,\lambda_m^+,
\qquad
b_j^-:=\sum_{n=1}^{n_-}\overline{C_{jn}^-}\,\lambda_n^-.
```

Then

```tex
\boxed{
B
=
\sum_{i=1}^{m_+}|b_i^+\rangle\langle \eta_i^+|
\;+\;
\sum_{j=1}^{m_-}|b_j^-\rangle\langle \eta_j^-|.
}
```

Equivalently, with the operator-columns

```tex
E_+:=
\bigl[\,|\eta_1^+\rangle\ \cdots\ |\eta_{m_+}^+\rangle\,\bigr],
\qquad
E_-:=
\bigl[\,|\eta_1^-\rangle\ \cdots\ |\eta_{m_-}^-\rangle\,\bigr],
```

```tex
L_+:=
\bigl[\,|b_1^+\rangle\ \cdots\ |b_{m_+}^+\rangle\,\bigr],
\qquad
L_-:=
\bigl[\,|b_1^-\rangle\ \cdots\ |b_{m_-}^-\rangle\,\bigr],
```

one has the compact factorization

```tex
\boxed{
B=L_+E_+^*+L_-E_-^*.
}
```

#### Proof

Substitute the orthonormal-basis expansions of `g_m^+` and `g_n^-` into the
raw sign-pure decomposition:

```tex
\sum_{m=1}^{n_+}|\lambda_m^+\rangle\langle g_m^+|
=
\sum_{m=1}^{n_+}\sum_{i=1}^{m_+}
\overline{C_{im}^+}\,|\lambda_m^+\rangle\langle \eta_i^+|
=
\sum_{i=1}^{m_+}|b_i^+\rangle\langle \eta_i^+|.
```

The minus part is identical. This proves the compressed sign-pure form, and
the matrix factorization `B=L_+E_+^*+L_-E_-^*` is just the same identity in
operator-column notation. ∎

### Corollary `PO3a finite mixed-matrix form`

Under the compressed matrix receiver,

```tex
P_+HP_-
=
P_+U^*GL_-E_-^*
\;+\;
E_+L_+^*GUP_-
\;+\;
E_+L_+^*GL_-E_-^*.
```

If, in addition, the two leakage operators factor through the finite cap
spaces,

```tex
P_+U^*GL_-=E_+A,
\qquad
L_+^*GUP_-=BE_-^*
```

for finite matrices `A,B`, and if

```tex
M:=L_+^*GL_-,
```

then

```tex
\boxed{
P_+HP_-=E_+(A+B+M)E_-^*.
}
```

In particular,

```tex
P_+HP_-=0
\qquad\Longleftrightarrow\qquad
A+B+M=0.
```

#### Proof

Start from

```tex
H=U^*GB+B^*GU+B^*GB
```

and substitute `B=L_+E_+^*+L_-E_-^*`.

For the first term,

```tex
P_+U^*GBP_-
=
P_+U^*G(L_+E_+^*+L_-E_-^*)P_-.
```

Because `E_+^*P_-=0`, only the minus part survives:

```tex
P_+U^*GBP_-=P_+U^*GL_-E_-^*.
```

For the second term,

```tex
P_+B^*GUP_-
=
P_+(E_+L_+^*+E_-L_-^*)GUP_-,
```

and now `P_+E_-=0`, so

```tex
P_+B^*GUP_-=E_+L_+^*GUP_-.
```

For the third term,

```tex
P_+B^*GBP_-
=
P_+(E_+L_+^*+E_-L_-^*)G(L_+E_+^*+L_-E_-^*)P_-.
```

Again the only surviving block is the cross-sign one:

```tex
P_+B^*GBP_-=E_+L_+^*GL_-E_-^*.
```

Summing the three displayed identities gives the first formula. If
`P_+U^*GL_-=E_+A` and `L_+^*GUP_-=BE_-^*`, then substitution yields

```tex
P_+HP_-
=
E_+AE_-^* + E_+BE_-^* + E_+ME_-^*
=
E_+(A+B+M)E_-^*.
```

Since `E_+` and `E_-` are injective partial isometries on coefficient space,
this vanishes exactly when `A+B+M=0`. ∎

So the fully compressed `PO3a` receiver is now:

```tex
\text{extract }R,C,\rho_r,d_c;
\quad
\text{compress to }B=L_+E_+^*+L_-E_-^*;
\quad
\text{check one finite matrix }A+B+M.
```

### Theorem `PO3a-canonical finite matrix receiver`

The previous receiver can be strengthened by building the finite plus/minus
spaces so that the leakage vectors are included by definition, rather than by
an extra factorization hypothesis.

Keep the same corrected-column setup and the same raw sign-pure decomposition

```tex
B
=
L_+^{\mathrm{raw}}(G_+^{\mathrm{raw}})^*
\;+\;
L_-^{\mathrm{raw}}(G_-^{\mathrm{raw}})^*.
```

Define the finite plus and minus spaces by

```tex
E_+
:=
\operatorname{span}\Bigl(
\operatorname{Ran}G_+^{\mathrm{raw}}
\cup
\operatorname{Ran}(P_+U^*GL_-^{\mathrm{raw}})
\Bigr),
```

```tex
E_-
:=
\operatorname{span}\Bigl(
\operatorname{Ran}G_-^{\mathrm{raw}}
\cup
\operatorname{Ran}(P_-U^*GL_+^{\mathrm{raw}})
\Bigr).
```

Choose orthonormal basis columns

```tex
E_+
=
\bigl[\,|\eta_1^+\rangle\ \cdots\ |\eta_{m_+}^+\rangle\,\bigr],
\qquad
E_-
=
\bigl[\,|\eta_1^-\rangle\ \cdots\ |\eta_{m_-}^-\rangle\,\bigr].
```

Since `\operatorname{Ran}G_\pm^{\mathrm{raw}}\subset E_\pm`, there exist
finite coefficient matrices `C_\pm` such that

```tex
G_+^{\mathrm{raw}}=E_+C_+,
\qquad
G_-^{\mathrm{raw}}=E_-C_-.
```

Set

```tex
L_+:=L_+^{\mathrm{raw}}C_+^*,
\qquad
L_-:=L_-^{\mathrm{raw}}C_-^*.
```

Then

```tex
\boxed{
B=L_+E_+^*+L_-E_-^*.
}
```

Moreover, the leakage terms now factor automatically:

```tex
P_+U^*GL_-=E_+\mathsf A,
\qquad
L_+^*GUP_-=\mathsf B E_-^*,
```

with the canonical finite matrices

```tex
\mathsf A:=E_+^*U^*GL_-,
\qquad
\mathsf B:=L_+^*GUE_-,
\qquad
\mathsf M:=L_+^*GL_-.
```

Hence

```tex
\boxed{
P_+HP_-=E_+(\mathsf A+\mathsf B+\mathsf M)E_-^*.
}
```

In particular,

```tex
\boxed{
P_+HP_-=0
\qquad\Longleftrightarrow\qquad
\mathsf A+\mathsf B+\mathsf M=0.
}
```

#### Proof

The identity

```tex
B=L_+E_+^*+L_-E_-^*
```

follows exactly as before:

```tex
L_+E_+^*
=
L_+^{\mathrm{raw}}C_+^*E_+^*
=
L_+^{\mathrm{raw}}(E_+C_+)^*
=
L_+^{\mathrm{raw}}(G_+^{\mathrm{raw}})^*,
```

and similarly on the minus side.

By construction,

```tex
\operatorname{Ran}(P_+U^*GL_-^{\mathrm{raw}})\subset E_+.
```

Since `L_-=L_-^{\mathrm{raw}}C_-^*`, this implies

```tex
\operatorname{Ran}(P_+U^*GL_-)\subset E_+,
```

hence

```tex
P_+U^*GL_-
=
E_+(E_+^*U^*GL_-)
=
E_+\mathsf A.
```

The minus-side leakage is identical:

```tex
L_+^*GUP_-
=
(L_+^*GUE_-)E_-^*
=
\mathsf B E_-^*.
```

Now substitute `B=L_+E_+^*+L_-E_-^*` into

```tex
H=U^*GB+B^*GU+B^*GB.
```

Exactly as in the previous corollary, the mixed block keeps only the three
cross-sign pieces:

```tex
P_+HP_-
=
P_+U^*GL_-E_-^*
\;+\;
E_+L_+^*GUP_-
\;+\;
E_+L_+^*GL_-E_-^*.
```

Substituting the canonical factorizations and writing
`\mathsf M:=L_+^*GL_-` gives

```tex
P_+HP_-=E_+(\mathsf A+\mathsf B+\mathsf M)E_-^*.
```

Since `E_+^*E_+=I` and `E_-^*E_-=I`, this vanishes exactly when
`\mathsf A+\mathsf B+\mathsf M=0`. ∎

So the strongest current finite-dimensional receiver for `PO3a` is now:

```tex
\text{build the finite plus/minus spaces so that the leakage is already inside;}
\quad
\text{then solve one finite matrix identity }
\mathsf A+\mathsf B+\mathsf M=0.
```

### First-order endpoint specialization

The abstract packet is not separate from the current live route; in the first
endpoint model it collapses exactly to the already active zero-mode vector.

Assume the boundary correction has the single endpoint form

```tex
B
=
|\mathbf 1\rangle\langle \ell_{+,N}P_+ + \ell_{-,N}P_-|.
```

Equivalently, this is the sign-split rank-one expansion

```tex
B
=
|\mathbf 1\rangle\langle \ell_{+,N}P_+|
\;+\;
|\mathbf 1\rangle\langle \ell_{-,N}P_-|,
```

with

```tex
b_{1,+}=b_{1,-}=\mathbf 1,
\qquad
\eta_{1,+}=\ell_{+,N},
\qquad
\eta_{1,-}=\ell_{-,N}.
```

Then `PO3a-core` gives

```tex
P_+HP_-
=
|P_+U^*G\mathbf 1\rangle\langle \ell_{-,N}|
\;+\;
|\ell_{+,N}\rangle\langle P_-U^*G\mathbf 1|
\;+\;
\langle \mathbf 1,G\mathbf 1\rangle
|\ell_{+,N}\rangle\langle \ell_{-,N}|.
```

So in the first-order endpoint model there are no hidden new mechanisms at all.
The three general `PO3a-core` families collapse to:

1. the positive component of the single vector `U^*G\mathbf 1`;
2. the negative component of the same vector;
3. one scalar self-pairing `\langle \mathbf 1,G\mathbf 1\rangle`.

After pulling back along the raw tail synthesis, this is exactly the old
zero-mode receiver

```tex
v_{a,N}:=T_{a,\infty,N}^*G_g[a]\mathbf 1.
```

So the abstract `PO3a-core` theorem is perfectly compatible with the current
live route:

```tex
\text{general three-family cross-sign reduction}
\Longrightarrow
\text{first-order endpoint case}
\Longrightarrow
\text{zero-mode vector } v_{a,N}.
```

This is important because it shows we are not forking the proof. We now have
the same live obstruction described in two equivalent languages:

- upper-shell: three coefficient families from `PO3a-core`;
- lower-shell: the zero-mode / square-tail receiver route.

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

At this point the next honest split is already clear.

```tex
\textbf{SQ1. Direct square-tail rigidity.}
```

Use the new quadratic divisor tower / Newton-profile formulation and attack the
remaining wall directly:

```tex
J_a(r^2)=0\ \forall r>N
\Longrightarrow
J_a\equiv 0.
```

Inside `SQ1`, the quadratic divisor tower has an exact Gibbs-profile
description. Write

```tex
b_\gamma:=\frac{2a^2}{\pi^2}\sin^2(a\gamma),
\qquad
s_j:=(N+j)^2,
\qquad
\lambda_\gamma:=y_\gamma^2.
```

Then

```tex
J_a(z)=\sum_{\gamma\in\Gamma^\sharp}\frac{b_\gamma}{\lambda_\gamma-z},
```

and after dividing by the first `k` square-tail factors one gets

```tex
J_{a,k}(z)
=
\frac{J_a(z)}{\prod_{j=1}^k (z-s_j)}
=
\sum_{\gamma\in\Gamma^\sharp}
\frac{b_\gamma^{(k)}}{\lambda_\gamma-z},
\qquad
b_\gamma^{(k)}
:=
\frac{b_\gamma}{\prod_{j=1}^k (\lambda_\gamma-s_j)}.
```

So the normalized coefficient mass is exactly

```tex
\nu_k(\gamma)
:=
\frac{|b_\gamma|^2\prod_{j=1}^k|\lambda_\gamma-s_j|^{-2}}
{\sum_{\eta\in\Gamma^\sharp}|b_\eta|^2\prod_{j=1}^k|\lambda_\eta-s_j|^{-2}}.
```

For any two support points `\lambda_\gamma,\lambda_\eta` one has the exact
ratio law

```tex
\frac{\nu_k(\gamma)}{\nu_k(\eta)}
=
\frac{|b_\gamma|^2}{|b_\eta|^2}
\prod_{j=1}^k
\frac{|\lambda_\eta-s_j|^2}{|\lambda_\gamma-s_j|^2}.
```

Equivalently, with the quadratic potential

```tex
\Phi_k(\lambda):=\sum_{j=1}^k \log|\lambda-s_j|,
```

the normalized divisor tower is the Gibbs family

```tex
\nu_k(\gamma)
\propto
|b_\gamma|^2 e^{-2\Phi_k(\lambda_\gamma)}.
```

So `SQ1` has now been converted into a precise question about a single moving
weight system on the squared support:

```tex
\text{can the quadratic Gibbs mass }
|b_\gamma|^2 e^{-2\Phi_k(\lambda_\gamma)}
\text{ escape indefinitely as }k\to\infty?
```

There are now two clean structural gains inside this Gibbs picture.

```tex
\textbf{SQ1.1. Fixed-anchor no-drift.}
```

For any two fixed support points `\lambda,\mu\in\Lambda_a` choose square roots
`w^2=\lambda`, `u^2=\mu`. Then

```tex
W_k(\lambda)
:=
|b_\lambda|^2\prod_{j=1}^k |\lambda-(N+j)^2|^{-2}
```

satisfies

```tex
\frac{W_k(\lambda)}{W_k(\mu)}
=
C_{N}(\lambda,\mu)\bigl(1+O_{N,\lambda,\mu}(1/k)\bigr),
\qquad
C_N(\lambda,\mu)\in(0,\infty).
```

Indeed

```tex
\prod_{j=1}^k\bigl((N+j)^2-\lambda\bigr)
=
\frac{\Gamma(N+k+1-w)\Gamma(N+k+1+w)}
{\Gamma(N+1-w)\Gamma(N+1+w)},
```

and the same formula with `u` in place of `w` reduces the ratio to a paired
Gamma quotient; the standard Stirling estimate for
`\Gamma(z+a)\Gamma(z-a)/\Gamma(z)^2` then gives the stated limit. So the fatal
linear-branch drift is absent here: fixed squared anchors do not asymptotically
eat each other.

```tex
\textbf{SQ1.2. Summable pole-envelope criterion.}
```

Define

```tex
\Theta_k:=\prod_{j=1}^k (N+j)^{-4},
\qquad
D_{N,k}(\lambda):=\prod_{j=1}^k\left|1-\frac{\lambda}{(N+j)^2}\right|^{-2},
\qquad
\mathfrak D_N(\lambda):=\sup_{k\ge 0} D_{N,k}(\lambda).
```

Then `W_k(\lambda)=\Theta_k |b_\lambda|^2 D_{N,k}(\lambda)`. If

```tex
\sum_{\lambda\in\Lambda_a}|b_\lambda|^2\mathfrak D_N(\lambda)<\infty,
```

then for every fixed `\lambda`

```tex
D_{N,k}(\lambda)\to D_{N,\infty}(\lambda)
:=
\prod_{j=1}^\infty\left|1-\frac{\lambda}{(N+j)^2}\right|^{-2}\in(0,\infty),
```

and dominated convergence yields

```tex
\frac{Z_k}{\Theta_k}
=
\sum_{\lambda\in\Lambda_a}|b_\lambda|^2D_{N,k}(\lambda)
\longrightarrow
\sum_{\lambda\in\Lambda_a}|b_\lambda|^2D_{N,\infty}(\lambda)
=:M_{N,\infty}\in(0,\infty).
```

Consequently the normalized Gibbs measures converge pointwise to

```tex
\pi_N(\lambda)
:=
\frac{|b_\lambda|^2D_{N,\infty}(\lambda)}{M_{N,\infty}},
```

so under this explicit summability condition there is not just an anchor, but a
full limit law and hence no escape at all.

So the live `SQ1` burden has become much narrower. It is no longer the raw
Gibbs dynamics itself, but the explicit static summability wall

```tex
\sum_{\lambda\in\Lambda_a}|b_\lambda|^2\mathfrak D_N(\lambda)<\infty.
```

One honest half-step of this wall is already explicit.

```tex
\textbf{SQ1.3a. Explicit bound for the limiting square divisor.}
```

Write

```tex
L_N:=\pm\{N+1,N+2,\dots\},
\qquad
\delta_N(y):=\operatorname{dist}(y,L_N).
```

Then for every strip height `A>0` there is a constant `C_{N,A}` such that for
all `y` with `|\Im y|\le A` and `y\notin L_N`,

```tex
D_{N,\infty}(y^2)
=
\prod_{j=1}^\infty\left|1-\frac{y^2}{(N+j)^2}\right|^{-2}
=
|E_N^{sq}(y^2)|^{-2}
\le
C_{N,A}(1+|y|)^{4N+2}\delta_N(y)^{-2}.
```

Indeed the canonical square-tail divider is

```tex
E_N^{sq}(y^2)
=
\prod_{m>N}\left(1-\frac{y^2}{m^2}\right)
=
\frac{\sin(\pi y)}{\pi y}\prod_{m=1}^N\left(1-\frac{y^2}{m^2}\right)^{-1}.
```

The front factor contributes only polynomial growth:

```tex
\left|y\prod_{m=1}^N\left(1-\frac{y^2}{m^2}\right)\right|
\ll_N
(1+|y|)^{2N+1}.
```

On the strip `|\Im y|\le A`, the numerator `\sin(\pi y)` has only simple zeros
at the integers. Near any tail zero `m\in L_N`, periodicity plus bounded-strip
compactness give

```tex
|\sin(\pi y)|\asymp_A |y-m|.
```

Away from the tail lattice, `\delta_N(y)\ge 1/2`, and after the cancellation of
the finitely many front zeros `0,\pm1,\dots,\pm N` the same strip-compactness
argument yields a uniform lower bound of the same shape. Thus

```tex
|E_N^{sq}(y^2)|
\gg_{N,A}
\delta_N(y)(1+|y|)^{-2N-1},
```

which is exactly the stated estimate for `D_{N,\infty}(y^2)`.

So near-pole concentration is now visible in an explicit square-root metric:
the limiting divisor can only blow up through small distance to the tail square
lattice.

Even better, the second half also collapses cleanly.

```tex
\textbf{SQ1.3b. Partial-to-envelope comparison.}
```

For `m\ge N+1` write the individual square factor as

```tex
f_m(y):=\left|1-\frac{y^2}{m^2}\right|^{-2}.
```

Then

```tex
f_m(y)\ge 1
\iff
\left|1-\frac{y^2}{m^2}\right|\le 1
\iff
|y|^4\le 2\Re(y^2)m^2.
```

Indeed

```tex
\left|1-\frac{y^2}{m^2}\right|^2
=
1-\frac{2\Re(y^2)}{m^2}+\frac{|y|^4}{m^4}.
```

So there are only two cases.

If `\Re(y^2)\le 0`, then every factor satisfies `f_m(y)\le 1`, hence
`k\mapsto D_{N,k}(y^2)` is nonincreasing and

```tex
\mathfrak D_N(y^2)=1.
```

If `\Re(y^2)>0`, define the threshold

```tex
m_*(y):=\frac{|y|^2}{\sqrt{2\Re(y^2)}}.
```

Then `f_m(y)\le 1` for `m<m_*(y)` and `f_m(y)\ge 1` for `m\ge m_*(y)`. Hence
the partial products

```tex
D_{N,k}(y^2)=\prod_{j=1}^k f_{N+j}(y)
```

are first nonincreasing and then nondecreasing. Therefore their supremum can
occur only at the endpoints:

```tex
\boxed{
\mathfrak D_N(y^2)=\max\bigl(1,D_{N,\infty}(y^2)\bigr).
}
```

Combining this exact identity with `SQ1.3a` gives the explicit envelope bound

```tex
\boxed{
\mathfrak D_N(y^2)
\le
1+C_{N,A}(1+|y|)^{4N+2}\delta_N(y)^{-2}
\qquad (|\Im y|\le A).
}
```

So the full pole-envelope is now controlled by the same square-root
near-lattice quantity as the limiting divisor, up to an inessential additive
constant.

At this point the direct `SQ1` burden is no longer dynamical at all. It has
been reduced to one static summability check:

```tex
\textbf{SQ1.4. Support-side summability check.}
```

Using `\lambda_\gamma=y_\gamma^2`, it is now enough to prove

```tex
\sum_{\gamma\in\Gamma^\sharp}
|b_\gamma|^2
\left(
1+
(1+|y_\gamma|)^{4N+2}\delta_N(y_\gamma)^{-2}
\right)
<\infty.
```

If this support-side bound holds, then `SQ1.2 + SQ1.3a + SQ1.3b` close the
entire no-escape wall for the quadratic Gibbs family. Local oracle search only
surfaced the project's own Gamma-ratio infrastructure; the short external
sanity-check only confirms the standard sine-product / Gamma-product
identities, not any imported square-tail injectivity theorem. So `SQ1.4` is
now the honest next theorem target inside the direct square-tail branch.

There is also an immediate obstruction built into this sufficient criterion.
Since `\mathfrak D_N(\lambda)\ge 1` for every support point, `SQ1.4` would
already force

```tex
\sum_{\gamma\in\Gamma^\sharp}|b_\gamma|^2<\infty.
```

But here

```tex
b_\gamma=\frac{2a^2}{\pi^2}\sin^2(a\gamma),
```

so this route would require the very strong arithmetic input

```tex
\sum_{\gamma\in\Gamma^\sharp}\sin^4(a\gamma)<\infty.
```

Nothing in the current `PO3a` package provides such decay; on the contrary, the
whole modulo-one / Ford--Zaharescu side story suggests that `a\gamma/\pi`
should behave more like an equidistributed phase than like an `\ell^2` tail.
Therefore `SQ1.2 + SQ1.3` should be read as a sharp diagnostic criterion, but
not as the present mainline unless a radically stronger arithmetic theorem is
inserted. In the current tree this demotes the direct Gibbs no-escape path to a
backup route, and pushes the live burden back toward `SQ2` or another
non-`\ell^2` square-tail mechanism.

```tex
\textbf{SQ2. Square-support backend adaptation.}
```

Try to adapt the old `PO2` discrete-Cauchy backend to the squared support
`\Lambda_a`, now that the support and the sample set are both order-`1/2`
objects.

The exact `SQ2` synthesis is now sharper.

First, the square-support backend should not start from the raw receiver
`J_a(z)=\sum b_\gamma/(\lambda_\gamma-z)`. Unlike the old `PO2` mixed kernel,
the coefficients

```tex
b_\gamma=\frac{2a^2}{\pi^2}\sin^2(a\gamma)
```

come with no inherited decay at `k=0`, so the natural `\ell^2` compatibility of
the old `CB1` packet is not automatic for the undivided square receiver.

However, after one square-tail division this changes completely. For every
`k\ge 1`,

```tex
b_\gamma^{(k)}
=
\frac{b_\gamma}{\prod_{j=1}^k(\lambda_\gamma-(N+j)^2)}
```

obeys

```tex
|b_\gamma^{(k)}|
\ll_{a,N,k}
|\lambda_\gamma|^{-k}
```

on the support, because `|b_\gamma|` is bounded and
`\lambda_\gamma\asymp \gamma^2`. Since

```tex
n_{\Lambda_a}(R)\asymp \sqrt R\log R,
```

already `k=1` gives

```tex
\sum_{\gamma\in\Gamma^\sharp}|b_\gamma^{(1)}|^2<\infty.
```

So the honest backend target is not the raw `J_a`, but the divided receivers
`J_{a,k}` with `k\ge 1`.

This yields the right `SQ2` packet:

```tex
\textbf{SQ2a. Admissibility after one square divisor.}
```

Show that the discrete support `\Lambda_a` with unit weights is admissible for a
Cauchy-de Branges framework, and that each `J_{a,k}` with `k\ge 1` belongs to
the natural `\ell^2` coefficient class over `\Lambda_a`.

```tex
\textbf{SQ2b. Square-tail common-zero package.}
```

Use the canonical square divider

```tex
E_N^{sq}(z)=\prod_{m>N}\left(1-\frac{z}{m^2}\right)
```

as the exact common-zero object for the tail `\{(N+1)^2,(N+2)^2,\dots\}`.
The right question is whether the square-tail quotient class of the divided
receivers forms a nontrivial nearly invariant `*`-closed subspace in the
admissible Cauchy-de Branges ambient space.

```tex
\textbf{SQ2c. Non-vacuous ordering / second subspace.}
```

As in the old `CB2a3` analysis, ordering alone is useless unless one can
produce at least two genuinely distinct nearly invariant `*`-closed square-tail
subspaces. The natural candidate is the internal square-division chain coming
from

```tex
J_{a,k+1}(z)=\frac{J_{a,k}(z)}{z-(N+k+1)^2}.
```

So the live question becomes: does exhausting one square-tail zero change the
associated subspace strictly, or does the chain collapse trivially?

The external signal is now consistent with this split. The 2018
Krein/ordering theorem for Cauchy-de Branges spaces looks structurally
compatible with the strip/parabolic support geometry, but the 2022 localization
route still appears non-routine because it requires power separation; on the
squared support this would mean a quantitative lower gap theorem for
`\lambda_\gamma` or, equivalently, for the scaled ordinates `y_\gamma`.

So the active `SQ2` mainline is now:

```tex
\boxed{
\text{start at }J_{a,1}\text{ (not }J_a\text{), build the square-tail nearly
invariant package, and test whether ordering becomes non-vacuous.}
}
```

The first `SQ2` subbrick is therefore already concrete.

```tex
\textbf{SQ2a1. Base support admissibility on }\Lambda_a.
```

Let

```tex
\mu_a:=\sum_{\lambda\in\Lambda_a}\delta_\lambda.
```

Because

```tex
n_{\Lambda_a}(R)\asymp \sqrt R\log R,
```

the squared support has convergence exponent `1/2`, hence in particular

```tex
\sum_{\lambda\in\Lambda_a}\frac{1}{1+|\lambda|^2}<\infty.
```

So the bare discrete-support summability side of the old `CB1` package is
actually easier on `\Lambda_a` than it was on the unsquared support. The
conjugation symmetry also survives squaring:

```tex
\lambda\in\Lambda_a \Longrightarrow \bar\lambda\in\Lambda_a.
```

Thus the square support with unit weights satisfies the raw discrete Cauchy
support admissibility conditions one would want before even asking for an
ordering theorem.

```tex
\textbf{SQ2a2. Coefficient admissibility for divided receivers.}
```

For every `k\ge 1` define

```tex
J_{a,k}(z)=\sum_{\gamma\in\Gamma^\sharp}
\frac{b_\gamma^{(k)}}{\lambda_\gamma-z},
\qquad
b_\gamma^{(k)}
=
\frac{b_\gamma}{\prod_{j=1}^k(\lambda_\gamma-(N+j)^2)}.
```

Then

```tex
\sum_{\gamma\in\Gamma^\sharp}|b_\gamma^{(k)}|^2<\infty
\qquad (k\ge 1).
```

Indeed `|b_\gamma|` is bounded and

```tex
|b_\gamma^{(k)}|\ll |\lambda_\gamma|^{-k},
```

while the support counting law `n_{\Lambda_a}(R)\asymp \sqrt R\log R` gives
absolute convergence already for

```tex
\sum_{\lambda\in\Lambda_a}|\lambda|^{-2}.
```

So the divided receivers `J_{a,k}` with `k\ge 1` automatically lie in the
natural `\ell^2(\Lambda_a,\mu_a)` coefficient class.

This is a real positive collapse. The old `PO2` backend had to fight for
support admissibility and coefficient decay separately. On the square support,
after one divisor both are automatic:

```tex
\boxed{
\text{raw }J_a\text{ is too rough, but every }J_{a,k}\ (k\ge 1)
\text{ sits in the native discrete Cauchy data class.}
}
```

So `SQ2a` is no longer the blocker. The live wall moves one level deeper:

```tex
\textbf{SQ2b. Can the square-tail zero package be promoted to a nontrivial
nearly invariant `*`-closed subspace framework?}
```

There is also an exact warning here, mirroring the old `CB2a3` lesson.

Let

```tex
s_m:=(N+m)^2,
\qquad
E_k^{sq}(z):=\prod_{m>k}\left(1-\frac{z}{s_m}\right),
```

so `E_k^{sq}` is the canonical common-zero factor for the tail of `J_{a,k}`.
Define the normalized quotient candidate

```tex
G_k(z):=\frac{J_{a,k}(z)}{E_k^{sq}(z)}.
```

Now use the exact relations

```tex
J_{a,k+1}(z)=\frac{J_{a,k}(z)}{z-s_{k+1}},
```

and

```tex
E_k^{sq}(z)=\left(1-\frac{z}{s_{k+1}}\right)E_{k+1}^{sq}(z)
=
-\frac{z-s_{k+1}}{s_{k+1}}E_{k+1}^{sq}(z).
```

Combining them gives

```tex
G_k(z)
=
\frac{J_{a,k}(z)}{E_k^{sq}(z)}
=
-s_{k+1}\frac{J_{a,k}(z)}{(z-s_{k+1})E_{k+1}^{sq}(z)}
=
-s_{k+1}G_{k+1}(z).
```

So all quotient generators are just scalar multiples:

```tex
\boxed{
G_k \in \mathbb C^\times G_{k+1}
\qquad\forall k\ge 0.
}
```

Iterating gives the exact closed form

```tex
G_k(z)=\frac{(-1)^k}{s_1\cdots s_k}\,G_0(z),
\qquad
G_0(z):=\frac{J_a(z)}{E_0^{sq}(z)}.
```

This is a very strong route squeeze. It means the most natural internal
square-division chain does **not** produce a second distinct quotient object
after the common zeros are removed. So the naive `SQ2c` plan

```tex
\text{“use }J_{a,k}\text{ and }J_{a,k+1}\text{ to get two different ordered
subspaces”}
```

is vacuous: after quotienting by the exact square-tail zero package, the chain
collapses to one line.

Therefore the square-support Krein/ordering branch now has the same honest
interface as the old `CB2a3` branch, but in an even sharper form:

```tex
\textbf{SQ2c. Find a genuinely different second square-tail subspace, or
accept that the natural internal chain is vacuous.}
```

So `SQ2` remains mathematically cleaner than `SQ1`, but its most natural
ordering candidate has now been killed exactly. Equivalently: after quotienting
by the full square-tail zero package, the branch is no longer a family
question, but a one-object question about the single normalized quotient `G_0`.

The current search status is honest:

- the local project index does not yet contain a ready-made square-tail
  injectivity theorem beyond the generic `PO2` Cauchy-tail wall;
- a short external probe did not reveal a clean imported uniqueness theorem
  specialized to zeros on `m^2`.

So this branch should now be treated exactly as it stands:

```tex
\text{no imported theorem yet;}
\qquad
\text{live attack } = \text{SQ1 or SQ2 only.}
```

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

There is now a sharper intermediate packet between this slogan and the full
explicit formula.

```tex
\textbf{Endpoint-projector calculus target.}
```

Let

```tex
E_{a,N}:=R_aT_{a,\infty,N}
=
|\mathbf 1\rangle\langle \ell_{+,N}P_+|
\;+\;
|\mathbf 1\rangle\langle \ell_{-,N}P_-|.
```

By Riesz representation, write

```tex
h_{+,N}:=(\ell_{+,N}P_+)^*,
\qquad
h_{-,N}:=(\ell_{-,N}P_-)^*,
```

so

```tex
E_{a,N}^*
=
|h_{+,N}\rangle\langle \mathbf 1|
\;+\;
|h_{-,N}\rangle\langle \mathbf 1|,
```

with `h_{+,N}\in\mathcal H_+` and `h_{-,N}\in\mathcal H_-`.

Now every operator word containing only finitely many endpoint insertions
`E_{a,N},E_{a,N}^*` and otherwise only sign-preserving tail operators expands
into finitely many sign-split rank-one terms. Concretely:

1. one-endpoint words reduce to finitely many vectors paired with
   `\ell_{+,N}P_+` and `\ell_{-,N}P_-`;
2. one-adjoint-endpoint words reduce to finitely many `h_{+,N},h_{-,N}`
   vectors against one physical-space functional;
3. double-endpoint words reduce to finitely many scalar pairings multiplying
   the four rank-one bricks
   `|h_{\sigma,N}\rangle\langle \ell_{\tau,N}P_\tau|`.

So the real next exact theorem-target for `PO3a.2` is narrower than “write
down `B_{a,N}`”. It is:

```tex
\text{prove that every surviving boundary word is a finite sum of endpoint-generated words.}
```

If that lands, the finite sign-split expansion of `B_{a,N}` is automatic from
the explicit rank-two split of `E_{a,N}`.

### Theorem `PO3a-endpoint-word trigger`

The previous slogan can be frozen as one exact reduction lemma.

Let `\mathcal K_N=\mathcal H_{+,N}\oplus \mathcal H_{-,N}` be the tail space,
and keep the endpoint operator

```tex
E_{a,N}
=
|\mathbf 1\rangle\langle \ell_{+,N}P_+|
\;+\;
|\mathbf 1\rangle\langle \ell_{-,N}P_-|
```

with adjoint

```tex
E_{a,N}^*
=
|h_{+,N}\rangle\langle \mathbf 1|
\;+\;
|h_{-,N}\rangle\langle \mathbf 1|.
```

Assume a candidate boundary operator `B_{a,N}^{\mathrm{word}}` is a finite
linear combination of the three endpoint-word families

```tex
A_jE_{a,N},
\qquad
E_{a,N}^*B_j,
\qquad
E_{a,N}^*M_jE_{a,N},
```

where

```tex
A_j:L^2(-a,a)\to \mathcal K_N,
\qquad
B_j:\mathcal K_N\to L^2(-a,a),
\qquad
M_j:L^2(-a,a)\to L^2(-a,a)
```

are bounded and only finitely many indices `j` occur.

Then `B_{a,N}^{\mathrm{word}}` admits a finite sign-split rank-one expansion

```tex
B_{a,N}^{\mathrm{word}}
=
\sum_r |b_{r,+}\rangle\langle \eta_{r,+}|
\;+\;
\sum_s |b_{s,-}\rangle\langle \eta_{s,-}|,
\qquad
\eta_{r,+}\in\mathcal H_{+,N},
\quad
\eta_{s,-}\in\mathcal H_{-,N}.
```

More concretely:

1. writing `A_j\mathbf 1=u_{j,+}+u_{j,-}` with
   `u_{j,\pm}:=P_\pm A_j\mathbf 1`, each one-endpoint word expands as

   ```tex
   A_jE_{a,N}
   =
   \sum_{\sigma,\tau\in\{+,-\}}
   |u_{j,\sigma}\rangle\langle \ell_{\tau,N}P_\tau|;
   ```

2. writing `B_j^*\mathbf 1=v_{j,+}+v_{j,-}` with
   `v_{j,\pm}:=P_\pm B_j^*\mathbf 1`, each adjoint-endpoint word expands as

   ```tex
   E_{a,N}^*B_j
   =
   \sum_{\sigma,\tau\in\{+,-\}}
   |h_{\sigma,N}\rangle\langle v_{j,\tau}|;
   ```

3. each double-endpoint word expands as

   ```tex
   E_{a,N}^*M_jE_{a,N}
   =
   \langle \mathbf 1,M_j\mathbf 1\rangle
   \sum_{\sigma,\tau\in\{+,-\}}
   |h_{\sigma,N}\rangle\langle \ell_{\tau,N}P_\tau|.
   ```

So if the genuine boundary defect `H_{a,N}` is shown to lie in this finite
endpoint-word span, then the abstract packets `PO3a-core`,
`PO3a-finite reduction`, and `PO3a-row-column reduction` become immediately
applicable.

#### Proof

For the first family,

```tex
A_jE_{a,N}
=
A_j|\mathbf 1\rangle\langle \ell_{+,N}P_+|
\;+\;
A_j|\mathbf 1\rangle\langle \ell_{-,N}P_-|
=
|A_j\mathbf 1\rangle\langle \ell_{+,N}P_+|
\;+\;
|A_j\mathbf 1\rangle\langle \ell_{-,N}P_-|.
```

Now split `A_j\mathbf 1` by sign:

```tex
A_j\mathbf 1=u_{j,+}+u_{j,-},
\qquad
u_{j,\pm}=P_\pm A_j\mathbf 1.
```

Substituting this into the previous line gives the four displayed sign-split
rank-one bricks.

For the second family,

```tex
E_{a,N}^*B_j
=
|h_{+,N}\rangle\langle \mathbf 1|B_j
\;+\;
|h_{-,N}\rangle\langle \mathbf 1|B_j
=
|h_{+,N}\rangle\langle B_j^*\mathbf 1|
\;+\;
|h_{-,N}\rangle\langle B_j^*\mathbf 1|.
```

Splitting `B_j^*\mathbf 1=v_{j,+}+v_{j,-}` with `v_{j,\pm}=P_\pm B_j^*\mathbf
1` again yields four sign-split bricks.

For the third family, first compute

```tex
\langle \mathbf 1|M_j|\mathbf 1\rangle
=
\langle \mathbf 1,M_j\mathbf 1\rangle.
```

Therefore

```tex
E_{a,N}^*M_jE_{a,N}
=
\langle \mathbf 1,M_j\mathbf 1\rangle
\Bigl(
|h_{+,N}\rangle\langle \ell_{+,N}P_+|
+ |h_{+,N}\rangle\langle \ell_{-,N}P_-|
+ |h_{-,N}\rangle\langle \ell_{+,N}P_+|
+ |h_{-,N}\rangle\langle \ell_{-,N}P_-|
\Bigr),
```

which is already a finite sign-split rank-one expansion.

Since only finitely many words occur, the whole operator
`B_{a,N}^{\mathrm{word}}` is a finite sum of such sign-split bricks. ∎

The live burden is therefore one step sharper than before:

```tex
\text{it is enough to prove that the real }H_{a,N}
\text{ is generated by finitely many }A E,\ E^*B,\ E^*ME\text{ words.}
```

### Corollary `PO3a-endpoint normal form`

There is one further exact reduction that is closer to the actual Volterra
undoing algebra.

Assume `U,V,U_1,U_2:\mathcal K_N\to\mathcal K_N` are bounded tail operators
that preserve the sign decomposition:

```tex
U P_\pm = P_\pm U P_\pm,
\qquad
V P_\pm = P_\pm V P_\pm,
\qquad
U_i P_\pm = P_\pm U_i P_\pm.
```

Then every finite linear combination of the three word families

```tex
A_jE_{a,N}U_j,
\qquad
V_j^*E_{a,N}^*B_j,
\qquad
U_{1,j}^*E_{a,N}^*M_jE_{a,N}U_{2,j}
```

still admits a finite sign-split rank-one expansion.

#### Proof

By `PO3a-endpoint-word trigger`, it is enough to check that composing on the
tail side by sign-preserving operators does not destroy sign purity on the
right or left vectors.

For the first family,

```tex
A_jE_{a,N}U_j
=
\sum_{\sigma,\tau\in\{+,-\}}
|u_{j,\sigma}\rangle\langle \ell_{\tau,N}P_\tau U_j|,
```

with `u_{j,\sigma}=P_\sigma A_j\mathbf 1` as before. Since `U_j` preserves the
sign decomposition,

```tex
\ell_{\tau,N}P_\tau U_j
=
\ell_{\tau,N}U_jP_\tau,
```

so the right functional still vanishes on the opposite sign subspace and
therefore remains sign-pure of sign `\tau`.

For the second family,

```tex
V_j^*E_{a,N}^*B_j
=
\sum_{\sigma,\tau\in\{+,-\}}
|V_j^*h_{\sigma,N}\rangle\langle v_{j,\tau}|,
```

where `v_{j,\tau}=P_\tau B_j^*\mathbf 1`. Because `V_j^*` also preserves the
sign splitting, `V_j^*h_{\sigma,N}` stays in `\mathcal H_{\sigma,N}`.

For the third family,

```tex
U_{1,j}^*E_{a,N}^*M_jE_{a,N}U_{2,j}
=
\langle \mathbf 1,M_j\mathbf 1\rangle
\sum_{\sigma,\tau\in\{+,-\}}
|U_{1,j}^*h_{\sigma,N}\rangle
\langle \ell_{\tau,N}P_\tau U_{2,j}|,
```

and the same sign-preservation argument applies on both sides.

Hence every such normal-form word is again a finite sum of sign-split rank-one
bricks. ∎

### Lemma `PO3a-outer-endpoint annihilation`

Let `T:=T_{a,\infty,N}` be the raw tail synthesis. Then

```tex
T^*\mathbf 1=0,
\qquad
T^*R_a=0,
\qquad
R_a^*T=0.
```

Consequently, any Volterra-undoing word of the form

```tex
T^*X R_a Y,
\qquad
X R_a^* Y T
```

vanishes whenever the endpoint projector sits directly on the outer pullback
side. So after expanding the defect into finitely many endpoint insertions, the
only potentially surviving words are the normal-form families

```tex
A E_{a,N}U,
\qquad
V^*E_{a,N}^*B,
\qquad
U_1^*E_{a,N}^*ME_{a,N}U_2.
```

#### Proof

The identity `T^*\mathbf 1=0` was already frozen above from Fourier
orthogonality, because `T` uses only nonzero modes while `\mathbf 1` is the
zero mode.

Since

```tex
R_a=\mathbf 1\otimes \operatorname{ev}_{-a},
```

one has

```tex
T^*R_a
=
T^*|\mathbf 1\rangle\langle \operatorname{ev}_{-a}|
=
|T^*\mathbf 1\rangle\langle \operatorname{ev}_{-a}|
=
0.
```

Taking adjoints gives

```tex
R_a^*T=(T^*R_a)^*=0.
```

So any word in which `R_a` or `R_a^*` sits immediately on the outer synthesis
side dies. The surviving one-endpoint words must therefore contain the
composites `R_aT=E_{a,N}` or `T^*R_a^*=E_{a,N}^*`, and any surviving
two-endpoint word must contain both of them, which is exactly the displayed
normal form. ∎

### Theorem `PO3a-two-endpoint extraction`

There is now one exact algebraic receiver that captures what the real
Volterra-undoing route would have to prove.

Let `U,V:\mathcal K_N\to\mathcal K_N` be bounded sign-preserving tail
operators, let `K_a:L^2(-a,a)\to L^2(-a,a)` be bounded, and assume the
boundary defect admits the Volterra normal form

```tex
H_{a,N}^{\mathrm{Vol}}
:=
U^*T^*
\Bigl(
(I-R_a)^*K_a(I-R_a)-K_a
\Bigr)
TV.
```

Then one has the exact decomposition

```tex
\boxed{
H_{a,N}^{\mathrm{Vol}}
=
-\,U^*E_{a,N}^*K_aTV
\;-\;
U^*T^*K_aE_{a,N}V
\;+\;
U^*E_{a,N}^*K_aE_{a,N}V.
}
```

In particular, `H_{a,N}^{\mathrm{Vol}}` is a finite linear combination of the
three endpoint normal-form families

```tex
A E_{a,N}U,
\qquad
V^*E_{a,N}^*B,
\qquad
U_1^*E_{a,N}^*ME_{a,N}U_2,
```

and therefore admits a finite sign-split rank-one expansion.

#### Proof

Expand the bracket:

```tex
(I-R_a)^*K_a(I-R_a)-K_a
=
K_a - R_a^*K_a - K_aR_a + R_a^*K_aR_a - K_a
```

so

```tex
(I-R_a)^*K_a(I-R_a)-K_a
=
-\,R_a^*K_a
-\,K_aR_a
+\,R_a^*K_aR_a.
```

Multiplying on the outside by `U^*T^*` and `TV` gives

```tex
H_{a,N}^{\mathrm{Vol}}
=
-\,U^*T^*R_a^*K_aTV
\;-\;
U^*T^*K_aR_aTV
\;+\;
U^*T^*R_a^*K_aR_aTV.
```

Using the definitions

```tex
E_{a,N}=R_aT,
\qquad
E_{a,N}^*=T^*R_a^*,
```

this becomes exactly

```tex
H_{a,N}^{\mathrm{Vol}}
=
-\,U^*E_{a,N}^*K_aTV
\;-\;
U^*T^*K_aE_{a,N}V
\;+\;
U^*E_{a,N}^*K_aE_{a,N}V.
```

The first term is of the family `V^*E_{a,N}^*B`, the second is of the family
`AE_{a,N}U`, and the third is of the family `U_1^*E_{a,N}^*ME_{a,N}U_2`.
So `PO3a-endpoint normal form` applies and yields the finite sign-split
rank-one expansion. ∎

This is the sharpest current formulation of the live algebraic burden:

```tex
\text{it is enough to prove that the real }H_{a,N}
\text{ admits exactly this Volterra normal form.}
```

### Corollary `PO3a-zero-mode collapse under two-endpoint extraction`

Under the self-adjoint Volterra normal form, the surviving boundary packet is
already controlled by one tail vector and one scalar.

Assume the setup of `PO3a-two-endpoint extraction`, and in addition assume
`K_a=K_a^*`. Define

```tex
v_{K,a,N}:=T^*K_a\mathbf 1\in \mathcal K_N,
\qquad
c_{K,a}:=\langle \mathbf 1,K_a\mathbf 1\rangle\in\mathbb C.
```

Then

```tex
\boxed{
H_{a,N}^{\mathrm{Vol}}
=
-\sum_{\sigma\in\{+,-\}}
|U^*h_{\sigma,N}\rangle\langle V^*v_{K,a,N}|
\;-\;
\sum_{\tau\in\{+,-\}}
|U^*v_{K,a,N}\rangle\langle \ell_{\tau,N}P_\tau V|
\;+\;
c_{K,a}
\sum_{\sigma,\tau\in\{+,-\}}
|U^*h_{\sigma,N}\rangle\langle \ell_{\tau,N}P_\tau V|.
}
```

So once the Volterra normal form is real, the entire boundary layer is
generated by:

1. the single tail vector `v_{K,a,N}=T^*K_a\mathbf 1`;
2. the single scalar `c_{K,a}=\langle \mathbf 1,K_a\mathbf 1\rangle`;
3. the fixed endpoint Riesz vectors `h_{+,N},h_{-,N}` and functionals
   `\ell_{+,N}P_+`, `\ell_{-,N}P_-`.

#### Proof

Start from the three-term decomposition of `PO3a-two-endpoint extraction`.

For the first term,

```tex
U^*E_{a,N}^*K_aTV
=
U^*
\bigl(
|h_{+,N}\rangle\langle \mathbf 1|
+ |h_{-,N}\rangle\langle \mathbf 1|
\bigr)
K_aTV.
```

Since `K_a=K_a^*`,

```tex
\langle \mathbf 1|K_aTV
=
\langle T^*K_a\mathbf 1|V
=
\langle V^*v_{K,a,N}|.
```

Hence

```tex
U^*E_{a,N}^*K_aTV
=
\sum_{\sigma\in\{+,-\}}
|U^*h_{\sigma,N}\rangle\langle V^*v_{K,a,N}|.
```

For the second term,

```tex
U^*T^*K_aE_{a,N}V
=
U^*T^*K_a
\bigl(
|\mathbf 1\rangle\langle \ell_{+,N}P_+|
+ |\mathbf 1\rangle\langle \ell_{-,N}P_-|
\bigr)V
```

which becomes

```tex
U^*T^*K_aE_{a,N}V
=
\sum_{\tau\in\{+,-\}}
|U^*v_{K,a,N}\rangle\langle \ell_{\tau,N}P_\tau V|.
```

For the third term,

```tex
U^*E_{a,N}^*K_aE_{a,N}V
=
U^*
\bigl(
|h_{+,N}\rangle\langle \mathbf 1|
+ |h_{-,N}\rangle\langle \mathbf 1|
\bigr)
K_a
\bigl(
|\mathbf 1\rangle\langle \ell_{+,N}P_+|
+ |\mathbf 1\rangle\langle \ell_{-,N}P_-|
\bigr)V.
```

The middle scalar is exactly `c_{K,a}=\langle \mathbf 1,K_a\mathbf 1\rangle`,
so

```tex
U^*E_{a,N}^*K_aE_{a,N}V
=
c_{K,a}
\sum_{\sigma,\tau\in\{+,-\}}
|U^*h_{\sigma,N}\rangle\langle \ell_{\tau,N}P_\tau V|.
```

Substituting these three identities back into
`PO3a-two-endpoint extraction` gives the displayed formula. ∎

This is the cleanest current lower-shell receiver for `PO3a`:

```tex
\text{after the Volterra normal form lands, the live data are only }
v_{K,a,N}
\text{ and }
c_{K,a}.
```

### Corollary `PO3a-return to the project zero-mode receiver`

If the genuine Volterra normal form uses the physical kernel itself,

```tex
K_a=G_g[a],
```

then the generic vector from the previous corollary is exactly the already
active project receiver

```tex
v_{K,a,N}=T^*G_g[a]\mathbf 1=v_{a,N},
```

and the scalar is

```tex
c_{K,a}
=
\langle \mathbf 1,G_g[a]\mathbf 1\rangle.
```

So in that natural specialization,

```tex
\text{`PO3a-zero-mode collapse' does not create a new object at all;}
```

it simply recovers the old lower-shell zero-mode vector together with one
constant self-pairing.

In particular, if the real boundary defect can be written in the Volterra
normal form with `K_a=G_g[a]`, then the whole lower-shell `PO3a` burden
compresses exactly to:

1. the sign structure of `v_{a,N}=T^*G_g[a]\mathbf 1`;
2. the scalar `\langle \mathbf 1,G_g[a]\mathbf 1\rangle`;
3. the fixed endpoint vectors `h_{\pm,N}` and functionals
   `\ell_{\pm,N}P_\pm`.

So the new Volterra packets and the older zero-mode route are now frozen as two
descriptions of the same receiver, not two competing backends.

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
