# Usage card — Lagarias–Suzuki (math/0412039) & Lagarias (math/0601653)

Read in full as text here: `ls1.txt` = arXiv math/0412039v4 (3 Nov 2005); `ls2.txt` = arXiv math/0601653v2 (30 Jan 2006).
Journal refs (J. Number Theory 118 (2006) 98–122 / J. Théor. Nombres Bordeaux 18 (2006)) [MEMORY, UNVERIFIED].

## A. math/0412039 — "RH for certain integrals of Eisenstein series"

(a) **Functions.** `E*(z,s)=π^{-s}Γ(s)ζ(2s)·½Σ_{(c,d)=1} y^s/|cz+d|^{2s}` (eq. (2), p.1), constant term
`a₀(y,s)=ζ*(2s)y^s+ζ*(2−2s)y^{1−s}` (eq. (10), p.2). Three targets:
`Z_{2,Q}(s)=ζ*(2s)/(s−1) − ζ*(2−2s)/s` (Thm 1, eq. (15), p.3);
`I(T,s)=−ζ*(2s)T^{s−1}/(s−1) + ζ*(2−2s)T^{−s}/s` (Thm 2, eq. (20), p.3, = ∫∫_{D^T}E*dxdy/y², eq. (17)–(18));
`a₀(y,s)` for y ≥ 1 (Thm 3, eq. (22), p.4). Note `Z_{2,Q}(s) = −I(1,s)` (eq. (21), p.4).

(b) **Decomposition.** Everything is cleared to an entire two-term object
`H(T,s) = ¼(2s)(2s−1)(2s−2)I(T,s) = −ξ(2s)T^{s−1} + ξ(2s−1)T^{−s}` (eq. (42), p.11), i.e.
`A(s) = ξ(2s)T^{s−1}`, `B(s) = ξ(2s−1)T^{−s}` — a shift-pair `F(s+c)`, `F(s−c)` with `F(s)=ξ(2s−½)`, `c=¼`.

(c) **Inequality — half-plane dominance, proved zero-block by zero-block. Theorem 4 (p.7):**
F entire of genus ≤ 1, real on ℝ, `F(s)=±F(1−s)` (i), all zeros in `|Re s−½| < a` (ii).
Then for `c ≥ a`: `|F(s+c)/F(s−c)| > 1` on Re s > ½ (eq. (27)) and `< 1` on Re s < ½ (eq. (28)); hence
`G_θ(s)=F(s+c)+e^{iθ}F(s−c)` (eq. (29)) has **all** zeros on Re s = ½.
Proof: block Hadamard product with convergence factors removed (eq. (31)–(32)), then per-block
`|(s+c−ρ)/(s−c−(1−ρ̄))|² > 1` (eq. (34)), which reduces to `(σ+c−β)² > (σ−c−1+β)²`, i.e. to
`σ>½` **and** `2c > 2(β−½)` (p.9–10). Remark (2), p.10: "*The local inequality argument … paired zeros ρ
and 1−ρ̄, a condition that requires only that F(s) have constant modulus on the critical line*."

(d) **The unconditional input is exactly `0 < β < 1`**, i.e. the classical zero-free line Re s = 1
(Hadamard–de la Vallée Poussin; Euler product gives Re s > 1). Verbatim, p.11: "*the zeros of F(s) are
confined to ¼ < ℜ(s) < ¾, so we can take a = ¼*", then `c = ¼` gives `|ξ(2s)/ξ(2s−1)| > 1` (eq. (41)).
The second input is trivial: `T ≥ 1` ⟹ `T^{2σ−1} ≥ 1` for σ > ½, so the T-factor cannot undo the
dominance (p.11). Nothing else. `T ≥ 1` is sharp — RH fails for I(T,s) for all 0<T<1 (p.3, via Hejhal).
For **Theorem 3** the input is different and genuinely automorphic: **Maass–Selberg** (Lemma 1, eq. (47),
p.12), where `(s−s̄)(1−s−s̄)∫_D|E*_T|²dxdy/y² ≠ 0` off {Re s = ½} ∪ ℝ — an L² positivity; plus
`E*(z,σ) > 0` for real σ > 1 from the defining series (Lemma 2, p.13), and `f(σ)>0` from the product (eq. (50)).
The real-zero threshold `y* = 4πe^{−γ}` comes from `G(y,½) = (log4π − γ − log y)√y` (p.12).

(e) **Where it stops.** The mechanism needs **two** terms of unequal modulus off the line; ξ alone is one term,
and at `c=0` the ratio (27) is `|F(s)/F(s)| ≡ 1` — empty. Taking `c < ¼` requires shrinking the strip (ii),
i.e. `β < ½ + 2c` for **all** zeros: the required shift equals the width of the unconditional zero-free strip,
so closing `β<1 → β=½` **is** RH. Authors on their own Thm 3 (p.19): "*Here our result Theorem 3 is again a
direct verification without providing a mechanism.*"

(f) **Modularity is inessential for Thms 1–2.** Their proof uses only ξ's functional equation, reality, genus,
and the strip. PSL(2,ℤ) enters only to (i) *identify* `I(T,s)`, `Z_{2,Q}(s)` as E*-integrals (eq. (13),(17)),
(ii) note `D^T ⊂ F` iff `T ≥ 1` (p.3), (iii) supply Zagier's `∫∫_F E*dµ_H ≡ 0` to get `Z_{2,Q}=−I(1,s)` (p.4).
**Nonnegativity of µ is never used in the proofs of Thms 1–2** despite the abstract's framing; the paper has no
general theorem about nonnegative measures. Hecke operators: never. Automorphy is essential in exactly one
place — Maass–Selberg for Thm 3 — and that yields only *modified* RH for `a₀(y,s)`, never anything about ζ.

## B. math/0601653 — "Zero spacing distributions for differenced L-functions"

(a)+(b) `A_h(s)=½(ξ(s+h)+ξ(s−h))`, `B_h(s)=−(1/2i)(ξ(s+h)−ξ(s−h))`, θ-family `A_{h,θ},B_{h,θ}` from
`E_{h,θ}(s)=e^{iθ}ξ(s+h)` (p.8). Decomposition is Hermite–Biehler: `E = A − iB`,
`A=½(E(s)+E(1−s̄))`, `B=−(1/2i)(E(s)−E(1−s̄))` (Lemma 2.2, p.6).

(c) **Hermite–Biehler / de Branges.** *Lemma 2.2* (= de Branges [1, Lemma 5], p.6): if
`|E(s)| > |E(1−s̄)|` for Re s > ½ (eq. (2.6)), then A and B have all zeros on Re s = ½ and they **interlace**.
*Lemma 2.1(1)* (p.5) supplies the hypothesis unconditionally: `|ξ(h+s)| > |ξ(h+1−s̄)|` for Re s > ½, `h ≥ ½`
(eq. (2.3)). *Theorem 2.1(1)* (p.8): for `|h| ≥ ½` all zeros of `A_{h,θ}, B_{h,θ}` are on the line, simple, interlacing.

(d) **Input again `0 < β < 1`.** Proof of Lemma 2.1 is per-zero in the modified Hadamard product (2.1),
reduced to `|β−h−σ| > |β−h−(1−σ)|` (eq. (2.5)). Case (1), p.6: "*Suppose h ≥ ½ so that β − h − ½ < 0*",
then the triangle inequality is strict. `β − h − ½ < 0` for `h = ½` ⟺ `β < 1`. Under RH (`β = ½`) any `h>0`
works — that is exactly case (2). Simplicity uses the same input: a double zero forces `ρ₀ = s₀+h` with
`Re ρ₀ = ½ + h ≥ 1`, "*a contradiction*" (p.8). The exponential factor is handled by `Re B*(χ₀) ≥ 0`,
in fact `B*(χ₀) = 0` (eq. (2.2), p.4).

(e) **Where it stops, sharply.** `h ≥ ½` means the shifted zeros sit at `Re ≥ 1` — *outside* the critical strip,
where the Euler product converges absolutely and all arithmetic is switched off. §7(2), p.19: "*One can prove an
unconditional result for |h| > ½, since … the Dirichlet series of L(s,π) converges absolutely for ℜ(s) > 1*",
giving `ζ'/ζ(½+h+it) = O(1)` (Lemma 4.1, `R_h(T)`, p.11). At `h = 0` the hypothesis (2.6) degenerates to the
identity `|ξ(1−s̄)| = |ξ(s)|` (ξ(1−s̄)=conj ξ(s)) — **zero content**, and `B_0 ≡ 0`, `A_0 = ξ`. The step that
would require RH is precisely case (2) of Lemma 2.1: pushing `h` below ½ needs `β = ½`.
Two further hard stops stated by the author: (i) §6, p.19 — the de Branges space that exists unconditionally is
`E(z) = ξ(1−iz)` (= h=½, θ=0), and Conrey–Li showed de Branges's sufficient conditions **fail** for exactly
that space; (ii) §7(1), p.19: "*we do not know of any analogue of an Euler product (or Hecke operator
factorization) that is preserved under such deformations.*"

(f) **No modular structure at all** in this paper; only the functional equation + reality on the line +
`0<β<1` + genus 1. §5 extends verbatim to primitive Dirichlet ξ(s,χ), where reality on ℝ is *dropped*
(Remark after Lemma 2.1, p.5: the relevant property is "*constant phase on the critical line*").

## C. One structural fact worth keeping (Theorem 4.1, p.11 + §7(3), p.20)

For every `h ≠ 0` (unconditionally for `|h| ≥ ½`) the normalized zero spacings of `A_{h,θ}, B_{h,θ}` converge to
a **delta measure at (1,1,…,1)** — perfectly rigid unit spacing, no GUE. Reason (p.11): the zeros are a small
perturbation of `arg Γ`-driven archimedean points. Hence Lagarias's own question, §7(3), p.20:
"*Is it true that any entire function G(s) such that for some h>0, ξ(s) = ½(G(s+h)+G(s−h)) necessarily has the
property that not all its zeros lie on the critical line?*" — he expects **yes**, because ξ should satisfy GUE.

## D. Transfer to `Q(f₀ s)` / Ξ (WHY_NOT_YET.md, read 2026-09-06) — **NO.**

1. **Zero-local by construction.** Both mechanisms (Thm 4 eq. (33)–(36); Lemma 2.1 eq. (2.4)–(2.5)) run
   term-by-term over the Hadamard product and take **zero locations as input**, producing zero locations of a
   *different* function. No prime / Euler-product data enters anywhere. This fails filter item §4.2 of
   WHY_NOT_YET (a second expression must be written **without** zeros and without assuming their reality) in the
   most direct way possible: it assumes their location.
2. **Zero kill-power — passes plants by design.** Theorem 4 applied to a plant with off-line zeros in a strip
   (e.g. `(1+16z²)cos 8z`) still concludes that `F(s+c)+F(s−c)` has all zeros on the line. The method is
   *indifferent* to whether F satisfies RH. Fails filter §4.3.
3. **The only unconditional inequality about ξ produced is Lemma 2.1(1)**, `|ξ(h+s)| > |ξ(h+1−s̄)|`,
   Re s > ½, h ≥ ½. Its content is exactly `β < 1` (Hadamard–de la Vallée Poussin) re-dressed as
   Hermite–Biehler. It is (i) not new, (ii) a pointwise modulus inequality on a *shifted copy*, not a
   statement about Ξ on the real axis, and (iii) carries no quadratic form: nothing in either paper touches
   `Q(f₀ s)`, a signed Dirichlet form, or any positivity on tests. Fails filter §4.1 (it is the de Branges
   coordinate already in WHY_NOT_YET §1) and §4.5 (its margin `~|β−h−½|` → 0 as (h,β)→(½,1); pure slack).
4. **The automorphic input (Maass–Selberg, ls1 eq. (47)) does not transfer.** It is L² positivity of the
   *truncated* Eisenstein series and bites only because `a₀(T,s)` factors out of the right side of (47). It
   gives modified RH for a two-term object, never a decomposition of ζ, and says nothing about the Weil form.
5. **What is worth taking (both are obstructions, not routes, and both are cheap to apply):**
   - **A discriminator for future candidates.** Any proposal to write Ξ as a two-term dominance combination
     `A_{h,θ}` of something with real zeros must reproduce GUE-like local statistics; ls2 Thm 4.1 proves this
     whole class has rigid unit spacing instead. This is a seconds-cost plant test on any such candidate,
     and it is *independent* of the ones in WHY_NOT_YET §4.3.
   - **One line for WHY_NOT_YET §1, row "Hermite–Biehler / de Branges".** The record column should note that
     the unconditionally-existing de Branges space is exactly `E(z)=ξ(1−iz)` (h=½), and that Conrey–Li
     refuted de Branges's sufficient conditions for precisely that space (ls2 §6, p.19). The coordinate is not
     merely equivalent to RH — its best-studied sufficient condition is dead.
6. **Blunt summary.** These are theorems about *other* functions (`I(T,s)`, `Z_{2,Q}`, `a₀(y,s)`, `A_h`, `B_h`),
   all of which are two-term shift-combinations whose off-line dominance is bought by moving `h ≥ ½` outside
   the critical strip. The papers contain **no** new unconditional inequality about Ξ and **nothing** about the
   Weil form. Recommended disposition: one paragraph in `docs/CHAT_DIGESTS.md`, no probe, no batch.
