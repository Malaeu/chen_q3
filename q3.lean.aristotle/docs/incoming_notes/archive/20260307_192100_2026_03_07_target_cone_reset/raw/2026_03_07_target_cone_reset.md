# Target Cone Reset Note

Source: user note pasted into Codex session on 2026-03-07.

## Claim

According to a document from December 24, 2025, надо скорректировать курс жёстко:
**не shifted-A3 на exact A1′ family, а исправление самой target cone.**
В текущем Q3 mainline всё ещё заявлена как “density on `(W_K)` + continuity + A3/RKHS
`=> Q >= 0` on full Weil class”, причём Section 12/13 фактически берёт
`W_K = C^+_{\mathrm{even}}([-K,K])` и дальше утверждает `Q(\Phi) >= 0` для всех
even compactly supported `\Phi`. Но классический Weil criterion в нормальной форме
идёт не по всем таким `\Phi`, а по convolution squares `\psi * \psi^e`:
RH эквивалентна `W(\psi * \psi^e) >= 0` для всех `\psi \in C_c^\infty(\mathbb R)`.

Из этого делается вывод:

1. текущая mainline-цель в Q3 слишком широка и как написана ложна;
2. для Archimedean density
   `a(\xi) = \log \pi - \Re \psi(1/4 + i \pi \xi) = -\log|\xi| + O(1)`
   при больших `|\xi|`, так что можно построить even nonnegative compactly supported bump
   вдали от active prime nodes, где prime part vanishes but Archimedean integral is negative;
3. значит target cone должен быть не `C_c^+`-style cone, а positive-definite /
   convolution-square Weil cone;
4. current shifted A1′ надо снять с mainline;
5. centered A3 + RKHS остаются, но новый missing theorem — это centered density theorem
   inside a corrected positive-definite cone.

## Proposed corrected chain

`T0-corr`
`=>` corrected Weil cone `\mathcal W^{pd}`
`=>` centered packet density `(A1-pd)` in `\mathcal W_K^{pd}`
`=>` centered A3/RKHS positivity
`=>` A2 closure on each `\mathcal W_K^{pd}`
`=>` LF-lift
`=>` Weil criterion
`=>` RH.

## Proposed new theorem target

For every `K > 0`, centered Fejér×heat / autocorrelation packets are dense in the
corrected local Weil-positive-definite cone `\mathcal W_K^{pd}` in the topology needed
by A2.

## Operational conclusion from the note

- This is not a “finish shifted positivity” note.
- It claims the present target cone itself is wrong.
- Therefore it potentially attacks the current pipeline before `G1/G2/G3`, not after.
