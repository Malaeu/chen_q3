# STATUS: TRY_GLOBAL_COMPENSATION_VIA_WEIGHTED_ENERGY
```yaml
OPERATIVE_CLASS: TRY_GLOBAL_COMPENSATION_VIA_WEIGHTED_ENERGY
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-19
SCOPE: ABSTRACT
VERIFIER: PAPER
SOURCE_COMMIT: 1bf11ae615822bfd1dfcab709eef8a703d378285
PROTOCOL_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
LOCAL_COMPENSATION_USED: true
LOCAL_POINTWISE_POSITIVITY_USED: false
MAIN_IDENTITY: L_sigma(PPbar)=2/sigma*d_sigma_norm_sq
GLOBAL_SIGN_PROVED: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 4
```

Ы. Поправка владельца принята: факт необходимости сохранять компенсацию между t был известен раньше и не считается новым прогрессом. Этот раунд не возвращается к локальной положительности. Объект сразу интегрируется по всей t-прямой.

## 1. Полностью компенсированный объект

[ABSTRACT][PAPER] Пусть
\[
f_\sigma(t)=e^{\sigma t}\Phi(t),\qquad D=-i\partial_t,
\]
и P — произвольный комплексный полином, фиксированный при дифференцировании по sigma. По Пляншерелю
\[
\|P(D)f_\sigma\|_2^2=\frac1{2\pi}\int |P(\tau)|^2|F(\sigma+i\tau)|^2d\tau.
\]
Поэтому
\[
\boxed{\mathcal L_\sigma(P\overline P)=\frac2\sigma\partial_\sigma\|P(D)f_\sigma\|_2^2.}
\tag{1}
\]
Это точная форма, где все t уже просуммированы до знакового вопроса. Никакая локальная ell_t и никакой локальный Schur-остаток не заменяют (1).

## 2. Точное раскрытие без потери компенсации

[ABSTRACT][PAPER] Так как D(e^{\sigma t}g)=e^{\sigma t}(D-i\sigma)g,
\[
P(D)f_\sigma=e^{\sigma t}P(D-i\sigma)\Phi.
\]
Обозначим
\[
G_{\sigma,P}=P(D-i\sigma)\Phi.
\]
Тогда прямое дифференцирование полной нормы даёт
\[
\boxed{
\frac12\partial_\sigma\|P(D)f_\sigma\|_2^2
=\int_{\mathbb R}e^{2\sigma t}
\left[t|G_{\sigma,P}|^2-
\Im\left(G_{\sigma,P}\overline{P'(D-i\sigma)\Phi}\right)\right]dt.
}
\tag{2}
\]
Все перекрёстные члены P и все разные t остаются внутри одного интеграла. Это не сумма поточечно положительных вкладов.

Интегрирование первого члена по частям, используя быстрое убывание Phi, даёт эквивалентную компенсированную форму
\[
\boxed{
\frac12\partial_\sigma\|P(D)f_\sigma\|_2^2
=-\frac1\sigma\Re\int e^{2\sigma t}
G'_{\sigma,P}\overline{G_{\sigma,P}}dt
-\int e^{2\sigma t}\Im\left(G_{\sigma,P}\overline{P'(D-i\sigma)\Phi}\right)dt.
}
\tag{3}
\]
Здесь штрих у G означает t-производную. Формулы (2),(3) — один глобальный объект; запрещено оценивать два интеграла независимо, если это разрушает cancellation.

## 3. Что это говорит о требуемом all-order законе

[ABSTRACT][PAPER] Для глобальной положительности всех Hankel-форм достаточно и необходимо в текущем Fourier/moment bridge доказать
\[
\boxed{
\partial_\sigma\|P(D)f_\sigma\|_2^2\ge0
\quad\forall P,\quad0<\sigma\le1/2.
}
\tag{4}
\]
Это уже сохраняет компенсацию. Но (4) не следует из положительности нормы и здесь НЕ объявляется доказанным.

Минимальная недостающая identity теперь точнее: найти source-specific оператор B_sigma на замыкании полиномиальных производных Phi такой, что
\[
\frac12\partial_\sigma\|P(D)f_\sigma\|_2^2
=\|B_\sigma P(D)f_\sigma\|_2^2
\]
или, слабее, точную сумму неотрицательных глобальных интегралов после совместного интегрирования по t. Коэффициенты B_sigma не могут зависеть от P через неизвестные нули F.

## 4. Сильнейшая атака

[ABSTRACT][PAPER] Простая локализация по t запрещена предыдущим строгим свидетелем ell_0(X^5-66X^3+678X)^2<0. Поэтому любой B_sigma, действующий как pointwise multiplier/local source Gram до интегрирования, не может быть универсальным all-order объяснением. Допустимый фактор обязан быть нелокальным по t или использовать производные/интегрирование по частям так, чтобы отрицательные локальные области компенсировались до оценки.

Нельзя также разделять (3) и требовать положительности каждого члена: это возвращает уже известную ошибку budget-by-parts.

## 5. Два кандидата на следующий decisive test

[COFINAL_FAMILY][CONDITIONAL] R1 — commutator factorization. Пусть A_sigma=D-i sigma на weighted representation. Вычислить quadratic form производной нормы как антикоммутатор генератора sigma-деформации с P(A_sigma)^*P(A_sigma), затем искать точное completion-of-squares с source potential V=-Phi'/Phi. Kill-power 10/10, первый символический тест 3/10. Отрицательный конечный polynomial witness для полного интеграла убьёт эту theorem-shape; локальный witness не убивает.

[COFINAL_FAMILY][CONDITIONAL] R2 — global orthogonal-polynomial Schur law. Строить P_n из УЖЕ УСРЕДНЁННЫХ mu_j(sigma), затем дифференцировать их глобальную норму с учётом условия ортогональности. В производной коэффициентов P_n возникают члены, но ортогональность может уничтожить их. Если получится
\[
\partial_\sigma\mathcal L_\sigma(|P_n|^2)
=\text{global nonnegative expression},
\]
это даёт индукционный закон без локальной positivity. Kill-power 10/10, стоимость 4/10.

FINAL PROPOSAL: первым тестировать R2, потому что он использует ровно доказанную Schur-структуру и автоматически сохраняет t-компенсацию. Registered prediction: производная минимальной глобальной нормы после ортогонализации убирает производные коэффициентов P_n, но оставшийся знак потребует одной source-specific commutator identity. Если уже для n=2 или n=3 остаётся неподписанный член без структурного сокращения, немедленно перейти к R1, не увеличивая размер матрицы.

MINIMAL_MISSING_IDENTITY: GLOBAL_ORTHOGONAL_NORM_DERIVATIVE_SQUARE_IDENTITY.

K8A:
DOWNSTREAM_CONSUMER: H>=0 for all tau and 0<sigma<=1/2.
ACTUAL_CONSUMER_REQUIREMENT: positivity of the full averaged functional L_sigma on all polynomial squares, or direct full Fourier sign.
ORIGINAL_REQUESTED_OBJECT: compensation-preserving all-order law.
ORIGINAL_OBJECT_IS: PROVED_NECESSARY as a route interface only up to equivalent direct-sign alternatives.
KNOWN_WEAKER_INTERFACES: direct H>=0; vanishing-error lower envelopes.
FAILURE_TYPE: NO_DERIVATION for the all-order square identity.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: exact global energy representation after integration, not local source positivity.

META CLOSEOUT:
- Became smaller: the search is restricted to global weighted-energy/orthogonalized identities.
- Killed earlier: local all-order positivity only; not revisited.
- Must not try again: pointwise t positivity, separate budgeting of compensating terms, finite-minor extrapolation.
- Current smallest gap: GLOBAL_ORTHOGONAL_NORM_DERIVATIVE_SQUARE_IDENTITY.
- Next cheapest decisive test: derive the sigma derivative for the globally orthogonal monic polynomial P_n at n=2,3 and inspect exact cancellations before any numerics.
- Prior prediction: local positivity bootstrap remains refuted; compensation requirement preserved.
- Memory: target=GLOBAL_COMPENSATION; operator=REPRESENTATION_SHIFT; next=R2 symbolic preflight.

VERIFICATION HANDOFF: only this Markdown is written; no Lean source changed. Lean/Arb not run; no axiom profile claimed. Independent mathematical review remains pending.
