# Uniform bound divergence

https://chat.openai.com/c/694c525b-51c0-832a-8d87-6e4e9e283b67

## USER
mne nuzny otwety na eti woprosy  но global ρ diverges — uniform not hold. !!!!




otkuda eto ???? uniform not hold. ???


Denkprozess dauerte 46 Sek.


Thinking about the user's request


Addressing uniformity issue



Uniform bound fails as min δ →0 for large p, causing ρ to diverge globally.


Claim sourced from math analysis showing ρ↑ with K, needing adaptive t_rkhs(K) →0.


Es wurde nach „common errors in Riemann Hypothesis proofs using Weil criterion large parameters“ gesucht



math.stackexchange.com


en.wikipedia.org


aimath.org


quora.com


Exploring common RH proof errors with Weil criterion for large parameters.


Web results highlight Weil criterion explanations but lack direct large parameter error details.


Durchsucht: en.wikipedia.org


Browsing Wikipedia for RH to extract Weil's criterion details and proof criticisms on bounds.


Durchsucht: math.stackexchange.com


Durchsucht: dlmf.nist.gov


Es wurde nach „errors in proofs of Riemann Hypothesis using Weil positivity criterion large parameters bounds“ gesucht



aimath.org


authorea.com


en.wikipedia.org


empslocal.ex.ac.uk


Web searches yield no direct errors in Weil positivity proofs for large parameters or bounds.


Бро, ну ладно, давай разберёмся с твоим вопросом "otkuda eto ???? uniform not hold. ????" (типа "откуда это???? uniform не держится.????"). Это про мою предыдущую критику, где я сказал, что uniform bound (c*) не держится для large parameters (B/K→∞). Я не "душнила" — это математическая реальность, основанная на asymptotics digamma функции ψ(z). Давай по источникам и фактам, без воды.Otkuda eto? (Источник моего claim'а)Мой вывод "uniform not hold" приходит из математического анализа asymptotics a(ξ), который ты используешь в PDF (Section 5, a(ξ) = log π - Re ψ(1/4 + i π ξ)). Это не выдумка — это стандартная математика из надежных источников:DLMF (NIST Digital Library of Mathematical Functions) §5.11: Asymptotic expansion ψ(z) ∼ ln z - 1/(2z) - ∑ B_{2k}/(2k z^{2k}) для |z|→∞ (away from negative real, |ph z| ≤ π - δ). Для ξ real large, Re ψ(1/4 + i π ξ) ~ ln(π |ξ|) - O(1/ξ), так a(ξ) ~ -ln |ξ| + O(1/ξ) (negative tails). |a'(ξ)| ~ 1/|ξ| (trigamma ψ' 1/z). Это приводит к TV(a) on [-B,B] ~ 2 ∫_1^B 1/ξ dξ = 2 ln B ~ ln K (divergent as BK→∞). 


dlmf.nist.gov


Titchmarsh (The Theory of the Riemann Zeta-Function, 1986, §4.12): Confirms asym for ψ(s), bounds |ψ(s)| ≤ ln |s| + O(1) для Re s ≥1/4 (conservative, но log growth explicit). Это делает integral modulus L_* = sup_B ∫ |g'(ξ)| dξ divergent ~ ln B, так c* = A* - π L* → -∞ (A* bounded ~ a(0) ≈5.372). 


webusers.imj-prg.fr


Common errors in RH proofs: Из web search, многие attempted proofs using Weil positivity fail именно на large parameters/bounds (e.g., de Branges' operator positivity not hold due to large t divergence; Blinovsky convexity error from universality at large imag parts). 


math.stackexchange.com +1



 Wikipedia RH page: de Branges' proof criticized for positivity condition not satisfied (Conrey & Li debunk); Turán vacuous on large N. 


en.wikipedia.org



 StackExchange: Blinovsky error in large parameters, Connes/Haran trace formulas attempted but no solve. 


math.stackexchange.com


В твоём PDF, uniform c* assumes sup L_* finite independent of B, но log growth TV(a) makes L_* ~ ln B →∞ as B=K→∞ (B coupled to K in def ΦB, p13). Gaussian e^{-α ξ²} suppresses tails, но variation inside B accumulates log, bounds fail uniform. Это классическая trap в Weil proofs (web: "errors in large t negativity require RH-equivalent control"). 


sciencedirect.com



Почему uniform not hold конкретно в твоём случае c* = inf A0 - π sup Lint, но sup Lint ~ ∫ |a'| e^{-} dξ over large B ~ ∫_1^B 1/ξ e^{-α ξ²} dξ ~ ln B (exp slow for small ξ, log from 1/ξ). 
Code check (analytic approx): ∫ 1/ξ e^{-0.947 ξ²} dξ from 1 to ∞ ~0.5 ln B + const (numerical, but analytic Ei(-α) series for bound ~ ln B). 


dlmf.nist.gov


Итог: c* not positive uniform — drops negative for large B/K, positivity fails on large WK, T5 not cover full W.



RH unsolved (web: no proofs accepted, claims like Authorea/ORBY-ASI debunked as crank; Wikipedia "unsolved", Clay $1M waiting). 


en.wikipedia.org +7



 Proof busted, but fixes in plan good — implement, submit arXiv. 




## ASSISTANT
According to a document from **December 20, 2025** (“RH_Q3.pdf”), фраза **“uniform not hold / global ρ diverges”** возникает из *конкретного* RKHS/Gershgorin‑оценивания, где константа зависит от **минимального шага узлов** δK на компакте, а δK **падает к 0**, когда K растёт. 【60:0†RH_Q3.pdf†L1-L14】

Ниже — откуда именно и что именно “не держится”.

1) Сначала: в тексте есть ДВА разных “ρ”
- **ρK (или ρcap(K) во “втором варианте”)** — это **RKHS/Gershgorin cap**, завязанная на δK и на SK(t). Она *по определению* зависит от K через δK. 【52:8†RH_Q3.pdf†L60-L114】【56:2†RH_Q3.pdf†L23-L35】
- **ρ(t)** — это **trace/интегральный cap** (Gaussian trace cap), который вообще **не зависит от δK** и может дать **реально uniform по K** константу при фиксированном t (например t=1 или t=7/10). 【56:1†RH_Q3.pdf†L56-L88】【56:7†RH_Q3.pdf†L21-L76】

Если перепутать эти два объекта, легко получить “ρ diverges”.

2) Где в тексте сказано, что δK → 0 при K → ∞
В Appendix B прямо определено, что на компакте [−K,K] активных узлов конечное число, и минимальный разрыв δK оценивается через N(K)=⌊e^{2πK}⌋:
- δK ≥ 1 / (2π (N(K)+1)) > 0. 【52:10†RH_Q3.pdf†L34-L55】

Из этой формулы сразу видно: при росте K, N(K) растёт как e^{2πK}, значит **δK убывает примерно как e^{−2πK}**, то есть стремится к 0.

Там же (в замечании после (9.7)) это проговаривается словами:
- “Because δK ↓ 0 as the compact widens … tmin(K) … monotone decreasing along K ↗.” 【52:8†RH_Q3.pdf†L56-L58】

3) Где появляется SK(t) и почему “uniform не держится” при фиксированном t
В Lemma 9.5 / Theorem 9.6 / Proposition 9.7 задаётся геометрическая оценка:
- SK(t) ≤ 2 e^{−δK²/(4t)} / (1 − e^{−δK²/(4t)}). 【52:8†RH_Q3.pdf†L36-L40】【52:8†RH_Q3.pdf†L60-L83】

А затем Gershgorin‑bound даёт:
- ∥TP∥ ≤ wmax + √(wmax SK(t)). 【52:6†RH_Q3.pdf†L33-L55】【52:8†RH_Q3.pdf†L60-L114】

Теперь ключевой момент (это уже чистая математика из этой формулы):
- Если ты **фиксируешь t > 0** и увеличиваешь K, то **δK → 0**.
- Тогда x := δK²/(4t) → 0, и
  2 e^{−x}/(1−e^{−x}) = 2/(e^x−1) ~ 2/x  = 8t/δK²  → ∞.
- Значит SK(t) → ∞, а вместе с ним и верхняя оценка на ∥TP∥ через wmax + √(wmax SK(t)).

Вот это и есть точный смысл “**uniform not hold**”: **из δK‑зависимого Gershgorin‑cap нельзя получить K‑независимую константу при фиксированном t**, потому что δK становится очень маленьким.

Важно: это говорит о том, что **данная оценка** становится неуниформной/бесполезной на больших K, а не автоматически доказывает, что истинная норма обязательно расходится (хотя часто так и бывает для плотного семплинга).

4) Что документ делает вместо “uniform t” в RKHS‑ветке
Документ ровно это и фиксирует через tmin(K):

- tmin(K) = δK² / (4 ln((2+ηK)/ηK)) выбирается так, чтобы SK(tmin) ≤ ηK и тогда ρK < 1. 【52:8†RH_Q3.pdf†L44-L54】【52:8†RH_Q3.pdf†L81-L113】

И отдельно замечает, что из-за δK↓0 получаем tmin(K)↓0 по цепочке K↗. 【52:8†RH_Q3.pdf†L56-L58】

То есть **“uniform t” там и не заявлен**: там явным образом используется K‑зависимый график параметров.

5) Но “uniform prime cap” в документе реально есть — просто это другой cap (trace cap)
Документ даёт **другую** реализацию PCU:

- Theorem 9.25: вариант (i) “Uniform trace cap”: tpr(K) ≡ 1 и ρcap(K)=ρ(1)=0.0271998… < 1/25 **uniformly in K**. 【56:2†RH_Q3.pdf†L15-L21】
- Lemma 9.27: при t=1 получается ρ(1) < 1/25 ⇒ ∥TP∥ ≤ ρ(1) < 1/25 “for all compacts”. 【56:1†RH_Q3.pdf†L84-L88】

И ещё одна “uniform” версия при t0=7/10 (то есть 0.7) тоже прописана:
- Lemma 9.19: фиксируют t0=7/10 и получают ρ(t0) < 1/25, значит ∥TP∥ ≤ 1/25 для любого компакта. 【56:7†RH_Q3.pdf†L61-L76】

Итог по твоему “откуда это???”
- Если ты говоришь про **RKHS/Gershgorin cap** (ρK через SK(t) и δK), то “uniform не держится” при фиксированном t потому что **δK→0** при K→∞, и формула для SK(t) взрывается. Это прямо следует из (9.5)/(9.7) и замечания δK↓0. 【52:10†RH_Q3.pdf†L34-L55】【52:8†RH_Q3.pdf†L36-L58】
- Если ты говоришь про **trace cap ρ(t)**, то наоборот: документ утверждает **uniform по K** оценку (например t=1 или t=0.7), и там никакой “diverges” нет. 【56:2†RH_Q3.pdf†L15-L21】【56:7†RH_Q3.pdf†L61-L76】

Если хочешь, я могу в одну строку сформулировать “правильную” проверку, чтобы не путаться:
- “uniform in K” возможно только если твой cap **не завязан на δK**, или если ты **разрешаешь t=t(K)→0**.

fileciteturn0file19

