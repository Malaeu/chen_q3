# Andrews, Independent Reproduction of the CCM Zeta Spectral Triple — usage cards

Source PDF: `pdfs/andrews_ccm_reproduction_2026.pdf` (скачан 2026-08-07 с Zenodo,
6 страниц, прочитаны 1–3).

Полное название: Ronnie Andrews Jr. (Team Xcelerator Inc.), "Independent Reproduction and
Convergence Analysis of the Connes–Consani–Moscovici Zeta Spectral Triple", **June 2026**.
DOI: `10.5281/zenodo.20427500` · лицензия CC BY-NC-ND 4.0 · исходники:
`10.5281/zenodo.20427502`, GitHub `TeamXcelerator/ccm-reproduction-and-convergence` +
`TeamXcelerator/xcelerator-toolkit`.

**Класс работы:** независимое численное воспроизведение, не доказательство. Расширяет
результат CCM с 55 до **999 совпадающих знаков** на первом нуле. Работа передана
Х. Московичи (соавтору CCM) и переслана А. Конну на рецензию.

---

## 1. ⭐ Пространство и базис — буквально наши

§2.1, стр. 2, дословно:

```
H_λ = L²([λ⁻¹, λ], du/u),        L = 2 ln λ
V_n(u) = (1/√L)·e^{2πin·ln(λu)/L},     n ∈ {−N, …, N}
```

**Соответствие с нашими объектами — тождественное, не аналогия:**

| Andrews / CCM | Наше | Где у нас |
|---|---|---|
| `H_λ = L²([λ⁻¹,λ], du/u)` | `H_m = Lp ℂ 2 (dStar.restrict (I_m i))` | `D0KTrialStage1.lean:44` |
| `λ` | `lambda_m i = √(i.m)` | `D0KTrialStage1.lean:19` |
| `L = 2 ln λ` | `L_m i = log i.m` | совпадает при `λ = √m` |
| `V_n(u) = L^{−1/2} e^{2πin ln(λu)/L}` | `V_n_m i n` | `D0KTrialStage1.lean:60` |
| `n ∈ {−N,…,N}` | `modeSet i = Icc (−N) N` | `D0CanonicalApproximation.lean:27` |

> **Закрывает фальсификатор R9 (индексный кросс-волк).** Их `V_n` одиночный, наш `V_n_m`
> двойной — но их **два параметра** `(λ, N)` есть ровно наша пара `PairIndex (m, N)`.
> Это одно семейство в двух нотациях, а не два семейства. Формально предъявить всё ещё
> обязаны мы, но риск «другое семейство» снят.

## 2. ⭐ Явная формула матрицы — то, чего мы просили у M1

§2.1, стр. 2:

```
τ_{n,m} = W_{0,2}(V_n,V_m) − W_R(V_n,V_m) − Σ_{k=p^j, k ≤ λ²} (log p / √k) · q(V_n,V_m)(log k)
```

где `W_{0,2}` — **замкнутая ранг-два** полюсная поправка; `W_R` — архимедов (гамма-фактор)
вклад через квадратуру Гаусса–Лежандра; сумма по степеням простых кодирует фон Мангольдта
`Λ(k) = log p` при `k = p^j`.

`QW_λ` — **вещественная симметричная** матрица `(2N+1) × (2N+1)`.

> Совпадает с донесением разведки по CCM (см. `maps/RECON_2026-08-07_CCM_ORIGINAL.md` §1.3)
> и подтверждает его независимо. Для нашего инструмента: `K = τ`, `G = I` (базис
> ортонормирован), `hK : K.IsHermitian` выполняется — матрица вещественная симметричная.

## 3. ⭐⭐ Чётность подтверждена эмпирически — наша гипотеза `hJq`

Abstract и §1 пункт 4, дословно:

> "The smallest eigenvector's even-symmetry (CCM's Step 1 hypothesis) holds at **every
> above-floor configuration tested up to λ²=1200, HP-2000**; the forced-even projection is
> **empirically unnecessary** — the natural eigenvector converges to the same even vector and
> produces **bit-identical eigenvalues**."

§3 пункт 1: итерация автодетектит уход собственного вектора в нечётность через
`‖ξ − γξ‖/‖ξ‖` (γ — отражение индекса) и применяет чётную проекцию только при
необходимости — **это no-op при каждой протестированной конфигурации выше пола точности**.

> Прямо кормит гипотезу `hJq : J *ᵥ q = q` нашего инструмента, а также входу A программы
> Конна. Это **эмпирика, не теорема** — но эмпирика на 1200 значениях `λ²` с точностью 2000
> знаков, и с явно названным механизмом ложных срабатываний (недостаточная рабочая точность
> ниже пола `ε_N` порождает артефакты смешанной симметрии).

## 4. ⭐ Публичный кэш τ-матриц — матрицу можно скачать, а не считать

§3.1:

> "on-disk caches for the two dominant precomputed quantities: the Gauss–Legendre
> nodes/weights … and the **τ-matrix** at a given `(λ², N, precision_bits)`. Both caches are
> keyed on the construction parameters, validated against structural identities on every
> load, and hosted in **dedicated public cache repositories** (GL nodes, τ-matrices, Weil
> eigenvectors) with a deterministic remote-fetch tier (DynamicFetch)."

> "All configurations reported in this paper, including the largest (`λ²=1200, N=970`,
> HP-2000: τ serializes to ~7 GB), have their τ-cache fixtures committed to the public cache
> repository and are fetched on demand. **No configuration requires a fresh τ-build to
> reproduce.**"

> **Это меняет стоимость хода 1.** Нам не нужно собирать матрицу с нуля: `(G, K)` берутся из
> публичного кэша, остаётся построить `q`, подобрать `β, τ` и проверить `M ⪰ 0`.

## 5. Малые размеры уже работают

Abstract: "a **21×21 matrix from 6 primes** already yields 21.585 matching digits."

> Проверять сертификат можно начиная с `21×21`. Это делает ход 1 задачей на часы, а не на
> смену: наши `PSD_PenaltyCertificate.lean` рассчитаны на `23×23` рациональные SOS/LDL —
> **тот же порядок размера**.

## 6. Поведение сходимости — двухрежимное по N

Abstract:

> "accuracy exhibits **two-regime behavior in basis size N** (linear growth, then
> **saturation at the Weil eigenvalue ceiling ε_N**); `ε_N` decays super-exponentially with
> **prime count** (hundreds of digits per doubling at fixed `N/√(λ²) ≈ 28`); and accuracy
> grows monotonically with `λ`, controlled directly by `ε_N`."

> **Важно для нашего вопроса о переносе.** Точность растёт по `N` линейно, потом **насыщается**
> на потолке `ε_N`, а сам `ε_N` управляется числом простых (то есть `λ²`), не `N`.
> Значит режим «растить `N` при фиксированной `λ`» имеет предел — что прямо касается
> дискриминатора `β_N` из `maps/ZOOM_2026-08-07_GAP_TRANSFER_THROUGH_GALERKIN.md`:
> **прогон `β_N` надо ставить в линейном режиме, до насыщения**, иначе будем мерить потолок
> точности, а не математику. Отношение `N/√(λ²) ≈ 28` — их рабочая точка.

## 7. Чего здесь НЕТ

**Ни оценки спектральной щели, ни второго собственного значения.** Проверено чтением
abstract, введения и §2–3; вся работа про **наименьшее** собственное значение `ε_N` и про
точность нулей.

> **Целина по `Δ_λ` подтверждается третьим независимым чтением** (после самой CCM и
> Groskin). Для пакета: M2 усиливается, но не закрывается — остаётся закрытый
> «Quantitative Convergence Law» того же автора.

## 8. Открытое по этой работе

1. Прочитаны страницы 1–3 из 6. **§4 (Convergence Analysis) и таблицы не читаны** — там,
   по оглавлению, §4.7 «convergence sweeps» и §4.8 про чётность. Дочитать при постановке хода 1.
2. Второй, **закрытый** Zenodo того же автора — «A Quantitative Convergence Law for the CCM
   Zeta Spectral Triple». По названию — закон сходимости спектра к нулям, не щель, но до
   вскрытия честно говорить «целина ×3, не ×4».
3. Публичные кэш-репозитории названы, но URL в прочитанных страницах не приведён — искать
   в §3.1 сносках или в GitHub-репозитории toolkit.

---

**Провенанс.** PDF скачан 2026-08-07 с `https://zenodo.org/records/20427500/files/paper_v2.0.pdf`,
342 245 байт, 6 страниц. Прочитаны напрямую страницы 1–3. Всё выше — из прочитанного;
пункты про §4 помечены как непрочитанные.

Внести в `references.bib` и Zotero — отдельным шагом.
