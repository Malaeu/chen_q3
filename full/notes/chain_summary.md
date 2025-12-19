# Track B Chain — Archimedean → Toeplitz → RKHS → T5 → Weil

## 0. Нормализация (T0)

* **Что делаем:** приводим тестовые функции к guinand–Weil нормализации, чтобы квадратичная форма $Q$ совпадала с критерием Вейля.
* **Где смотреть:** `sections/T0.tex`, `sections/T0_AD_fix.tex`.
* **Ключевые факты:**
  * Proposition \ref{prop:T0-GW} — Guinand–Weil crosswalk.
  * Lemma \ref{t0:lem:T0} — нормализация $Q$.
* **Источники:** Guinand (1955), Weil (1952).

## 1. Локальная плотность (A1′)

* **Что делаем:** Fejér×heat аппроксиманты дают плотность положительных генераторов на каждом $W_K$.
* **Где смотреть:** `sections/A1prime.tex`.
* **Ключевые факты:**
  * Theorem \ref{a1:thm:A1-local-density}.
  * Lemma \ref{lem:a1-fixed-t-density} — фиксированный heat-scale.
* **Источники:** классические результаты по ядрам Fejér и heat; арXивная база не нужна.

## 2. Непрерывность (A2)

* **Что делаем:** оцениваем Lipschitz-модуль квадратичной формы $Q$ на компактных $W_K$; контролируем хвосты.
* **Где смотреть:** `sections/A2.tex`.
* **Ключевые факты:**
  * Lemma \ref{lem:Q-local-finite}.
  * Lemma \ref{a2:lem:A2}, Corollary \ref{a2:cor:explicit-lip}.
* **Источники:** NIST DLMF (дигамма), стандартные интегральные оценки.

## 3. Toeplitz–Symbol Bridge (A3)

* **Что делаем:** строим архимедовый символ $P_A$, выводим положительный запас $c_{\mathrm{arch}}(K)$ и связываем его с Toeplitz-матрицей.
* **Где смотреть:** каталог `sections/A3/` — файлы `calibration.tex`, `arch_bounds.tex`, `rayleigh_bridge.tex`, `symbol_floor.tex`, `fejer_modulus.tex`, `matrix_guard.tex`, `local_positivity.tex`, `locks.tex`, `main.tex`.
* **Ключевые факты:**
  * Lemma \ref{lem:a3.lipschitz-explicit}, Proposition \ref{a3:prop:A0-minus-LA} — Lipschitz-модули.
  * Lemma \ref{lem:a3-core-lower-bound}, Corollary \ref{cor:a3-arch-floor-compact} — архимедовый запас.
  * Theorem \ref{thm:a3-rayleigh-identification}, Theorem \ref{thm:A3}.
* **Источники:** Böttcher (1907), Szegő (1952), Böttcher–Silbermann (2006).

## 4. RKHS и контроль prime-оператора

* **Что делаем:** оцениваем $\|T_P\|$ в reproducing kernel Hilbert space, избавляемся от любых табличных проверок. Сравниваем
  \[
    \rho_K = w_{\max} + \sqrt{w_{\max}}\,S_K(t_{\min}(K))
    \quad\text{и}\quad
    c_{\mathrm{arch}}(K).
  \]
  Это ключевой мост Archimedean ↔ prime.
* **Где смотреть:** `sections/RKHS/` — `core.tex`, `main.tex`, `prime_cap.tex`, `prime_trace_closed_form.tex`, `prime_norm_leq_rho.tex`, `weil_isometry.tex`.
* **Ключевые факты:**
  * Lemma \ref{lem:rkhs-energy}, Lemma \ref{lem:gram-min-eig-lb}, Proposition \ref{prop:operator-sandwich}.
  * Theorem \ref{rkhs:thm:rkhs-contraction}, Proposition \ref{prop:rkhs-schedule}.
  * Lemma \ref{pm:lem:rho-closed-form}, Proposition \ref{pm:prop:norm-leq-rho}.
  * Theorem \ref{thm:rkhs-tstar}.
* **Источники:** Aronszajn (1950), Berlinet–Thomas-Agnan (2004), Paulsen–Raghupathi (2016), Guth–Maynard (2024), Li (1997).
* **Почему "без таблиц":** ранние черновики Track B опирались на численные сетки (JSON/таблицы). Здесь все оценки $\rho_K$ выведены аналитически — грам-матрицы, Gershgorin, ранний блок + heat-хвост — никаких численных проверок.

## 5. IND/AB и prime cancellation

* **Что делаем:** закрываем остаточные «assume» для prime-блоков: measure domination, block induction, локальные перегоны.
* **Где смотреть:** `sections/IND_AB/` — файлы `MD_2_3_base_interval.tex`, `MD_2_3_constants.tex`, `IND_prime_step.tex`, `AB_infinity_closure.tex`, `parameter_recipe.tex`, `ind_schedule_table.tex`.
* **Ключевые факты:**
  * Theorem \ref{md:thm:MD23}, Lemma \ref{md:lem:IND-early-analytic}.
  * Theorem \ref{md:thm:INDprime}, Theorem \ref{md:thm:IND_block}.
  * Lemma \ref{md:lem:weight-cap}, Lemma \ref{md:lem:gap-compact}.
* **Источники:** Gershgorin (Varga 2004), Horn–Johnson (2013), NIST DLMF по логарифмическим оценкам.

## 6. D3 / Prime cancellation

* **Что делаем:** структурный контроль dispersion/cancellation на расширенных окошках (поддержка RKHS и Toeplitz блоков).
* **Где смотреть:** `sections/D3/` — `operator_bridge.tex`, `structural_PC_theorem.tex`, `amp_noD3.tex`.
* **Ключевые факты:**
  * Lemma \ref{d3:lem:D3-dispersion}, Theorem \ref{d3:thm:D3-contraction}.
  * Theorem \ref{thm:amp-noD3}.
* **Источники:** те же RKHS + Toeplitz главы.

## 7. Compact-by-compact transfer (T5)

* **Что делаем:** монотонно поднимаем $K$ и передаём positivity от одного компакта к следующим. Это «compact-to-global inheritance».
* **Где смотреть:** `sections/T5/` — `summary.tex`, `compact_transfer.tex`, `lemmas.tex`, `grid.tex`.
* **Ключевые факты:**
  * Lemma \ref{lem:T5p-grid}, Theorem \ref{thm:T5-compact}.
  * Lemma \ref{t5:lem:T5-dicts}, Theorem \ref{t5:thm:T5-transfer}.
* **Источники:** функциональный анализ (индуктивные пределы), плюс результаты секций A1′ и A2.
* **Комментарий:** доказано в явной форме; никаких «словесных» пропусков.

## 8. Weil linkage и Main theorem

* **Что делаем:** фиксируем предпоследний шаг: $Q(\Phi)\ge 0$ на $W$ ⇔ RH.
* **Где смотреть:** `sections/Weil_linkage.tex`, `sections/Weil_pack.tex`, `sections/Main_closure.tex`, финал в `RH_Q3.tex`.
* **Ключевые факты:**
  * Theorem \ref{thm:Weil-criterion}.
  * Theorem \ref{thm:Main-positivity}.
  * Theorem \ref{thm:RH}.
* **Источники:** Weil (1952), Conrey (2003) — обзор.

---

## PDFs (папка `pdfs/`)

* `Weil1952_mathnet.pdf` — оцифровка оригинальной заметки Вейля (Math-Net).
  * Добавить в Zotero: просто перетащи файл на запись «Weil1952» → прикрепится.
* Остальные (Edwards 1974, Montgomery–Vaughan 2007, Böttcher–Silbermann 2006 и т.д.) можно скачать скриптом `tools/annas_archive_downloader.js`:
  ```bash
  cd Q3_paper/tools
  npm install
  node annas_archive_downloader.js
  ```
  Скрипт складывает файлы в `../pdfs/`; имя файла совпадает с BibTeX-ключом. После этого перетаскиваешь в Zotero (Attach Stored Copy).

---