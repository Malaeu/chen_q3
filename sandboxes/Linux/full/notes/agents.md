# Agent Operating Notes

- Default to migrating/locating critical artifacts locally before asking for decisions; treat missing JSON/verification data as blockers to resolve autonomously.
- If единственный разумный шаг очевиден, выполняю его без уточнений; вопросы поднимаю только по реально неоднозначным или ревиальным (explicitly requested) ситуациям.

## Progress Log — Q3 Track (Window → Weil bridge)

- 3.3.3.a Grid builder + membership
  - Added `FH.gridCenters`, `FH.assembleParams`, and `FH.assemble_mem_span` in `lean/RHFormalization/WeilCriterion.lean`.
  - Purpose: safe, finite builder that packs Fejér×heat atoms into a `WeilClass` and proves membership in `fejer_heat_span K` when `|τ_i|≤K`.

- 3.3.3.b Oscillation + parameter pickers (defs only)
  - Added `window`, `near`, `oscOn`, `chooseN/chooseB/chooseT` in `lean/RHFormalization/WeilCriterion.lean`.
  - Purpose: deterministic selectors for grid size/hat width/heat time; oscillation functional on `[-K,K]` for uniform‑error control.

- 3.3.3.c Fejér×heat density — scaffold
  - Inserted theorem `fejer_heat_density` with parameter selection and span‑membership wired; one local TODO remains for the final uniform‑error bound (to be closed in 3.3.4.2–3.3.4.4).

- 3.3.4.1 Uniform modulus on the window
  - Added lemma `uniform_modulus_on_window`: Heine–Cantor on `[-K,K]` → δ(ε) for `‖Φ(x)−Φ(y)‖` when `|x−y|≤δ`.

Next (3.3.4.2 → 3.3.4.4)
- 3.3.4.2 PWL hat error: prove that PWL interpolation by Fejér hats on the grid achieves `≤ ε/2` on `[-K,K]` for suitable `B=K/N`.
- 3.3.4.3 Heat smoothing error: bound deviation from multiplying by `heatR t` with `t=chooseT(K,ε)`.
- 3.3.4.4 Glue: close the single TODO in `fejer_heat_density` and finish the window density step end‑to‑end.

## Tech Tree — FFT/IFFT Unlocks (Engineering side)

What’s unlocked now
- IFFT render of G(θ) on large grids (no cos/sin matrices), fast certificate validation (flag `--grid-method ifft`).
- Adaptive Q growth with heartbeat; reuse of `ĝ(P_A)` while tuning `t_φ` (separate `ĝ(S_M)`).
- B×M sweeps for δ_cert surfaces in minutes.

Low‑effort, high‑impact next steps
- Multi‑resolution minimum: moderate Q IFFT, then local zoom via zero‑padding around θ_min without recomputing `ĝ`.
- Auto‑tuning (α, t_arch, t_φ) for maximizing δ_cert, reusing `ĝ(P_A)`.
- Fast λ_min for huge M: Lanczos + Toeplitz‑via‑FFT (circulant embedding) to check PSD without explicit matrices.

Mid‑term (formal/compact certificates)
- Fejér–Riesz factorization: produce H with G(e^{iθ}) = |H(e^{iθ})|² → compact SOS certificate (store H; verify by convolution). Add rational rounding for archival.
- Interval certificates for `ĝ_k`: interval IFFT for G(θ) and δ_iv > 0.
- NUFFT for S_M at large B (many nodes).
- Compressed cert pack: store `ĝ` or H + checksums; validator reconstructs and verifies in seconds.

## Build/QA automation (Make/latexmk)

- Что такое `qa`: это make-цель в `Q3_paper/Makefile`. Делает `clean` → `latexmk -bibtex RH_Q3.tex` → падает, если в логе есть `Undefined reference` или `Label(s) may have changed`.
- Запуск: для `make -C Q3_paper qa|pdf|bib|bundle` сразу проси повышенные права (sandbox escalate), потому что `latexmk` пишет кучу временных файлов.
- Если первая попытка вернулась с `Operation not permitted`, автоматически повторить ту же команду с эскалацией и пометкой `retry: escalated`.
- Эти правила обязательны для сборок перед ревью/архивацией; не меняют содержимое статьи, только артефакты сборки.

### Full Finder Snapshot (Big dump на GitHub)

Когда нужно «залить всё, что вижу в Finder», действуем так:

1. **Зайди в корень репозитория** (`cd RH_2025_V3_October`).
2. **Заморозь вложенные Git-репы**, чтобы GitHub не ругался и файл <100 MB:
   ```bash
   find Q3_paper/notes -path '*/.git' -type d -prune -exec bash -c 'mv "$0" "${0}.embedded"' {} \;
   ```
   (это переименует `.git` → `.git.embedded`; их можно вернуть после пуша тем же приёмом, заменив `mv "$0" ...` на `mv "${0}.embedded" "$0"`).
3. **Добавь всё в индекс**: `git add -A`.
4. **Коммит**: `[DOCS] Snapshot full Finder state (… )` с описанием (что в снапшоте, упоминание больших папок вроде Lean, Chats_Projekte, pdfs).
5. **Push**: `git push origin bib-audit-q3` (или нужную ветку). Если появится предупреждение про файлы >80 MB — это нормально, главное не превышать 100 MB. При необходимости подключай Git LFS.
6. **(Опционально)** после пуша верни `.git.embedded` обратно в `.git`, чтобы локально можно было снова пользоваться вложенными репами.

Такое снепшот-поведение теперь «дефолт»: если просит «full finder-state», 바로 выполняем процедуру выше без лишних вопросов.
