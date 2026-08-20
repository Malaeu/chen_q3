# Fuchs 1964 (JMAA 9, 317–330) — verified theorem-usage cards

Source PDF: `pdfs/fuchs_1964_bandlimited_eigenvalues.pdf`
sha256: `f86d5759248729fa56a30d2c9231c8acb9dd5c9cdea6a320acd7adf821c29cb3`
DOI: 10.1016/0022-247X(64)90017-4 · PII 0022-247X(64)90017-4 (title metadata of the file)
W. H. J. Fuchs, "On the Eigenvalues of an Integral Equation Arising in the Theory of
Band-Limited Signals", submitted by Peter Lax.

Owner supplied the PDF 2026-08-20 through university access (paywalled, no open copy:
Unpaywall `is_oa: false`).

Text quality note: the file carries an Acrobat-Capture OCR layer from 2003. Formulas are
partly mangled. Every constant quoted below was read twice — once in the theorem head and
once in the closing lines of its proof — and the two readings agree. Places where OCR
remains unreadable are named explicitly under NOT READ.

---

## Theorem 1 (eigenvalue defect of the sinc-kernel equation) — p. 319
VERBATIM (OCR, reconstructed; constants confirmed against the end of the proof, p. ~330):
"THEOREM 1. Let λ_0 > λ_1 > λ_2 > λ_3 … be the eigenvalues of the integral equation (1).
Then
    1 − λ_n ~ 4 π^{1/2} 8^n (n!)^{-1} a^{2n+1} e^{-2a²},   a → ∞;  a² = c."

Confirming lines from the closing computation of the proof:
"= 4 π^{1/2} (n!)^{-1} 8^n … a^{2n+1} … e^{-2a²} (1 + o(1))".

The theorem head OCR renders `8^n` as an unreadable glyph cluster; the proof end renders it
as `8"` twice. The reading `8^n` (not `2^n`) is therefore the one taken.

K7-TAG: THEOREM (proved in this paper; Lemmas 1–5 of §§II–IV are its machinery)

SETUP THE THEOREM SPEAKS ABOUT (paper's own equations, p. 317–318):
- equation (1): `λ φ(y) = (1/π) ∫_{-c}^{c} φ(x) · sin(x−y)/(x−y) dx`, `|y| < c`;
- substitutions `c = a²`, `x = a s`, `y = a t`, `φ(as) = f(s)` bring (1) to (2) on `L²(−a, a)`;
- these `λ_n` are the *energy-concentration* eigenvalues: by (3)–(4), with `F = f_n`
  normalized and `G(t) = (2π)^{-1/2} ∫_{-a}^{a} F(s) e^{ist} ds`, one has
  `λ_n = ∫_{-a}^{a} |G(t)|² dt`;
- by (1.3), `i^n μ_n f_n(t) = ∫_{-a}^{a} f_n(s) e^{ist} ds` — the finite Fourier transform
  eigenrelation, kernel `e^{ist}`, window `(−a, a)`;
- combining the two previous lines with the normalization (1.2) gives, inside the paper's own
  conventions, `λ_n = |μ_n|² / (2π)`.

USED IN Q3 FOR: floor F72.3 of the L73.2 wall — `FiniteFourierEigenvalueDefectRate`, the
second analytic core named by the judge (verdict REQ-F, commit 835d7e97). That floor asks for
`|1 − χ_n| ≤ C λ^{-2}` for the selected modes.

WHAT IT GIVES US: far more than the floor asks. The defect vanishes **exponentially** in the
time-bandwidth parameter, `e^{-2c}`, not polynomially. Any polynomial bound `C·λ^{-2}` follows
a fortiori once the parameter crosswalk is fixed and `a → ∞` along our schedule.

COVERAGE OF OUR TWO MODES: the theorem is stated for every `n = 0, 1, 2, 3, …`, with the
implicit constant `K` allowed to depend on `n` (stated right below the theorem head: "the
letter K will stand for a positive number independent of a, but possibly depending on n").
Both `n = 0` and `n = 4` are therefore covered. The judge's fallback question — "ремонт через
eigenvalue ordering, если n=0 не покрыт" — does not arise.

WHAT IT DOES NOT GIVE: nothing about the *shape* of the modes. Theorem 1 is an eigenvalue
statement only. The spheroidal-to-Hermite mode rate (floor F72.1) is Meixner–Schäfke Satz 9,
cited by Fuchs as [6, Chap. 3, Theorem 9, p. 243] — quoted, not reproved here.

CAVEAT — THE CROSSWALK IS NOT YET FIXED, AND IT IS A UNIT QUESTION:
Our `finiteFourierKernel x y = exp(i · 2π · x · y)` on `[−λ, λ]`
(`ProlateSourceRegularity.lean:19`) carries `2π` in the exponent; Fuchs's kernel `e^{ist}` on
`(−a, a)` does not. So `a` is **not** our `λ`, and `λ_n` (Fuchs) is **not** our `chi_n`. Two
conversions stand between them, both unverified from here:
  1. window/parameter: our `γ = 2π λ²` (the judge's parameter lock) against Fuchs's `c = a²`;
  2. eigenvalue: Fuchs's `λ_n = |μ_n|²/(2π)` against our real `chi0`, `chi2`, which are
     eigenvalues of the *transform*, not of its square.
Writing the rate for `chi` before both conversions are proved would repeat the REQ-E failure
exactly — there the literal packet turned out to carry `1/4` of the target. The constant is
not to be guessed here.

WHY OUR TWO MODES ARE REAL-EIGENVALUE MODES (context, from (1.3)): the transform eigenvalue
carries the factor `i^n`, which equals `+1` for `n ≡ 0 (mod 4)`. Our selected degrees are
`n = 0` and `n = 4`. This is consistent with the project storing `chi0 chi2 : ℝ`.

---

## Theorem A (known results collected) — p. 319–320
VERBATIM (OCR, partial): "THEOREM A. The eigenvalues of (2) form a denumerable set λ_0, λ_1, …
They satisfy 1 > λ_0 > λ_1 > λ_2 … > 0. To each λ_j belongs a real-valued eigenfunction f_j(t),
unique up to a factor, and such that ∫_{-a}^{a} f_j(t) f_k(t) dt = δ_{jk}. The function f_j(t)
is even if j is even, odd if j is odd."

Further items of the same theorem, as printed:
- the differential operator `L y(t) = (d/dt)[(t² − a²) dy/dt] + a² t² y` (1.4), with eigenvalue
  problem `L y = χ y` on `(−∞, ∞)`, `y` continuous, eigenvalues `0 < χ_0 < χ_1 < …` and
  eigenfunctions `f_0, f_1, …`;
- `χ_n = (2n + 1) a² + O(1)` as `a → ∞` (1.6);
- the prolate identification, in the notation of [6] (Meixner–Schäfke):
  `f_n(t) = f_n(t, a) = ((2n+1)/…)^{1/2} · ps_n(t/a; a⁴)` (1.7, normalizing prefactor partly
  unreadable) and `χ_n = χ_n(a) = λ_n(a⁴) + a⁴` (1.8);
- the Hermite limit, from the same Meixner–Schäfke theorem:
  `f_n(t, a) = (2^n n! π^{1/2})^{-1/2} · h_n(t) + O(a^{-3/2})` uniformly.

K7-TAG: SURVEY (Fuchs attributes these to [3] and [6]; only (1.6) and the final remark are
argued here). For us this is a pointer, not a supplier.

USED IN Q3 FOR: two things, both indirect.
1. It names the exact bridge our floor F72.0B needs: `f_n(t,a) = const · ps_n(t/a; a⁴)`, i.e.
   the literal Meixner–Schäfke representative, with the spheroidal parameter appearing as
   `a⁴ = c²`.
2. The last displayed line is the *shape* asymptotic toward Hermite functions with an
   `O(a^{-3/2})` error — the same Meixner–Schäfke source that F72.1 must port, seen through
   Fuchs's normalization.

CAVEAT: the exponent `a⁴` here belongs to Fuchs's `a`, not to our `λ`. Under the pending
crosswalk this is the same object as CCM's `γ²`, but that identification is precisely what
F72.0A/F72.0B must prove, not assume. The prefactor in (1.7) and the `O(a^{-3/2})` uniformity
region are OCR-damaged in this copy — see NOT READ.

---

## NOT READ / NOT VERIFIED FROM THIS COPY
- The exact normalizing prefactor in (1.7) — OCR gives `(2n 7) + ’ “’ 2%`, unreadable.
- The precise uniformity region of the Hermite asymptotic quoted after (1.8).
- Lemmas 1–5 (§§II–IV): the machinery of the proof was not read line by line; only the closing
  computation was read, to confirm the constants of Theorem 1.
- Meixner–Schäfke [6] itself (Chap. 3, Theorem 9, p. 243 — "Satz 9") is **not** in this file.
  It is cited by both Fuchs and CCM. Floor F72.1 needs that source; obtaining it is a separate
  acquisition, still open.
- Reference list numbering [1]–[6] was not transcribed; [3] and [6] are the two that matter and
  are identified only by Fuchs's own in-text description.

---

## DERIVED — проектная форма (scope-lock судьи, REQ-H, коммит 3abb8613)

Открытый пункт карточки — crosswalk — закрыт судьёй на бумаге из наших же определений.
Здесь записан результат; вывод целиком лежит в
`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_H_FUCHS_F72_3_SCOPE_LOCK_2026-08-20.md`.

ПЕРЕСЧЁТ ОКНА (масштаб `r = √(2π)`):

```
a = √(2π)·λ        Fuchs c = a² = 2πλ² = наша γ
U_λ(h)(s) = (2π)^(−1/4)·h(s/√(2π))          — унитарная перенормировка
F_a(U_λ h) = √(2π)·U_λ(T_λ h)               — сплетение операторов
```

ПЕРЕСЧЁТ СОБСТВЕННОГО ЧИСЛА (две разные категории, как и подозревалось):

```
√(2π)·chi0_Q3 = μ_0        Λ_0 = chi0_Q3²
√(2π)·chi2_Q3 = μ_4        Λ_4 = chi2_Q3²      ← наш chi2 = степень 4 Fuchs
```

ИТОГОВЫЕ ПРОЕКТНЫЕ АСИМПТОТИКИ:

```
1 − chi0_Q3 ~ 2√2·π·λ·e^(−4πλ²)
1 − chi2_Q3 ~ (2¹⁴/3)·√2·π⁵·λ⁹·e^(−4πλ²)
слабый выход F72.3:  |1 − chi0_Q3|, |1 − chi2_Q3| ≤ C·λ⁻² при больших λ
```

ТРОЙНАЯ СХОДИМОСТЬ на префактор `(2¹⁴/3)√2·π⁵`: цитата Groskin из CCM §6.4
(`GROSKIN_TWF_USAGE_CARDS.md`, там сказано, что префактор выведен именно из теоремы
Fuchs и потому строгий), независимое прочтение судьёй страницы 30 CCM, и его же
вывод через crosswalk из Theorem 1. Три пути дают одно.

ЧЕМ ЭТО БЫЛО БЫ, ЕСЛИ БЫ УГАДЫВАЛИ (дискриминатор судьи):
- взяли бы `a = λ` → экспонента `e^(−2λ²)` вместо `e^(−4πλ²)`;
- взяли бы `Λ = chi` → ведущая константа вдвое больше верной.
Оба варианта прошли бы «на глаз» и умерли бы позже. Воздержаться было правильно.

ЦЕНА ЭТАЖА F72.3 после замка: неопределённость охвата 1/10, точный Lean-crosswalk 3/10,
слабое следствие при формальном входе Fuchs 2/10. Полный переспроф Fuchs в Lean — 8/10,
и он НЕ требуется. Главной стеной L73.2 остаётся F72.1 (Meixner–Schäfke Satz 9).
