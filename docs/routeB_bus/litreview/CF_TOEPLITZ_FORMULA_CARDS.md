# Carathéodory–Fejér / Toeplitz-form formula cards

Scout output for the H2b engine (Connes–van Suijlekom finite route) and the Q3
`MatrixBridge`. Exact statements about Toeplitz forms and the
Carathéodory–Fejér structure of positive-semidefinite (PSD) Toeplitz matrices.

## Source PDFs
1. `docs/routeB_bus/litreview/pdfs/grenander_szego_1958.pdf`
   — U. Grenander & G. Szegő, *Toeplitz Forms and Their Applications*
   (Univ. of California Press, 1958; the copy is the Chelsea/CUP reprint), 248 PDF pages.
   Book-page ↔ PDF-page offset: **PDF page = book page + 5** (book p.3 "Preliminaries" = PDF p.8).
2. `docs/routeB_bus/litreview/pdfs/toeplitz_1911.pdf`
   — O. Toeplitz, "Zur Theorie der quadratischen und bilinearen Formen von
   unendlichvielen Veränderlichen. I. Teil: Theorie der L-Formen",
   *Mathematische Annalen* 70 (1911), pp. 351–376. 26 PDF pages, German, scanned.

**Extraction note.** Grenander–Szegő quotes come from the PDF text layer, which
inserts spurious spaces between letters; I have collapsed only that
letter-spacing OCR artifact and left wording, symbols and italics as printed.
Theorem statements below are the book's italicised statements. Toeplitz-1911
quotes were read from the page image (its text layer is too garbled to quote).

---

## CARD 1 — Definition of a Toeplitz form (L-form), original — toeplitz_1911, p.351

VERBATIM (German, page image, p.351):
"Zur Theorie der quadratischen und bilinearen Formen von unendlichvielen
Veränderlichen. I. Teil: Theorie der L-Formen. Von Otto Toeplitz in Göttingen.
Die vorliegende Arbeit enthält die Theorie einer speziellen Klasse von
quadratischen und bilinearen Formen unendlichvieler Veränderlicher, nämlich
derjenigen Formen, deren Koeffizientenschema den Typus

```
  c_0   c_1   c_2   c_3   c_4  ...
  c_{-1} c_0  c_1   c_2   c_3  ...
  c_{-2} c_{-1} c_0 c_1   c_2  ...
  c_{-3} c_{-2} c_{-1} c_0 c_1 ...
  c_{-4} c_{-3} c_{-2} c_{-1} c_0 ...
```

hat, und die ich L-Formen nennen will, wegen ihrer engen Beziehung zu der
Laurentschen Reihe  Σ_{n=-∞}^{+∞} c_n z^n."

English gloss: the entry in row i, column j equals c_{j−i} — the matrix is
constant along diagonals (depends only on the index difference). Toeplitz calls
these "L-Formen" because of their link to the Laurent series Σ c_n z^n.

K7-TAG: DEFINITION
ARMS: Q3 MatrixBridge (the T_M[P_A] Toeplitz symbol matrix is exactly an L-form);
foundational for the whole CvS §5 finite route.

---

## CARD 2 — Definition of the associated Toeplitz forms — grenander_szego_1958, §1.10, book p.16–17 (PDF p.21–22)

VERBATIM (§1.10 "Toeplitz forms", opening + display (3)):
"1.10. Toeplitz forms. We consider three classes of functions. In each case we
associate with every function of the class a form of Hermitian character which
we call a Toeplitz form."

For a real-valued f(x) of class L with Fourier coefficients
c_n = (1/2π) ∫_{-π}^{π} e^{-inx} f(x) dx, c_{-n} = c̄_n, the associated forms are

"T_n = Σ_{μ,ν=0}^{n} c_{ν−μ} u_μ ū_ν"     (§1.10 (3))

with the integral representation

"T_n = (1/2π) ∫_{-π}^{π} | u_0 + u_1 e^{ix} + u_2 e^{2ix} + … + u_n e^{nix} |^2 f(x) dx."  (§1.10 (6))

English gloss: the (n+1)×(n+1) Hermitian Toeplitz matrix (c_{ν−μ}) built from the
Fourier coefficients of f; its quadratic form is the L²-average of |Σ u_k e^{ikx}|²
against the weight f. The same construction applies to a distribution function
α(x) via its Fourier–Stieltjes coefficients (§1.10 (7)–(8)).

Companion positivity theorems (same section, book p.18–19 / PDF p.23–24):
"Theorem (concerning functions of the class L). The function f(x) in (4) is
nonnegative (except for a set of measure zero) if and only if the Toeplitz forms
(6) are nonnegative for all values of n."

K7-TAG: DEFINITION (+ THEOREM for the f ≥ 0 ⇔ T_n ⪰ 0 equivalence)
ARMS: Q3 MatrixBridge (T_M[P_A] and its Rayleigh quotient = §1.10(6));
CvS §5 (PSD Toeplitz ↔ nonnegative symbol).

---

## CARD 3 — Carathéodory representation of a rank-deficient (finite-type) PSD Toeplitz form — grenander_szego_1958, §1.11, book p.19 (PDF p.24)

VERBATIM (§1.11 "Trigonometric moment problem", (a)):
"These forms are nonnegative semidefinite and even positive definite unless α(x)
is of the finite type. In the latter case we denote the jumps of α(x) by
A_1, A_2, …, A_m produced at the points t_1, t_2, …, t_m
(−π < t_1 < t_2 < … < t_m < π); we have then

T_n = Σ_{j=1}^{m} A_j | u_0 + u_1 e^{it_j} + u_2 e^{2it_j} + … + u_n e^{nit_j} |^2 .   (2)

Hence T_n is positive definite if n < m and nonnegative semidefinite for n ≥ m.
In general, the Toeplitz determinants D_n (the determinants of the form T_n) are
all positive. The special case (2) is the only exception; we have in this case
D_n > 0 for n ≤ m and D_n = 0 for n > m."

English gloss: a PSD Toeplitz form fails to be positive definite **iff** its
generating measure is a finite sum of m point masses A_j > 0 sitting at m points
t_j on the unit circle (θ = t_j, i.e. z = e^{it_j}). Exactly at the first rank
drop (Toeplitz determinant D_n = 0, first at n = m) the form is a nonnegative
combination of the rank-one squares |Σ_k u_k e^{ikt_j}|² — and the kernel of T_n
is spanned by the vector(s) orthogonal to all the exponential vectors
(1, e^{it_j}, …, e^{nit_j}). The nodes e^{it_j} are precisely the zeros of the
associated (Carathéodory–Fejér) polynomial, and they lie **on** the unit circle.

**This is the closest verbatim match to the exact CvS corollary** ("Hermitian PSD
Toeplitz of rank m with a kernel vector ⇒ associated polynomial's zeros all on the
unit circle"). Grenander–Szegő states it as the finite-type ⇔ rank-deficiency ⇔
D_n = 0 equivalence with the atomic representation; the "zeros e^{it_j} are the
kernel and lie on |z|=1" reading is obtained by combining this with Card 4
(Fejér–Riesz factorization). The bare phrase "rank n−1 ⇒ zeros on the unit
circle" is **not printed as a single labelled theorem** in this monograph.

K7-TAG: REPRESENTATION (Carathéodory structure theorem for PSD Toeplitz forms)
ARMS: CvS §5 finite route step (the rank-deficiency ⇒ on-circle-zeros corollary);
Q3 MatrixBridge (kernel/rank cap of T_P^{(M)}).

Historical attribution (Preface/Introduction, book p.xi–xii / PDF p.3):
"…at the same time C. Carathéodory obtained necessary and sufficient conditions
for the Fourier coefficients of a harmonic function in order to characterize the
regularity and positivity of such a function within a circle. The conditions of
Carathéodory have been transformed by Toeplitz and the connection of
Carathéodory's problem with the L-forms has been established. For the principal
theorem of Carathéodory various proofs have been offered … We mention the
following names: E. Fischer, G. Frobenius, G. Herglotz, F. Riesz, I. Schur and
G. Szegő." (Original papers indexed in the bibliography, PDF p.243–244:
E. Fischer 1911; G. Frobenius, "Ableitung eines Satzes von Carathéodory…", 1912;
I. Schur, "Über einen Satz von C. Carathéodory", 1912; F. Riesz, "Über ein
Problem des Herrn Carathéodory", 1915; G. Szegő, "Über einen Satz des Herrn
Carathéodory", 1920.)

---

## CARD 4 — Fejér–Riesz representation of a nonnegative trigonometric polynomial — grenander_szego_1958, §1.12, book p.20–21 (PDF p.25–26)

VERBATIM (§1.12 "Representation of L. Fejér and F. Riesz for nonnegative
trigonometric polynomials", (a)):
"Theorem. Any nonnegative trigonometric polynomial in x can be written as the
square of the modulus of a polynomial in z of equal degree where z is on the unit
circle, z = e^{ix}. That is, if
   f(x) = a_0 + Σ_{k=1}^{n} (a_k cos kx + b_k sin kx)   (1)
is nonnegative for all real values of x, a polynomial g(z) = Σ_{k=0}^{n} d_k z^k
exists such that f(x) = | g(z) |², z = e^{ix}."

Zero-structure (same section, PDF p.26):
"Hence the zeros of G(z) must be symmetrical with respect to the unit circle,
i.e. with every zero z_0, where 0 < |z_0| < 1, also (z̄_0)^{-1} will be a zero …
Moreover, the zeros of G(z) on the unit circle, if they exist, are of even
multiplicity."

English gloss: PSD trigonometric polynomial ⇔ |g(e^{ix})|² (spectral / Fejér–Riesz
factorization). The reciprocal-pair symmetry of the zeros is the mechanism that
forces the boundary (finite-type) case's nodes onto |z| = 1. Uniqueness holds
when g is taken outer (g(z) ≠ 0 for |z| < 1, g(0) > 0).

K7-TAG: THEOREM (Fejér–Riesz factorization)
ARMS: CvS §5 finite route (turns "symbol ≥ 0" into an explicit |g|² factor,
supplying the on-circle-zeros half of Card 3); Q3 MatrixBridge (P_A(θ) ≥ c_* > 0
symbol floor ⇒ factorization / Toeplitz positivity).

---

## CARD 5 — Szegő eigenvalue-distribution theorem for Toeplitz forms — grenander_szego_1958, §5.2, book p.64–65 (PDF p.69–70)

VERBATIM (Chapter 5 "Eigenvalues of Toeplitz Forms", §5.2 "Asymptotic
distribution of eigenvalues", main theorem):
"Theorem. Let f(x) be a real-valued function of the class L. We denote by m and M
the 'essential' lower and upper bound of f(x), respectively, and assume that m
and M are finite. If F(λ) is any continuous function defined in the finite
interval m ≤ λ ≤ M, we have

  lim_{n→∞}  ( Σ_{ν=1}^{n+1} F(λ_ν^{(n)}) ) / (n+1)  =  (1/2π) ∫_{-π}^{π} F(f(x)) dx."   (§5.2 (7))

Here (book p.64 / PDF p.69) "the eigenvalues of the Hermitian form T_n(f) are
defined as the roots of the characteristic equation det T_n(f − λ) = 0."
Corollaries (§5.2 (10)): "lim_{n→∞} λ_1^{(n)} = m,  lim_{n→∞} λ_{n+1}^{(n)} = M."

English gloss: the eigenvalues of the n×n Toeplitz section T_n(f) are
asymptotically equidistributed as the values of the symbol f(x) over [−π, π]
(Szegő's distribution / "equal distribution" theorem, phrased via H. Weyl's
equidistribution). The extreme eigenvalues converge to ess-inf / ess-sup of f.

K7-TAG: THEOREM (Szegő eigenvalue-distribution / equidistribution)
ARMS: Q3 MatrixBridge (λ_min(T_M[P_A]) → min P_A control: the extreme-eigenvalue
corollary bounds the smallest eigenvalue by the symbol floor c_*).

---

## CARD 6 — Toeplitz determinants & OPUC extremal recursion — grenander_szego_1958, §2.1–2.2, book p.37–39 (PDF p.42–44)

VERBATIM (§2.1 (b)+(6), the orthonormal polynomials φ_n on |z|=1 for the weight
(2π)^{-1} dα(x)):
"where D_n = det (c_{μ−ν})_0^{n} is the determinant of the Toeplitz form
   (1/2π) ∫_{-π}^{π} | u_0 + u_1 e^{ix} + u_2 e^{2ix} + … + u_n e^{nix} |² dα(x),   (6)
Since (6) is positive definite we have D_n > 0 for all n. We call these
determinants D_n the Toeplitz determinants associated with the distribution
dα(x)." … "k_n = (D_{n-1}/D_n)^{1/2}"   (§2.1 (8), leading coefficient of φ_n).

VERBATIM (§2.2 (a) extremum property):
"Theorem. The polynomial φ_n(z) minimizes the integral
   (1/2π) ∫ | g(z) |² dα(x),  z = e^{ix},
where g(z) = z^n + a_1 z^{n-1} + … + a_n is an arbitrary polynomial of degree n in
which the coefficient of z^n is 1. The minimum itself is k_n^{-2} = D_n / D_{n-1}."

VERBATIM (§2.2 (b)–(c) kernel polynomials — Christoffel–Darboux kernel):
"s_n(a, z) = Σ_{ν=0}^{n} φ_ν(ā) φ_ν(z)."  …
"Theorem. Let g(z) be any polynomial of degree n. Then
   (1/2π) ∫ s_n(a, z) g(z) dα(x) = g(a),  z = e^{ix}."   (§2.2 (6))

English gloss: the ratio of consecutive Toeplitz determinants D_n / D_{n-1} is the
squared minimal norm (Levinson/Durbin-style recursion driver); the on-circle
orthonormal polynomials φ_n and the reproducing kernel s_n(a,z) give the
determinant recursion and reproducing property usable for a finite-dimensional
Lean formalization. D_n = 0 ⇔ rank drop ⇔ finite-type measure (links back to Card 3).

K7-TAG: REPRESENTATION / DEFINITION (Toeplitz-determinant recursion, reproducing kernel)
ARMS: Q3 MatrixBridge (determinant/rank cap of the compressed prime operator
T_P^{(M)}); CvS §5 (D_n = 0 rank condition).

---

## Scout summary

- **Targets found verbatim: 5 / 5.**
  1. Toeplitz-form/L-form definition (Card 1 Toeplitz 1911 p.351; Card 2 §1.10). ✅
  2. Carathéodory representation of rank-deficient PSD Toeplitz form (Card 3, §1.11). ✅
  3. Szegő eigenvalue-distribution theorem (Card 5, §5.2). ✅
  4. Rank-deficient PSD Toeplitz ⇒ nodes on unit circle: assembled from Card 3
     (finite-type, D_n = 0) + Card 4 (Fejér–Riesz zero symmetry). ✅ (see caveat below)
  5. Determinant / OPUC recursion for Lean (Card 6, §2.1–2.2). ✅

- **Is the exact "PSD Toeplitz rank n−1 ⇒ zeros on the unit circle" corollary
  printed verbatim in Grenander–Szegő?** No — not as one labelled theorem. The
  monograph gives the two halves separately: §1.11 (finite type ⇔ D_n = 0 rank
  deficiency, atomic representation T_n = Σ A_j |Σ_k u_k e^{ikt_j}|² with nodes
  t_j on the circle) and §1.12 (Fejér–Riesz factorization + reciprocal-pair zero
  symmetry). The single-sentence CvS corollary is their **direct combination**;
  for a cited "principal theorem of Carathéodory" as one statement, the primary
  sources are Carathéodory 1911 / Fejér 1915–16 and Schur 1912 / Szegő 1920
  (indexed in the G–S bibliography, PDF p.243–244), which are **NOT** in these two
  PDFs and would live in "Carathéodory 1911 original" or the Grenander–Szegő
  Appendix/notes on Chapter 4.

- **Output file:** `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/CF_TOEPLITZ_FORMULA_CARDS.md`
