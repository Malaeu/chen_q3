# STATUS: TRY_FULL_THETA_DENSE_GRAM_SCHUR
```yaml
OPERATIVE_CLASS: TRY_FULL_THETA_DENSE_GRAM_SCHUR
REQUEST_MODE: OWNER_DIRECT_RESEARCH_NOT_CODEX_BUS_ADJUDICATION
PRIMARY: FULL_SOURCE_CURVATURE_SUPPLIER_AND_THREE_POINT_SCHUR_TEST
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_DERIVATION_WITH_EXACT_ALGEBRA_CHECKS_PENDING_INDEPENDENT_REVIEW

RESULTS_THIS_TURN:
  full_theta_log_curvature_q_gt_11: PAPER_DERIVED
  full_theta_4q_squared_minus_q_second_gt_135: PAPER_DERIVED
  gaussian_upper_bound_for_full_K_sigma: PAPER_DERIVED
  arbitrary_size_gram_for_separation_at_least_one_half: PAPER_DERIVED
  equally_spaced_three_point_gram_h_at_least_one_fifth: PAPER_DERIVED
  equally_spaced_three_point_gram_sufficiently_small_h_each_fixed_sigma: PAPER_DERIVED

NOT_PROVED:
  - ALL_THREE_POINT_CONFIGURATIONS
  - ALL_EQUAL_SPACING_H_FOR_ALL_SIGMA
  - ARBITRARY_SIZE_DENSE_GRAM_POSITIVITY
  - FULL_K_SIGMA_AUTOCORRELATION_FACTOR
  - FULL_HB_SIGN
  - ORIGINAL_V_SIGN
  - ORIGINAL_SUPPORT

NEXT_TEST:
  object: DELTA_sigma_h
  formula: 1+k_sigma(2h)-2*k_sigma(h)^2
  domain: sigma>0_and_0<h<1/5
  requirement: SOURCE_DERIVED_NONNEGATIVE_LOWER_ENVELOPE
  role: NECESSARY_SUBTEST_NOT_SUFFICIENT_FOR_RH
  local_h_neighborhood: PROVED_TO_EXIST_BUT_NO_EXPLICIT_UNIFORM_RADIUS_SUPPLIED

DISCRIMINATOR:
  test: EXACT_NORMALIZED_GRAM_SCHUR_PIVOT
  positive: RIGOROUS_LOWER_ENVELOPE_L_GE_ZERO_ON_DECLARED_DOMAIN
  negative: RIGOROUS_UPPER_ENVELOPE_U_LT_ZERO_FOR_UNCHANGED_FULL_SOURCE
  zero_consistent: INCONCLUSIVE_UNLESS_EXACT_IDENTITY_OR_ONE_SIDED_BOUND

LEAN_RUN: false
ARB_INTERVAL_RUN: false
EXACT_RATIONAL_SYMBOLIC_CHECKS: PASS
EXTERNAL_INDEPENDENT_REVIEW: false
NOVELTY_CLAIM: false
REPO_CHANGED: false
CODEX_DISPATCH: false
RH_CLAIM: false
ROUTE_PROMOTION: false
```

Ы. **Entscheidung:** Nicht weiter eine unbekannte Quadratzerlegung benennen. Wir untersuchen die exakten Matrizen des vollständigen Kerns. Ein erster voller Theta-Lieferant ist unten bewiesen; der nächste klar bezeichnete Test ist ein Dreipunkt-Schurrest. Ein bestandener Dreipunkttest wäre noch kein Beweis für alle Dimensionen.

## 1. Quelle, unveränderter Gegenstand und tatsächliches Ziel

**[ABSTRACT][PAPER]** Wir verwenden die Quelle aus `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Commit `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`, Blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`, §§1–2. In dieser Sitzung wurden die Zeilen 1–85 über den GitHub-Connector gelesen. Die ältere vollständige Transportbehauptung wurde nicht erneut unabhängig abgenommen.

Für die heutige Rechnung benötigen wir nur die dort definierten Funktionen, Positivität, Geradheit und Ableitungsabnahme:

\[
\Phi(t)=\sum_{n\ge1}\phi_n(t),\qquad
\phi_n(t)=\left(4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2}\right)e^{-\pi n^2e^{2t}}.
\]

Die volle Quelle ist positiv, glatt und gerade. Ihre festen Ableitungen fallen mit allen benötigten Exponentialgewichten hinreichend schnell ab. Diese Aussagen folgen aus der Jacobi-Identität und dem positiven Reihenansatz auf der positiven Halbgeraden, nicht aus RH.

Beibehalten werden

\[
F(p)=\xi(1/2+p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt,
\quad p=\sigma+i\tau,
\]
\[
\mathscr H(p)=4\operatorname{Re}(F'(p)\overline{F(p)}),
\]
\[
K_\sigma(w)=\int_{\mathbb R}v\sinh(2\sigma v)
\Phi(v+w)\Phi(v-w)\,dv,\qquad \sigma>0.
\]

Die vorige, lokal vorhandene Ausarbeitung `THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md` enthält die genaue Identität

\[
\boxed{\mathscr H(\sigma+i\tau)=8\widehat K_\sigma(2\tau).}
\tag{1}
\]

Die Fourierkonvention lautet \(\widehat K(\omega)=\int K(w)e^{-i\omega w}dw\). Der Kern ist reell und gerade. Es wird nicht behauptet, dass eine einzelne Kernmatrix bereits die ursprüngliche Form \(V\) ist.

**Tatsächliches globales Ziel:** Nichtnegativität von \(\widehat K_\sigma\) für alle Frequenzen und alle \(\sigma>0\). Eine hinreichende und hier äquivalente Kernfassung ist

\[
\forall N,\ \forall x_1,\ldots,x_N\in\mathbb R:\quad
G_\sigma(x):=[K_\sigma(x_i-x_j)]_{i,j=1}^N\succeq0.
\tag{2}
\]

Die Richtung (2) zu (1) lässt sich ohne einen hypothetischen Spektralfaktor beweisen: Die positiven Riemannsummen liefern positive Integralkernformen auf kompakten Intervallen. Testen mit \(e^{i\omega x}\mathbf1_{[-T,T]}(x)\) und Division durch \(2T\) ergibt im Grenzwert \(\widehat K_\sigma(\omega)\ge0\) durch dominierte Konvergenz. Umgekehrt liefert Fourierinversion die endlichen positiven Formen.

Wenn (1) nichtnegativ ist, wächst \(|F(\sigma+i\tau)|^2\) mit \(\sigma\). Ein Nullpunkt mit \(\sigma>0\) würde einen ganzen waagerechten Abschnitt von Nullpunkten erzwingen. Das widerspricht \(F\not\equiv0\). Dies ist nur der bedingte Verbraucher, nicht der Beweis seiner globalen Voraussetzung.

## 2. Erster ausgeführter Faktorcheck

**[ABSTRACT][PAPER]** Der naheliegende volle Quellenfaktor lautet \(f_\sigma(t)=e^{\sigma t}\Phi(t)\). Seine skalierte Autokorrelation ist

\[
A_\sigma(w)=\int_{\mathbb R}f_\sigma(v+w)f_\sigma(v-w)\,dv.
\]

Sie liefert tatsächlich positive Quadrate, aber nicht direkt den benötigten Kern:

\[
A_\sigma(w)=\int\cosh(2\sigma v)\Phi(v+w)\Phi(v-w)dv,
\quad
\boxed{\partial_\sigma A_\sigma(w)=2K_\sigma(w).}
\]

Dabei ist \(\widehat A_\sigma(\omega)=|F(\sigma+i\omega/2)|^2/2\). Positivität einer Familie von Autokorrelationen impliziert nicht Positivität ihrer Ableitung. Der Kandidat identifiziert also eine exakte Quellenstruktur, aber noch keinen positiven Lieferanten. Wir behandeln ihn nicht als erfolgreichen Quadratnachweis.

## 3. Neuer analytischer Lieferant für die volle Theta-Quelle

### Satz A — quantitative logarithmische Krümmung

**[ABSTRACT][PAPER]** Setze

\[
q(t):=-\frac{d^2}{dt^2}\log\Phi(t).
\]

Dann liefert die folgende Rechnung für alle reellen \(t\)

\[
\boxed{q(t)>11,\qquad 4q(t)^2-q''(t)>135.}
\tag{3}
\]

Dies ist eine eigene Herleitung für die festgelegte Quelle. Keine Neuheit gegenüber der Literatur wird behauptet. Die unabhängige Kontrolle der analytischen Argumente und eine Lean-Formalisierung stehen aus.

### 3.1 Der erste Term plus der vollständig kontrollierte Rest

Für \(t\ge0\) schreibe \(x=\pi e^{2t}\), also \(x\ge\pi>31/10\), und

\[
\Phi(t)=\phi_1(t)(1+\varepsilon(t)),\qquad
\varepsilon(t)=\sum_{n\ge2}\rho_n(x),
\]
\[
\rho_n(x)=n^2\frac{2n^2x-3}{2x-3}e^{-(n^2-1)x}.
\tag{4}
\]

Dies ist eine exakte Gleichheit mit der vollen Summe. Der Rest wird nicht weggelassen und \(\phi_1\) nicht anstelle von \(\Phi\) in den HB-Verbraucher eingesetzt.

Im Folgenden bezeichnen Striche Ableitungen nach \(t\). Es gilt gleichmäßig auf \(t\ge0\):

\[
0\le\varepsilon<\frac3{1000},\quad
|\varepsilon'|<\frac3{50},\quad
|\varepsilon''|<1,\quad
|\varepsilon'''|<17,\quad
|\varepsilon''''|<267.
\tag{5}
\]

### 3.2 Warum die Restsummen global und nicht nur an einem Punkt beschränkt sind

Schreibe \(m=n^2\), \(b=m-1\ge3\) und \(D=2x\,d/dx\). Dann

\[
\rho_n(x)=m^2e^{-bx}+\frac32mb\int_0^\infty
 e^{3u/2}e^{-(b+u)x}\,du.
\tag{6}
\]

Definiere \(T_0(z)=1\), \(T_{j+1}(z)=z(T_j(z)-T_j'(z))\). Es gilt

\[
(-1)^jD^je^{-cx}=2^jT_j(cx)e^{-cx}.
\]

Die Koeffizienten von \(T_j(y+9)\), nach fallenden Potenzen, lauten:

| j | Koeffizienten |
|---:|---|
| 0 | 1 |
| 1 | 1, 9 |
| 2 | 1, 17, 72 |
| 3 | 1, 24, 190, 495 |
| 4 | 1, 30, 331, 1583, 2745 |
| 5 | 1, 35, 475, 3090, 9451, 10458 |

Alle sind positiv. In (6) ist \((b+u)x\ge9\) für \(x\ge3\). Daher sind die Ableitungen bis Ordnung fünf alternierend vorzeichenrichtig. Insbesondere nehmen die Beträge bis Ordnung vier mit \(t\), und damit mit \(x\), ab. Ihre Maxima auf \(x\ge31/10\) liegen am linken Endpunkt.

Ableitung unter dem Integral und Summation sind zulässig: Für \(x\ge31/10\) dominiert eine exponentiell fallende Funktion jedes hier auftretende feste Polynom in \(u\) und \(n\).

### 3.3 Endliche exakte Arithmetik für die unendlichen Restsummen

Für \(x_0=31/10\) sei

\[
P_j(m)=\left.(-1)^jD^j\left[
 m\frac{2mx-3}{2x-3}e^{-(m-1)x}\right]
 e^{(m-1)x}\right|_{x=x_0}.
\]

Es handelt sich um ein rationales Polynom vom Grad \(j+2\). Mit

\[
P_j(m)=\sum_k p_{jk}m^k,\qquad B_j=\sum_k|p_{jk}|9^k
\]

folgt für \(m\ge9\)

\[
|P_j(m)|\le B_j(m/9)^{j+2}.
\]

Aus der endlichen Tayloruntergrenze für die Exponentialfunktion folgt \(e^{31/10}>22\). Für \(n\ge3\) ist das Verhältnis der aufeinanderfolgenden Majoranten höchstens

\[
(4/3)^{12}/22^7<1/2.
\]

Deshalb ist die gesamte Summe durch die rationale Zahl

\[
U_j=\frac{P_j(4)}{22^3}+\frac{2B_j}{22^8}
\tag{7}
\]

beschränkt. Die exakten Polynome sind:

\[
P_0=\frac{m(31m-15)}{16},
\]
\[
P_1=\frac{31m(m-1)(248m-45)}{640},
\]
\[
P_2=\frac{31m(m-1)(30752m^2-36952m+9705)}{12800},
\]
\[
P_3=\frac{31m(m-1)(7626496m^3-19404512m^2+17098856m-2055615)}{512000},
\]
\[
P_4=\frac{31m(m-1)}{5120000}
(472842752m^4-1990515456m^3+3248733536m^2-1744362312m+319706355).
\]

Die rationalen Vergleiche in (7) wurden exakt, ohne Gleitkommarundung, geprüft:

| Ableitungsordnung | U_j zur Orientierung, gerundet | verwendete rationale Obergrenze |
|---:|---:|---:|
| 0 | 0.002559173 | 3/1000 |
| 1 | 0.051694929 | 3/50 |
| 2 | 0.966031294 | 1 |
| 3 | 16.648200627 | 17 |
| 4 | 266.052438910 | 267 |

Die gerundeten Zahlen dienen nur der Lesbarkeit. Die Definition (7), die angegebenen rationalen Polynome und die rationalen Vergleiche begründen (5).

### 3.4 Schluss des Krümmungsbeweises

Für den ersten Term gilt

\[
q_1=-(\log\phi_1)''=4x+\frac{24x}{(2x-3)^2},\qquad
4x\le q_1\le\frac{20}{3}x\quad(x\ge3).
\]

Direkt berechnet man

\[
d_1:=4q_1^2-q_1''
=\frac{16x(64x^5-400x^4+1152x^3-1680x^2+972x-135)}{(2x-3)^4}.
\]

Die Differenz \(d_1-60x^2\) ist positiv für \(x\ge3\): Nach \(x=y+3\) lautet ihr Zähler

\[
64y^6+512y^5+4512y^4+28704y^3+85860y^2+111240y+48276.
\]

Ihr Nenner ist \((2x-3)^4>0\).

Setze \(L=\log(1+\varepsilon)\). Aus (5) und \(1+\varepsilon\ge1\) folgen

\[
|L''|<1+(3/50)^2=\frac{2509}{2500},
\]
\[
|L''''|<267+4(3/50)17+3+12(3/50)^2+6(3/50)^4
=\frac{856635243}{3125000}<275.
\]

Nun ist \(q=q_1-L''\). Somit

\[
q>4x-\frac{2509}{2500}\ge\frac{28491}{2500}>11,
\]
\[
\begin{aligned}
4q^2-q''
&=d_1-8q_1L''+4(L'')^2+L''''\\
&>60x^2-\frac{160}{3}\frac{2509}{2500}x-275.
\end{aligned}
\]

Die rechte Seite ist auf \(x\ge31/10\) streng wachsend. Ihr Wert am linken Endpunkt ist

\[
\frac{254384}{1875}>135.
\]

Geradheit der vollen \(\Phi\) macht \(q\) und \(q''\) gerade. Damit gilt (3) auch für \(t<0\). **Dies schließt den Beweis von Satz A.**

## 4. Erster Gewinn: ein ganzer Bereich beliebig großer Kernmatrizen

**[ABSTRACT][PAPER]** Aus \((\log\Phi)''<-11\) folgt für alle reellen \(v,w\)

\[
\Phi(v+w)\Phi(v-w)\le e^{-11w^2}\Phi(v)^2.
\]

Mit dem nichtnegativen Gewicht \(v\sinh(2\sigma v)\) erhalten wir

\[
\boxed{0<K_\sigma(w)\le K_\sigma(0)e^{-11w^2}.}
\tag{8}
\]

Seien jetzt beliebig viele verschiedene reelle Punkte paarweise mindestens \(1/2\) voneinander entfernt. Sortiere sie. Dann ist in jeder normierten Matrixzeile

\[
\sum_{j\ne i}\frac{|K_\sigma(x_i-x_j)|}{K_\sigma(0)}
\le2\sum_{k\ge1}e^{-11k^2/4}
\le\frac{2e^{-11/4}}{1-e^{-11/4}}<\frac17.
\]

Hier reicht \(e^{11/4}>15\), was bereits die Tayloruntergrenze bis Ordnung sechs liefert. Die elementare quadratische Abschätzung der gemischten Matrixeinträge ergibt daher

\[
\boxed{G_\sigma(x)\succeq\frac67K_\sigma(0)I.}
\tag{9}
\]

Das gilt für jedes endliche \(N\), alle \(\sigma>0\) und alle solchen Punktmengen. Es ist keine Extrapolation einer berechneten Matrix. Es beweist nicht die Positivität dicht liegender Punktmengen.

## 5. Der konkrete nächste Test: drei äquidistante Punkte

**[ABSTRACT][PAPER]** Normiere

\[
k_\sigma(w)=K_\sigma(w)/K_\sigma(0),\quad
 a=k_\sigma(h),\quad b=k_\sigma(2h).
\]

Für die drei Punkte \(-h,0,h\) ist die Matrix

\[
\begin{pmatrix}1&a&b\\a&1&a\\b&a&1\end{pmatrix}.
\]

Der ungerade Eigenwert ist \(1-b>0\) bei \(h>0\). Der verbleibende gerade Block ist

\[
\begin{pmatrix}1+b&\sqrt2a\\\sqrt2a&1\end{pmatrix}.
\]

Damit lautet die exakt noch zu prüfende Ungleichung

\[
\boxed{\Delta_\sigma(h):=1+k_\sigma(2h)-2k_\sigma(h)^2\ge0.}
\tag{10}
\]

Sie ist ein echter notwendiger Test des unveränderten vollständigen Kerns. Ein negatives \(\Delta\) wäre kein negatives Ergebnis für ein Theta-Präfix.

### 5.1 Größere Abstände bereits erledigt

Für \(h\ge1/5\) liefert (8)

\[
\Delta_\sigma(h)\ge1-2e^{-22h^2}>\frac16.
\]

Die letzte Ungleichung folgt aus \(e^{22/25}>12/5\), wiederum durch eine endliche Tayloruntergrenze. Der gerade Block hat Spur höchstens drei, also kleinsten Eigenwert mindestens \(1/18\); der ungerade Eigenwert ist größer als \(1/2\). Damit gilt für diese normierten Dreipunktmatrizen

\[
\boxed{G_\sigma(-h,0,h)\succeq\frac1{18}K_\sigma(0)I
\quad(h\ge1/5,\ \sigma>0).}
\tag{11}
\]

### 5.2 Auch die lokale Kollision ist vorzeichenrichtig

Für festes \(\sigma>0\) definiere das Wahrscheinlichkeitsmaß

\[
d\mu_\sigma(v)=\frac{v\sinh(2\sigma v)\Phi(v)^2}{K_\sigma(0)}\,dv.
\]

Direkte Differentiation nach \(w\) ergibt

\[
k_\sigma''(0)=-2\mathbb E_\sigma q,
\qquad
k_\sigma''''(0)=\mathbb E_\sigma(12q^2-2q'').
\]

Daraus folgt

\[
\begin{aligned}
k_\sigma''''(0)-k_\sigma''(0)^2
&=2\mathbb E_\sigma(4q^2-q'')+4\operatorname{Var}_\sigma(q)\\
&>270.
\end{aligned}
\tag{12}
\]

Die Taylorentwicklung von (10) lautet deshalb

\[
\Delta_\sigma(h)
=\left[\mathbb E_\sigma(4q^2-q'')+2\operatorname{Var}_\sigma(q)\right]h^4
+O_\sigma(h^6).
\tag{13}
\]

**Für jedes feste \(\sigma>0\) existiert also \(\delta_\sigma>0\), sodass**

\[
\boxed{\Delta_\sigma(h)>100h^4>0\qquad(0<h<\delta_\sigma).}
\tag{14}
\]

Eine explizite, gleichmäßige Zahl \(\delta_\sigma\), insbesondere für alle \(\sigma>0\) gemeinsam, wurde hier nicht geliefert. Die Taylorfehlerkonstante darf nicht unterschlagen werden. Deshalb schließen (11) und (14) zusammen noch nicht den vollständigen Dreipunktbereich.

## 6. Der nächste konkrete Arbeitsauftrag

**[ABSTRACT][CONDITIONAL]** Bearbeite ausschließlich

\[
\Delta_\sigma(h)\ge0\qquad\sigma>0,\quad0<h<1/5.
\tag{15}
\]

Der erste zu prüfende Lieferant ist ein **vorzeichenrichtiger Rest für die volle, gekoppelte Expression (10)**, nicht für ihre Terme einzeln. Die lokale Formel (13) stellt hierfür einen echten positiven Anfangsterm bereit.

Eine exakte Anfangsform ist die Integralrestform

\[
\frac{\Delta_\sigma(h)}{h^4}
=\frac16\int_0^1(1-u)^3\Delta_\sigma^{(4)}(uh)\,du,
\tag{16}
\]

weil die Ableitungen bis Ordnung drei in null verschwinden. Dabei ist

\[
\Delta_\sigma^{(4)}(x)
=16k_\sigma''''(2x)-4k_\sigma(x)k_\sigma''''(x)
-16k_\sigma'(x)k_\sigma'''(x)-12k_\sigma''(x)^2.
\tag{17}
\]

**Arbeitsreihenfolge:** Zuerst die Theta-Produkte in (17) gemeinsam einsetzen und den Rest in (16) vorzeichenrichtig abschätzen. Falls die stärkere Forderung \(\Delta^{(4)}\ge0\) scheitert, folgt daraus nicht \(\Delta<0\): Der Verbraucher benötigt nur den gewichteten Integralrest (16). Eine obere Schranke \(U(\Delta)<0\) wäre ein echter Gegenbeweis; eine negative untere Schranke wäre lediglich unbrauchbar.

Ein prüfbarer positiver Ausgang liefert die volle äquidistante Dreipunktungleichung. **Er liefert nicht automatisch ungleiche Dreipunktabstände und erst recht nicht alle Dimensionen.**

## 7. Wie dieser Test zum globalen Ziel gehört

**[ABSTRACT][CONDITIONAL]** Die konstruktive Richtung ist eine quellenabhängige Schur-Rekursion. Wenn eine bereits positive Matrix \(G_N\) um einen Punkt erweitert wird, ist der neue Rest

\[
s_N=K_\sigma(0)-v^*G_N^{-1}v,
\qquad v_i=K_\sigma(x_i-x_{N+1}).
\tag{18}
\]

Ein aus der Quelle abgeleitetes allgemeines Gesetz \(s_N\ge0\), für beliebige alte Punktmengen und den neuen Punkt, würde per Induktion die volle Positivität liefern. Bei singulären Zwischenmatrizen wären die entsprechende Bildbedingung und eine korrekt formulierte semidefinite Schur-Fassung erforderlich; ein unbekannter positiver Inversenboden wird nicht vorausgesetzt.

Der Dreipunkttest erprobt einen besonders kleinen Fall dieser Rekursion. **Ein bestandener Fall ist keine Induktion.** Erst ein verallgemeinerbarer Quellenmechanismus verdient die Fortsetzung zu beliebigem \(N\). Mehr positive numerische Matrizen ersetzen diesen Mechanismus nicht.

Dicht liegende Punkte sollen durch geteilte Differenzen behandelt werden: etwa \([f(x+h)-f(x)]/h\), nicht durch schlecht konditionierte Rohkoordinaten. Das ist eine Basisänderung, die für jedes \(h\ne0\) exakt zurückzuführen ist. Ihr Grenzübergang darf keine endlichen Konfigurationen auslassen.

## 8. Zwei zulässige Darstellungen und Entscheidung

| Darstellung | Konkrete Rolle | Geschätzte Entscheidungskraft / Aufwand |
|---|---|---|
| Voller Kern, dichte Dreipunktkonfiguration, gekoppelter Schurrest | Gewählter nächster notwendiger Test; Ziel (15), danach nur mit wirklicher allgemeiner Rekursion weiter | 8/10 für den kleinen Test; Anfangsaufwand 4/10, globale Rekursion unbekannt |
| Ableitung der vollständigen Autokorrelation \(\partial_\sigma A_\sigma\) | Reserve: quellenabhängiger Beweis der positiven Kernelzunahme oder explizite positive Ableitungsfaktoren | 10/10 bei Erfolg; Aufwand 8/10, Faktor noch nicht konstruiert |

Die Zahlen sind qualitative Arbeitsbewertungen, keine Wahrscheinlichkeiten und keine mathematischen Aussagen. Eine einzelne notwendige Prüfung hat nicht automatisch die Entscheidungskraft eines Beweises des Gesamtziels.

## 9. Gepflanzter Gegenfall: Warum die Quellenableitungen relevant sind

**[ABSTRACT][PAPER]** Der Test darf nicht jede positive glatte log-konkave Funktion akzeptieren. Setze \(k(w)=e^{-w^4}\) und \(h^4=\log(4/3)\). Dann

\[
a=3/4,\qquad b=(3/4)^{16},
\]
\[
\boxed{1+b-2a^2=(3/4)^{16}-1/8
=-\frac{493824191}{4294967296}<0.}
\]

Damit hat die Dreipunktmatrix einen negativen Eigenwert, obwohl der Kern glatt, gerade, positiv und log-konkav ist. Dieser Gegenfall ist **nicht** die Theta-Quelle. Er zeigt, warum deren konkrete Krümmungsinformation und Restkontrolle wichtig sind. Er widerlegt weder die globale Theta-Ungleichung noch die gesamte Faktorisierungsrichtung.

## 10. Prüfprotokoll und Vorhersagen

**[ABSTRACT][PAPER]** Ein lokales SymPy-Skript prüfte exakt:

- die Ableitungsrekursionen der rationalen Theta-Restterme;
- die positiven verschobenen Polynome bis Ableitungsordnung fünf;
- die rationalen Schranken (5), (7);
- den positiven Zähler von \(d_1-60x^2\);
- die Schranken für \(L''\) und \(L''''\);
- den rationalen Endboden \(254384/1875>135\);
- den exakten negativen gepflanzten Dreipunktwert.

Ausgabe: `all_exact_checks: PASS`. Die gesonderte rationale Taylorprüfung für \(e^{11/4}>15\) lieferte bereits mit Ordnung sechs \(9019421/589824>15\).

Dies ist keine Lean-Kernelprüfung und keine Arb-Intervallprüfung. Die analytischen Schritte — Ableitungswechsel, unendliche Majoranten, Integralargumente — sind Bestandteil des Papierbeweises und benötigen unabhängige Kontrolle.

Die Quellen-Krümmungsprüfung wurde öffentlich als konkreter Beweisauftrag festgehalten, bevor der vollständige Restbeweis und der finale rationale Check abgeschlossen wurden. Vorherige symbolische Exploration hatte die Wahl des Kandidaten beeinflusst; deshalb wird dies **nicht** als verblindeter Vorhersageerfolg gezählt. Ergebnis: der konkrete Papieransatz für (3) besteht die vorgelegten Prüfungen.

`P_EULER_HB_3`, die frühere breite Hoffnung auf einen vollständigen positiven Theta-Quadratlieferanten, bleibt **UNRESOLVED**. Die hiesigen Teilbereiche und Quellenungleichungen bestätigen diesen stärkeren Anspruch nicht.

## 11. Dependency epistemics

```yaml
DOWNSTREAM_CONSUMER: ZERO_EXCLUSION_FOR_ORIGINAL_F_IN_RE_P_POSITIVE
ACTUAL_CONSUMER_REQUIREMENT: FULL_H_NONNEGATIVE_OR_ANOTHER_INDEPENDENT_ZERO_EXCLUSION_PROOF
ORIGINAL_REQUESTED_OBJECT: FULL_THETA_KSIGMA_POSITIVE_SQUARE_DECOMPOSITION
ORIGINAL_OBJECT_IS: NOT_NECESSARY
KNOWN_WEAKER_SUFFICIENT_INTERFACES:
  - ALL_FINITE_FULL_KSIGMA_GRAM_MATRICES_PSD_WITH_ALL_QUANTIFIERS
  - FULL_H_NONNEGATIVE_WITHOUT_EXPLICIT_FACTORS
  - POSITIVE_DEFINITE_INCREASE_OF_FULL_AUTOCORRELATION_A_SIGMA
NECESSARY_SUBTEST_ONLY:
  - EQUALLY_SPACED_THREE_POINT_DELTA_NONNEGATIVE
  - SOURCE_CURVATURE_MOMENT_AT_ZERO_NONNEGATIVE
FULL_SOURCE_FAILURE_TYPE: NO_DERIVATION
FULL_SOURCE_EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: EXPLICIT_SOURCE_SCHUR_RECURSION_OR_FULL_SOURCE_AUTOCORRELATION_FACTOR
NOVELTY_AXIS: SOURCE_SPECIFIC_QUANTITATIVE_DERIVATIVE_CONTROL_SPENT_ON_EXACT_DENSE_GRAM_RESTS
KILL_SCOPE: NONE_FOR_THE_THETA_ROUTE
COUNTEREXAMPLE_SCOPE: GENERIC_POSITIVE_LOG_CONCAVE_KERNEL_IMPLIES_PSD_THREE_POINT_MATRIX
FORBIDDEN_PROMOTIONS:
  - THREE_POINT_PSD_TO_ALL_DIMENSIONS
  - SPARSE_GRAM_FLOOR_TO_DENSE_GRAM_FLOOR
  - SIGMA_DEPENDENT_LOCAL_TAYLOR_RADIUS_TO_UNIFORM_RADIUS
  - NEGATIVE_LOWER_BOUND_TO_NEGATIVE_WITNESS
  - FINITE_THETA_PREFIX_TO_FULL_THETA_SOURCE
```

## 12. Abschluss und Grenzen

**Kleiner geworden:** Der Arbeitsauftrag ist eine explizite Schurungleichung. Der erste echte Lieferant kontrolliert die logarithmische Krümmung der vollen Theta-Quelle mit rationalen Konstanten. Er schließt beliebig große ausreichend getrennte Konfigurationen, größere äquidistante Dreipunktabstände und die lokale Dreipunktkollision bei jedem festen \(\sigma\).

**Noch offen:** Der gekoppelte Rest bei kleinen endlichen Abständen, allgemeine dichte Punktmengen, die volle Faktorzerlegung, HB, SUPPORT und das Vorzeichen der ursprünglichen Form \(V\).

**Nicht erneut tun:** Einen unbekannten positiven Faktor nur benennen; einen Test für niedrigen Rang als Gesamtbeweis verkaufen; Theta-Restterme vor der vollständigen Quellengleichheit wegwerfen; eine negative Untergrenze mit einem Gegenbeispiel verwechseln.

Es wurde kein Codex-Auftrag abgesandt, kein Repository verändert und kein Zustand der Produktionsroute angehoben. Dieses Markdown ist der einzige Ergebnisbericht dieser Sitzung.

### Gelesene Quellen und externe Einordnung

- Aktuelles Projektprotokoll `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, über den GitHub-Connector gelesen; Blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`.
- Gepinnte Quellendefinition wie in §1.
- Lokale vollständige Vorarbeit `THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md`, insbesondere §§2, 8–12.
- Ein begrenzter externer Abgleich fand Csordas, *Fourier transforms of positive definite kernels and the Riemann ξ-Function*, arXiv:1309.0055, sowie Planat–Solé, *Second-Level Concavity of the Riemann Ξ Kernel*, arXiv:2608.19160v1. Deren Themen sind verwandte Kernel- und Konkavitätsfragen. Ihre Resultate werden für den vorliegenden Beweis nicht importiert, und ihre vollständigen Zertifikate wurden nicht überprüft. Die dortige Normalisierung ist von der hier fixierten zu unterscheiden. Keine dieser Sichtungen begründet einen Neuheits- oder RH-Anspruch.
