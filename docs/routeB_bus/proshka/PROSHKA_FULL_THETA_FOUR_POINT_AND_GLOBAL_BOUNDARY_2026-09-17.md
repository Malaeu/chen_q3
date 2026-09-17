# STATUS: TRY_FULL_SOURCE_MIXED_SCHUR_AFTER_FOUR_POINT_PROOF
```yaml
OPERATIVE_CLASS: TRY_FULL_SOURCE_MIXED_SCHUR_AFTER_FOUR_POINT_PROOF
PRIMARY: FULL_THETA_ARBITRARY_FOUR_POINT_PAPER_PROOF_AND_GLOBAL_BOUNDARY
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION_NOT_CODEX_BUS_ADJUDICATION
DATE: 2026-09-17
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_PROOF_WITH_COMPLETE_RATIONAL_INTERVAL_SOURCE_CERTIFICATE
INDEPENDENT_MATHEMATICAL_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
ARB_USED: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT

CLOSED_IN_THIS_PAPER:
  - FULL_SOURCE_q_GT_18_ABS_q1_LT_3q_0_LT_q2_LT_10q_q4_GT_MINUS_200q
  - EACH_FULL_THETA_PROFILE_STRICTLY_TOTALLY_POSITIVE_THROUGH_ORDER_FOUR
  - FULL_THETA_GRAM_POSITIVE_DEFINITE_FOR_ALL_DISTINCT_FOUR_POINTS_ALL_sigma_GT_0
  - FULL_FOUR_POINT_SCHUR_REST_POSITIVE
  - EXACT_MIXED_SCHUR_REST_PLUS_MATRIX_VARIANCE_IDENTITY
  - SINGULAR_AWARE_SCHUR_CRITERION_IN_EVERY_DIMENSION

NOT_CLOSED:
  - SOURCE_SPECIFIC_ALL_DIMENSION_SIGN_PROPAGATION
  - FULL_HB_SIGN_IN_0_LT_sigma_LT_1_OVER_2
  - ORIGINAL_SUPPORT
  - ORIGINAL_V_SIGN

CONDITIONAL_RESULTS_ONLY:
  - FULL_MIXTURE_GRAM_POSITIVITY_EQUIVALENT_TO_FULL_HB_SIGN
  - FULL_HB_SIGN_IMPLIES_SUPPORT_FOR_THE_ORIGINAL_MULTIPLIER
  - FULL_HB_SIGN_IMPLIES_EXACT_ORIGINAL_V_SPECTRAL_SQUARE_SUM

SCOPED_REJECTION:
  statement: EVERY_EXACT_MIDPOINT_PROFILE_IS_POSITIVE_DEFINITE_IN_ALL_DIMENSIONS
  KILL_SCOPE: THEOREM_SHAPE
  FAILURE_TYPE: INCOMPATIBILITY
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_STATEMENT_ONLY
  evidence: SECTION_6_HUDSON_THEOREM_PLUS_EXACT_NON_GAUSSIAN_THETA_SOURCE
  original_full_mixture_refuted: false
  original_V_negative_witness: false

DISCRIMINATOR:
  four_point: det_G4_EQ_det_G3_TIMES_s4_WITH_SOURCE_LOWER_BOUND_POSITIVE
  all_dimension: SOURCE_BOUND_FOR_MEAN_PROFILE_RESIDUAL_PLUS_MATRIX_VARIANCE
  zero_consistent_result: INCONCLUSIVE_UNLESS_AN_EXACT_IDENTITY_OR_ONE_SIDED_BOUND_DECIDES

REPOSITORY_CHANGED: false
CODEX_DISPATCHED: false
PRODUCTION_STATE_CHANGED: false
RH_CLAIM: false
```

## 0. Ergebnis und Beweisgrenze

**Der vollständige Vierpunktrest ist in diesem rechnergestützten Papierbeweis positiv:** für jedes `sigma > 0`, für beliebige vier verschiedene reelle Positionen, ohne Mindestabstand. Der Beweis kontrolliert den vollständigen unendlichen Theta-Quellterm. Er beruht nicht auf einer Stichprobe von Matrizen.

**Eine dimensionsunabhängige Schur-Identität und das vollständige algebraische Schur-Kriterium sind ebenfalls hergeleitet. Die Theta-spezifische Vorzeichenungleichung in beliebiger Dimension ist nicht hergeleitet.** Deshalb sind das gesamte HB-Vorzeichen, SUPPORT und das Vorzeichen der ursprünglichen Form V weiterhin offen. Die zugehörigen Schlussfolgerungen werden hier mit ihrer noch offenen Voraussetzung vollständig getrennt bewiesen.

Zugleich ist ein zu starker globaler Ansatz ausgeschlossen: Nicht jedes einzelne Mittelpunktprofil der echten Theta-Quelle kann in allen Dimensionen positiv definit sein. Dies folgt aus Hudsons Satz und der Nicht-Gaußförmigkeit der Quelle. Es ist **kein Gegenbeispiel zum vollständigen gemittelten Kern**.

Die Prüfprogramme wurden ausgeführt. Sie prüfen genaue rationale Intervalle und symbolische Identitäten. Sie ersetzen keine unabhängige Kontrolle des analytischen Beweises und sind weder Lean noch Arb. Die früheren Dreipunkt-Checks wurden zusätzlich erneut ausgeführt; der neue Vierpunktbeweis benötigt ihren speziellen Winkelbeweis nicht.

## 1. Unveränderte Objekte und Quellen

**[ABSTRACT][PAPER — Definitionen und aus S1 übernommene Quellregularität]**

Es gilt die Fourier-Konvention

\[
\widehat g(y)=\int_{\mathbb R}g(t)e^{-iyt}\,dt.
\]

Der vollständige positive, gerade Theta-Quellterm ist

\[
\Phi(t)=\sum_{n\ge1}
 (4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2})e^{-\pi n^2e^{2t}}.
\tag{1.1}
\]

Zur Quellregularität: Mit theta(u)=sum_(n>=1) exp(-pi n^2 u) und r(u)=4u theta''(u)+6 theta'(u) ist Phi(t)=exp(5t/2)r(exp(2t)). Zweimaliges Differenzieren der Jacobi-Identität liefert r(1/u)=u^(5/2)r(u), also Geradheit von Phi. Für u>=1 ist jeder Term von r positiv, denn 2pi n^2 u-3>0. Die übrige Hälfte folgt durch Geradheit. Lokal gleichmäßige Konvergenz aller festen Ableitungsreihen und die Dominierung durch Polynomfaktoren mal exp(-pi n^2 u) liefern Glattheit und superexponentiellen Abfall jeder festen Ableitung an beiden Enden. Die vollständige xi-Transformation folgt zunächst im absolut konvergenten Mellin-Bereich durch zwei partielle Integrationen und dann durch analytische Fortsetzung; dies ist die in S1 festgehaltene Normierung.

Die normalisierte ursprüngliche Quelle und die ursprüngliche Form sind

\[
A=\|\Phi\|_2>0,\qquad f=\Phi/A,
\]
\[
V(x,y)=\int_0^\infty(x+y+2t)f(x+t)f(y+t)\,dt.
\tag{1.2}
\]

**V-Positivität bedeutet hier Positivität jeder endlichen komplexen quadratischen Form der Matrix `[V(x_i,x_j)]`; sie bedeutet nicht bloß punktweise Positivität von V.**

Setze

\[
F(p)=\xi(1/2+p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt,
\quad p=\sigma+i\tau,\quad\sigma>0,
\]
\[
\mathscr H(p)=|F+F'|^2-|F-F'|^2=4\Re(F'\overline F).
\tag{1.3}
\]

Diese letzte Formel teilt nicht durch eine Funktion mit unbekannten Nullstellen.

Der vollständige Kern ist

\[
K_\sigma(w)=\int_{\mathbb R}v\sinh(2\sigma v)
                 \Phi(v+w)\Phi(v-w)\,dv,
\quad k_\sigma(w)=K_\sigma(w)/K_\sigma(0).
\tag{1.4}
\]

Für jedes feste sigma sind K und seine Ableitungen schnell fallend. Aus der symmetrisierten Doppelintegralform von (1.3) folgt mit t=v+w, u=v-w, Jacobi-Determinante 2:

\[
\boxed{\mathscr H(\sigma+i\tau)=8\widehat K_\sigma(2\tau).}
\tag{1.5}
\]

Der Faktor 8 gehört zur festgehaltenen Fourier-Konvention.

Für jeden reellen Mittelpunkt v definieren wir

\[
C_v(w)=\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}=e^{-R_v(w)},
\]
\[
R_v(w)=-\log\Phi(v+w)-\log\Phi(v-w)+2\log\Phi(v).
\tag{1.6}
\]

Die exakte positive Mischung lautet

\[
k_\sigma(w)=\int C_v(w)\,d\mu_\sigma(v),\qquad
 d\mu_\sigma(v)=\frac{v\sinh(2\sigma v)\Phi(v)^2}{K_\sigma(0)}\,dv.
\tag{1.7}
\]

Es ist ein Wahrscheinlichkeitsmaß. Alle Integrale sind absolut konvergent; an v=0 besitzt der Zähler lediglich eine Nullstelle, keine Singularität.

**Quellenbindung.** S1 bindet (1.1), (1.2), die xi-Transformation und die volle Quellregularität. S2 bindet den unveränderten kausalen Multiplikator aus Abschnitt 8. Die gesamten alten Sign-Transfer-Berichte werden hier nicht als neu unabhängig abgenommen bezeichnet. Die aktuellen weiteren Ableitungsschranken werden dagegen unten aus (1.1) neu kontrolliert.

## 2. Neue Ableitungsschranken für die vollständige Quelle

**[ABSTRACT][PAPER — analytischer Restbeweis plus ausgeführtes rationales Intervallzertifikat]**

Hier bezeichnet

\[
q(t)=-(\log\Phi(t))''
\]

ausschließlich die logarithmische Krümmung. Sie ist nicht der in älteren SUPPORT-Dokumenten ebenfalls q genannte normalisierte Quellterm.

### Satz 2.1

Für jedes reelle t gilt

\[
\boxed{q(t)>18,\quad |q'(t)|<3q(t),\quad
       0<q''(t)<10q(t),\quad q^{(4)}(t)>-200q(t).}
\tag{2.1}
\]

### 2.1 Exakte Zerlegung, nicht Quellenersatz

Für t>=0 setze x=pi exp(2t)>=pi>31/10 und D=2x d/dx. Dann

\[
\Phi=\phi_1(1+\epsilon),\qquad
\epsilon(x)=\sum_{n\ge2}\rho_n(x),
\]
\[
\rho_n(x)=\frac{n^2(2n^2x-3)}{2x-3}e^{-(n^2-1)x}.
\tag{2.2}
\]

Dies ist eine Identität: epsilon enthält sämtliche restlichen Theta-Terme. Mit L=log(1+epsilon) ergibt sich

\[
q_1=4x+\frac{24x}{(2x-3)^2},\qquad
q^{(j)}=D^j q_1-D^{j+2}L\quad(j=0,1,2,4).
\tag{2.3}
\]

### 2.2 Unendliche Ableitungsschwänze

Schreibe m=n^2, b=m-1. Dann

\[
\rho_n(x)=m^2e^{-bx}+\frac32mb
       \int_0^\infty e^{3u/2}e^{-(b+u)x}\,du.
\tag{2.4}
\]

Definiere Polynome T_0(z)=1 und T_{j+1}(z)=z(T_j(z)-T_j'(z)). Es gilt

\[
(-1)^jD^je^{-cx}=2^jT_j(cx)e^{-cx}.
\tag{2.5}
\]

Für j=0,...,7 besitzen alle Polynome T_j(z+24) strikt positive Koeffizienten. Der mitgelieferte Symbolcheck verifiziert dies exakt. Also alternieren die Vorzeichen der Ableitungen in (2.4), sobald bx>=24. Außerdem nimmt `|D^j rho_n|` dann für j<=6 mit x ab. Differentiation unter dem u-Integral ist durch exponentielle Dominierung für x>3/2 erlaubt.

Für einen rationalen Start x0 und ein n0 mit (n0^2-1)x0>=24 sei

\[
P_j(m)=(-1)^j[D^j\rho_n(x_0)]e^{(m-1)x_0},
\quad p=n_0^2,
\quad B_j=\sum_k|[m^k]P_j|p^k.
\]

P_j ist ein rationales Polynom von Grad hoechstens j+2. Für m>=p ist

\[
|P_j(m)|\le B_j(m/p)^{j+2}.
\]

Wähle ein rationales E<exp(x0). Das Verhältnis aufeinanderfolgender Majorantenterme für n>=n0 ist höchstens

\[
\left(\frac{n_0+1}{n_0}\right)^{2j+4}E^{-(2n_0+1)}<\frac12.
\]

Daher gilt die volle, gleichmäßige Schranke

\[
\sum_{n\ge n_0}|D^j\rho_n(x)|
\le 2B_j E^{-(p-1)}\quad (x\ge x_0).
\tag{2.6}
\]

Verwendet werden `(x0,n0,E)=(31/10,4,22)` und `(8,2,2980)`. Die beiden Exponentialuntergrenzen folgen jeweils aus einer positiven endlichen Taylor-Summe; die Verhältnisungleichungen sind exakte rationale Vergleiche.

Die n>=4-Schranken auf x>=31/10 für j=0,...,6 betragen ungefähr

```
7.47e-18, 7.73e-16, 8.16e-14, 8.78e-12,
9.63e-10, 1.075e-7, 1.221e-5.
```

Diese Dezimalzahlen dienen nur der Orientierung. Die Berechnung verwendet die vom Generator gelieferten exakten Brüche, keine gerundeten Dezimalwerte.

### 2.3 Kompakter Bereich: vollständige Intervalldeckung

Das Intervall [31/10,8] wird in genau 2048 **geschlossene**, benachbarte rationale Intervalle zerlegt. Auf jeder ganzen Zelle werden die n=2- und n=3-Terme aus (2.2) und alle benötigten Ableitungen eingeschlossen. Der unendliche n>=4-Schwanz wird mit (2.6) und seinem bewiesenen Vorzeichen eingeschlossen. Die Polynomdarstellung in x-3 erhält die nötigen Auslöschungen.

Die höhere Taylor-Koeffizientenrekursion von log(1+epsilon) benötigt keine numerische Logarithmusauswertung. Ist a(z)=sum a_j z^j, so folgen l_j für j>=1 aus a'=a l':

\[
l_n=\frac{n a_n-\sum_{j=1}^{n-1}j l_j a_{n-j}}{n a_0}.
\tag{2.7}
\]

Alle Operationen erfolgen mit nach außen gerundeten ganzzahligen Intervallen mit Nenner 2^144. Für exp(-u), u>=0, wird zunächst auf 0<=u/2^k<=1 skaliert. Die alternierenden Taylor-Summen der Grade 39 und 40 geben eine untere bzw. obere Schranke; anschließendes Quadrieren erhält die Einschließung.

Der ausgeführte zweite Check kontrolliert ausschließlich **exakte rationale** untere Endpunkte. In jeder einzelnen Zelle sind sie größer als:

| Ausdruck | geprüfte rationale Untergrenze |
|---|---:|
| q-18 | 13/20 |
| 3q-q' | 35 |
| 3q+q' | 54 |
| q'' | 120 |
| 10q-q'' | 38 |
| q^(4)+200q | 862 |

Er kontrolliert außerdem Anfang, Ende und jeden gemeinsamen Zellenrand. Das ist kein Test ausgewählter x-Werte, sondern eine endliche Zertifizierung einer vollständigen kompakten Domäne.

### 2.4 Unbeschränkter Bereich x>=8

Die zweite Anwendung von (2.6) kontrolliert nun den **gesamten** epsilon-Term n>=2. (2.7) liefert rationale Schranken l2,l3,l4,l6 für |D^2L|, |D^3L|, |D^4L|, |D^6L|. Insbesondere sind l2,l3,l4<1 und l6<560.

Aus (2.3) und positiven Polynomen in x-8 ergibt sich exakt

\[
q_1\ge4x,\quad0<Dq_1<2q_1,\quad
16x<D^2q_1<8q_1,\quad D^4q_1>0.
\]

Zähler und Nenner dieser Vergleiche werden im Generator kontrolliert. Somit gelten für die sechs geprüften Ausdrücke die unteren Schranken

\[
14-l_2,\quad32-3l_2-l_3,\quad32-3l_2-l_3,
\]
\[
128-l_4,\quad64-10l_2-l_4,\quad6400-200l_2-l_6,
\tag{2.8}
\]

und jede ist strikt positiv. Geradheit von q überträgt alle Aussagen auf t<0, bei q' mit Absolutbetrag. t=0 und x=8 sind abgedeckt. Damit ist (2.1) auf ganz R bewiesen.

### 2.5 Fehlgeschlagene Zertifikate und Vertrauensgrenze

Die registrierten Ungleichungen (2.1) wurden nicht nach Sichtung der Daten verändert. Eine erste Darstellung mit 512 Zellen hatte 90 nicht entscheidende Zellen. Die verschobene Polynomauswertung hatte bei 512 Zellen 29, bei 1024 Zellen 13 und bei 2048 Zellen keine nicht entscheidenden Zellen. Die negativen unteren Einschließungsenden dieser Zwischenläufe wurden **nie** als negative Quellenwerte behandelt.

Ein versuchter Bezug von python-flint scheiterte am Netzwerkzugang. Deshalb wurde kein Arb-Zertifikat erzeugt. Der ausgeführte Verifier ist der hier offengelegte rationale Checker. Hochpräzisions-Gegenrechnungen an sechs rationalen Quellenpunkten und 401 Exponentialargumenten stimmen mit den Intervallen überein; sie sind bloße zusätzliche Plausibilitätskontrollen, nicht die Quantorenbrücke oder eine unabhängige Begutachtung.

## 3. Aus den Quellschranken folgt Profilpositivität bis zur vierten Ordnung

**[ABSTRACT][PAPER]**

Fixiere v, schreibe C=C_v=e^{-R_v} und Q=R_v''. Dann gilt auf ganz R

\[
Q>36,\quad |Q'|<3Q,\quad 0<Q''<10Q,\quad Q^{(4)}>-200Q.
\tag{3.1}
\]

Das folgt aus Q(w)=q(v+w)+q(v-w) und (2.1). Q''' muss nicht separat abgeschätzt werden.

### 3.1 Vier Wronskians mit genauem Vorzeichen

Setze H_n=det[C^(i+j)]_(i,j=0,...,n-1). Die Multiplikation von C mit exp(a w) verändert H_n/C^n nicht: Die Ableitungsmatrix wird links und rechts durch binomiale Dreiecksmatrizen mit Diagonale eins transformiert. An jeder festen Stelle darf dadurch R' auf null gesetzt werden.

Direkte symbolische Differentiation ergibt

\[
H_1=C,\qquad -H_2/C^2=Q,
\]
\[
-H_3/C^3=2Q^3-QQ''+(Q')^2>\frac53Q^3.
\tag{3.2}
\]

Für H_4 lautet das vollständige Polynom, mit r=Q', t=Q'', u=Q''', v_4=Q^(4),

\[
\begin{aligned}
H_4/C^4={}&12Q^6-24Q^4t+24Q^3r^2+2Q^3v_4
 -12Q^2ru+7Q^2t^2\\
&+12Qr^2t-Qt v_4+Qu^2-9r^4+r^2v_4-2rtu+t^3.
\end{aligned}
\tag{3.3}
\]

Definiere

\[
a=Q'/Q^{3/2},\quad b=Q''/Q^2,\quad
c=Q'''/Q^{5/2},\quad d=Q^{(4)}/Q^3.
\]

Die entscheidende **vollständige Quadratergänzung** ist

\[
\begin{aligned}
\frac{H_4}{C^4Q^6}
={}&(c-a(6+b))^2+12-24b+7b^2+b^3\\
&+d(2-b+a^2)-a^2(12+b^2)-9a^4.
\end{aligned}
\tag{3.4}
\]

(3.1) liefert a^2<=1/4, 0<=b<=1/3 und d>=-1/4. Da 12-24b+7b^2+b^3 auf [0,1/3] fällt und sein Endwert 130/27 ist, erhalten wir

\[
\boxed{
\frac{H_4}{C^4Q^6}
\ge\frac{130}{27}-\frac9{16}-\frac{109}{36}-\frac9{16}
=\frac{143}{216}>0.}
\tag{3.5}
\]

Das freie Q''' bleibt im nichtnegativen Quadrat; es wurde nicht mit einer unnötigen Betragsabschätzung zerstört. Die Gleichungen (3.3), (3.4) und der Bruch 143/216 wurden exakt symbolisch kontrolliert.

### 3.2 Die benötigte Chebyshev-Lemma, mit Beweis

**Lemma.** Sind u0,...,u_(n-1) hinreichend glatt und alle initialen Wronskians W(u0,...,uj) positiv, dann ist det[u_j(t_i)]>0 für t1<...<tn.

**Beweis.** Induktion nach n. Für n=1 ist u0>0. Teile im allgemeinen Fall jede Auswertungszeile durch u0(t_i), sodass die erste Spalte eins wird. Ziehe von unten nach oben die jeweils vorherige Zeile ab. Nach Entwicklung entlang der ersten Spalte bleibt eine Matrix von Differenzen der Funktionen u_j/u0. Jede Differenz ist das Integral der Ableitung h_j=(u_j/u0)' auf dem zugehörigen Intervall [t_i,t_(i+1)]. Es gilt exakt

\[
W(h_1,\ldots,h_j)=W(u_0,\ldots,u_j)/u_0^{j+1}>0.
\]

Multilinearität schreibt die verbleibende Determinante als Integral der kleineren Auswertungsdeterminante an geordneten Punkten aus den aufeinanderfolgenden Intervallen. Nach Induktion ist der Integrand im Inneren positiv. Das Integral ist daher positiv. Alle herausgeteilten Faktoren sind positiv. QED.

Wende das Lemma zuerst auf u_j=(-1)^j C^(j), j=0,...,3, an. Ihre initialen Wronskians sind

\[
(-1)^{n(n-1)/2}H_n>0\quad(n\le4).
\]

Fixiere anschließend y1<...<yn. Die Wronskians der übersetzten Funktionen g_j(x)=C(x-y_j) sind ebenfalls positiv. Dies folgt aus der ersten Anwendung mit den in umgekehrter Reihenfolge geordneten x-y_j: das Vorzeichen der Spaltenumkehr hebt das Vorzeichen der Faktoren (-1)^j genau auf.

Eine zweite Anwendung des Lemmas liefert

\[
\boxed{\det[C_v(x_i-y_j)]_{i,j=1}^n>0
\quad(x_1<\cdots<x_n,\ y_1<\cdots<y_n,\ n\le4).}
\tag{3.6}
\]

Dies ist strikte totale Positivität **bis Ordnung vier** des einzelnen Profils. Bei y_i=x_i sind die Matrizen symmetrisch; ihre initialen Hauptminoren sind positiv. Sie sind deshalb positiv definit.

## 4. Vollständiger Vierpunktrest: bezahlt für alle Konfigurationen

**[ABSTRACT][PAPER]**

Seien x1,...,x4 verschieden. Für jeden v ist die Profilmatrix aus (3.6) positiv definit. Also gilt für jedes c in C^4, c!=0,

\[
c^*[k_\sigma(x_i-x_j)]c
=\int c^*[C_v(x_i-x_j)]c\,d\mu_\sigma(v)>0.
\tag{4.1}
\]

Somit

\[
\boxed{[K_\sigma(x_i-x_j)]_{i,j=1}^4\succ0
\quad\text{für alle }\sigma>0\text{ und alle vier verschiedenen reellen Punkte}.}
\tag{4.2}
\]

Es gibt keine Abstands-, Gitter-, Symmetrie- oder Höhenbedingung. Bei wiederholten Punkten werden gleiche Positionen zusammengefasst und man erhält positive Semidefinitheit. Es wird kein gleichmäßiger positiver Eigenwertabstand bei kollidierenden Punkten behauptet.

**Wichtige Grenze:** Positive Mischung erhält positive Definitheit von Gram-Matrizen. Sie erhält nicht automatisch totale Positivität beliebiger unsymmetrischer Auswertungsmatrizen. Für den v-gemittelten Kern wird nur die tatsächlich gebrauchte Gram-Aussage behauptet.

### 4.1 Der ursprüngliche Schurrest und seine untere Darstellung

Fixiere drei verschiedene Anker a1,a2,a3. Setze

\[
A_v=[C_v(a_i-a_j)]_{i,j=1}^3,\quad
b_v(x)=(C_v(a_i-x))_{i=1}^3,
\]
\[
A=\mathbb E A_v,\quad b(x)=\mathbb E b_v(x),\quad
z_v(x)=A_v^{-1}b_v(x),\quad z(x)=A^{-1}b(x).
\]

Die Anker bleiben in der ganzen Rechnung dieselben. Bei fest gewählten Ankern sind A_v gleichmäßig invertierbar in v: sie hängen stetig von v ab, sind positiv definit und konvergieren für |v|->infinity gegen I. Letzteres folgt aus q(t)->infinity und (1.6), das C_v(d)->0 für jeden festen d!=0 ergibt. Dies rechtfertigt die Integrale; eine quantitative uniforme Inversennorm wird nicht als Sign-Lieferant benötigt.

Für einen vierten Punkt x lautet der vollständige normierte Rest

\[
s_4(x)=1-b(x)^*A^{-1}b(x).
\]

Quadratergänzung ergibt exakt

\[
\boxed{
\begin{aligned}
s_4(x)={}&\mathbb E\,[1-b_v(x)^*A_v^{-1}b_v(x)]\\
&+\mathbb E\,[(z_v(x)-z(x))^*A_v(z_v(x)-z(x))].
\end{aligned}}
\tag{4.3}
\]

Für x außerhalb der drei Anker ist bereits der erste Integrand nach (3.6) positiv. Der zweite ist nichtnegativ. Also s4(x)>0 und

\[
\boxed{D_4=\det A-b(x)^*\operatorname{adj}(A)b(x)
       =\det G_4=(\det A)s_4(x)>0.}
\tag{4.4}
\]

(4.3) ist eine echte untere Darstellung. Das Urteil beruht nicht auf dem Scheitern eines anderen Zertifikats.

Bei vier gleichmäßig verteilten Punkten sind mit a=k(h), b=k(2h), c=k(3h) die beiden Paritätsblöcke

\[
\begin{pmatrix}1+c&a+b\\a+b&1+a\end{pmatrix},\qquad
\begin{pmatrix}1-c&a-b\\a-b&1-a\end{pmatrix}.
\]

Beide sind positiv definit. Das Produkt ihrer Determinanten ist exakt det G4; dieser Check wurde ausgeführt. Es wurde kein zweiter Block weggelassen.

## 5. Was dimensionsunabhängig jetzt tatsächlich vorliegt

### 5.1 Vollständiges algebraisches Kriterium, einschließlich Singularität

**[ABSTRACT][PAPER]** Für jede hermitesche Matrix G und einen Vektor b gilt

\[
\begin{pmatrix}G&b\\b^*&1\end{pmatrix}\succeq0
\iff
G\succeq0,\quad b\in\operatorname{Ran}G,\quad1-b^*G^\dagger b\ge0.
\tag{5.1}
\]

G^dagger bezeichnet die Moore-Penrose-Inverse. Die Bereichsbedingung ist zwingend: ein nichtverschwindender Kopplungswert auf einem Nullvektor von G erzeugt durch Skalierung eine negative quadratische Form. Liegt b im Bereich und G ist positiv semidefinit, liefert die Quadratergänzung

\[
u^*Gu+2\Re(\bar t b^*u)+|t|^2
=(u+tG^\dagger b)^*G(u+tG^\dagger b)
+|t|^2(1-b^*G^\dagger b).
\]

Dies beweist beide Richtungen und erfasst jede Dimension. **Es ist ein Kriterium. Es beweist nicht seine letzte Theta-spezifische Ungleichung.**

### 5.2 Ein einziges Restkern-Problem statt neuer Inversen jeder Größe

**[ABSTRACT][PAPER — exakte Identität; CONDITIONAL — Vorzeichen auf beliebigen Punktmengen]**

Benutze weiterhin nur die drei festen Anker aus Abschnitt 4. Definiere

\[
r_v(x,y)=C_v(x-y)-b_v(x)^*A_v^{-1}b_v(y),
\]
\[
r_\sigma(x,y)=k_\sigma(x-y)-b(x)^*A^{-1}b(y).
\]

Die Matrixvarianz-Rechnung polarisiert exakt zu

\[
\boxed{
\begin{aligned}
r_\sigma(x,y)={}&\mathbb E\,r_v(x,y)\\
&+\mathbb E\,[(z_v(x)-z(x))^*A_v(z_v(y)-z(y))].
\end{aligned}}
\tag{5.2}
\]

Zum Nachrechnen wird der zweite Term expandiert. Wegen E A_v=A und E A_v z_v(x)=E b_v(x)=b(x) verschwinden die beiden Kreuzterme genau bis auf den einen mittleren Schurwert.

Diese Identität gilt gleichzeitig für beliebig viele zusätzliche Punkte. Der zweite Term ist ein echter positiver Gram-Kern. Für jeden Koeffizientenvektor c lautet die notwendige verbleibende Abschätzung

\[
\boxed{
\sum_{i,j}\bar c_i c_j\mathbb E r_v(x_i,x_j)
+\int\left\|\sum_i c_i A_v^{1/2}(z_v(x_i)-z(x_i))\right\|^2d\mu_\sigma(v)
\ge0.}
\tag{5.3}
\]

Sie ist für **jedes** sigma im relevanten Bereich, **jede** endliche Punktmenge und **jeden** komplexen Koeffizientenvektor nötig. Auf der Diagonalen ist sie durch den Vierpunktbeweis bezahlt. Off-diagonale endliche Matrizen von r_sigma sind dadurch nicht bezahlt.

Die positive Ankerkomponente b(x)^*A^-1 b(y) stellt den alten Kern exakt wieder her. Damit ist positive Definitheit des ganzen Kerns äquivalent zur Positivität dieses einen Restkerns, wenn beliebige Punkte einschließlich der Anker zugelassen werden. Das ist kein anderer Quellterm und kein frei gewählter Ersatzkern.

**Der noch offene Teil ist die quantitative oder strukturelle Kontrolle der ersten, möglicherweise vorzeichenwechselnden Größe durch die zweite. Es wird nicht behauptet, dass eine positive Varianz automatisch groß genug ist.**

## 6. Warum die profilweise Erweiterung auf alle Dimensionen nicht funktionieren kann

**[ABSTRACT][PAPER — importierter Satz von Hudson plus eigene Quellabbildung]**

Setze psi=Phi/||Phi||2. Die Wigner-Funktion in einer bis auf einen positiven Faktor üblichen Konvention lautet

\[
W_\psi(v,\omega)=\int_{\mathbb R}\psi(v+w)\psi(v-w)e^{-2i\omega w}\,dw.
\tag{6.1}
\]

Für jedes feste v ist sie ein positiver Skalar mal dem Fourier-Transformierten von C_v an 2omega.

**Hudsons Satz:** Ein normierter reiner L2-Zustand hat genau dann eine überall nichtnegative Wigner-Funktion, wenn er die Exponentialfunktion eines quadratischen Polynoms ist. Verwendet wird der Originalsatz in S3, Abschnitt 4; die entsprechende gedruckte Seite 251 wurde visuell kontrolliert. Dies ist ein Import, keine neue Behauptung dieses Berichts.

Unsere positive gerade Quelle ist nicht gaußförmig: bereits q''>0 aus Satz 2.1 schließt konstante logarithmische Krümmung aus. Auch ihr doppelt-exponentieller Abfall zeigt dies.

Wären sämtliche C_v in jeder endlichen Dimension positiv definit, dann wären ihre Fourier-Transformierten überall nichtnegativ, folglich W_psi>=0. Dies widerspricht Hudson. Also gibt es für mindestens ein echtes Theta-Mittelpunktprofil eine negative endliche Gram-Richtung. Nach Abschnitt 3 muss sie mindestens fünf verschiedene Positionen benötigen.

Es wurden keine konkreten Koordinaten dieser negativen Profilmatrix berechnet; dies ist ein Existenzbeweis durch den importierten Satz und die folgende Testfunktionskonstruktion, kein ausgegebener Arb-Zeuge. Eine negative Wigner-Stelle besitzt aufgrund der Stetigkeit eine strikt negative lokale obere Schranke. Eine dort lokalisierte Fourier-Testfunktion und anschließend hinreichend feine endliche Riemann-Summen erzeugen eine strikt negative endliche Profilform.

Der verwendete elementare Fourier-Schritt benötigt keinen numerischen Nullstellentest: Positivität aller endlichen Gram-Summen geht durch Riemann-Summen auf Testfunktionsintegrale über. Eine negative offene Stelle der stetigen Fourier-Transformierten wird durch eine frequenzlokalisierte Testfunktion erkannt und widerspricht dieser Integralenpositivität.

**Die Unmöglichkeit betrifft genau die stärkere Forderung „jedes Profil separat in jeder Dimension positiv“.** Sie beweist weder die Negativität der vollständigen v-Mischung noch eine negative Richtung von V. Die Gewichte in (1.7) sind fest an den Quellterm und an sigma gebunden; sie dürfen nicht willkürlich auf eine negative Wigner-Region konzentriert werden.

Daraus folgt eine klare Arbeitsentscheidung: Nicht mechanisch den profilweisen Vierpunktbeweis auf fünf, sechs, ... Punkte erweitern. Irgendwann muss diese stärkere Familie scheitern. Für das Gesamtziel muss (5.3) die vollständige Mischung einschließlich der Kompensation erhalten.

## 7. Der genaue Übergang zum vollständigen HB-Vorzeichen

**[ABSTRACT][CONDITIONAL bezüglich der weiterhin offenen Prämisse; PAPER für die Implikationen]**

Für jedes feste sigma ist der volle Kern K_sigma glatt und schnell fallend. Deshalb sind äquivalent:

\[
[K_\sigma(x_i-x_j)]\succeq0\quad\text{für alle endlichen Punktmengen},
\]
\[
\widehat K_\sigma(\omega)\ge0\quad\text{für alle reellen }\omega,
\]
\[
\mathscr H(\sigma+i\tau)\ge0\quad\text{für alle reellen }\tau.
\tag{7.1}
\]

Die Rückrichtung von der Fourier-Seite folgt durch Fourier-Inversion und

\[
\sum\bar c_iK_\sigma(x_i-x_j)c_j
=\frac1{2\pi}\int\widehat K_\sigma(\omega)
\left|\sum_j c_je^{-i\omega x_j}\right|^2d\omega.
\]

Die Vorwärtsrichtung folgt durch Testfunktionen und Frequenzlokalisierung wie in Abschnitt 6. (1.5) bezahlt alle Konstanten.

Ein bekannter äußerer Bereich wird nicht als neuer Erfolg gezählt: S4, Gleichung (1.4), liefert ohne RH

\[
\Re(\xi'(s)/\xi(s))>0\quad(\Re s>1).
\]

Damit ist das volle Vorzeichen in unseren Koordinaten für sigma>1/2 vorhanden. Stetigkeit gibt Nichtnegativität für sigma=1/2. Der weiterhin unbezahlte innere Bereich ist folglich

\[
\boxed{0<\sigma<1/2,\quad\tau\in\mathbb R.}
\tag{7.2}
\]

Die Endpunkte bei tau=0 sind nicht das Problem: dort sind F(sigma), F'(sigma)>0 direkt aus dem Quellenintegral. Es fehlt die Kontrolle aller Oszillationshöhen. S4 nennt auch die RH-äquivalente Positivitätsbedingung für Re s>1/2. Diese Äquivalenz ist keine Unmöglichkeit des Ansatzes; sie ist die genaue Beweiskraft der offenen Ungleichung.

## 8. Wenn das volle Vorzeichen bezahlt ist: SUPPORT für denselben Multiplikator

**[ABSTRACT][CONDITIONAL]** Nehme in diesem Abschnitt zusätzlich das **vollständige**, nicht nur vierdimensionale Vorzeichen aus (7.1) für alle sigma>0 an.

Aus

\[
\mathscr H=2\partial_\sigma|F|^2\ge0
\]

folgt Nullstellenfreiheit von F auf Re p>0. Denn ein Nullwert bei sigma0+i tau0 würde durch Monotonie |F|^2=0 auf dem ganzen horizontalen Segment 0<sigma<sigma0 erzwingen. Die Identitätstheorie widerspricht F(0)!=0. Wegen Geradheit liegen dann alle Nullstellen von F auf der imaginären Achse.

Jetzt, und erst jetzt, ist die Division durch F im Inneren legitim. Setze

\[
L(p)=F'(p)/F(p),\quad \Re L\ge0,
\]
\[
M(p)=\frac1{1+L(p)}=\frac{F(p)}{F(p)+F'(p)}.
\]

M ist auf Re p>0 holomorph und |M|<=1. Seine Randwerte sind genau die alten Multiplikatorwerte m(y)=M(iy), nicht ein nachträglich konstruierter positiver Ersatz. Mit X(z)=xi(1/2-iz) ist die konsistente Koordinate z=ip.

Hier folgt der Trägernachweis auch direkt. Für eine Testfunktion phi mit kompaktem Träger in (-infinity,0) setze

\[
J(p)=\int\phi(t)e^{pt}\,dt.
\]

Die Paarung des ursprünglichen Y=F^-1 m mit phi lautet

\[
\langle Y,\phi\rangle=\frac1{2\pi}\int_{\mathbb R}M(iy)J(iy)\,dy.
\]

Verschiebe die vertikale Kontur auf Re p=a>0. Die horizontalen Integrale verschwinden wegen mehrfacher partieller Integration in J und |M|<=1. Liegt supp phi unter -delta<0, gilt für jedes feste N eine Schranke

\[
|J(a+iy)|\le C_N(1+a)^N e^{-a\delta}(1+|y|)^{-N}.
\]

Somit geht das verschobene Integral für a->infinity gegen null. Der Übergang vom Rand Re p=0 zu Re p=epsilon ist durch beschränkte Randwerte und Dominierung zulässig. Daraus folgt

\[
\boxed{\operatorname{supp}Y\subseteq[0,\infty).}
\tag{8.1}
\]

Die alte Gleichung mit rho=Phi/xi(1/2), `((1-t)rho)*Y=rho`, bleibt dieselbe; ihr ganzer Multiplikator wird nicht verändert. Der aus S2 bekannte bedingte Kausalitätsübergang erhält damit dieselbe Quelle. **Die benötigte globale Vorzeichenprämisse wurde durch Abschnitt 4 nicht bewiesen.**

## 9. Wenn das volle Vorzeichen bezahlt ist: ein exakter Quadratausdruck für die ursprüngliche Form V

**[ABSTRACT][CONDITIONAL — kein unabhängiger Quellbeweis des Vorzeichens]**

Unter derselben noch offenen globalen Prämisse liegen die Nullstellen von X(z)=xi(1/2-iz) sämtlich auf der reellen Achse. Schreibe sie als ±gamma mit positiven gamma und Multiplizität m_gamma. Die klassische Eigenschaft „gerade ganze Funktion der Ordnung eins“ und X(0)!=0 liefern die gepaarte Hadamard-Faktorisierung

\[
X(z)=X(0)\prod_{\gamma>0}(1-z^2/\gamma^2)^{m_\gamma},
\quad\sum_{\gamma>0}m_\gamma/\gamma^2<\infty.
\tag{9.1}
\]

Ordnung und Faktorisierung gehören zu den klassischen xi-Eigenschaften (S4). Die **Realität der Nullstellen in dieser Anwendung ist dagegen eine Folge der noch offenen Prämisse.** Es wird keine Einfachheit der Nullstellen angenommen. Geradheit beseitigt einen linearen Exponentialfaktor; Ordnung eins schließt einen quadratischen Exponentialfaktor aus.

Für jede reelle Nullstelle, positiv oder negativ, definiere mit dem unveränderten f aus (1.2)

\[
\psi_\gamma(x)=\int_0^\infty f(x+t)e^{-i\gamma t}\,dt.
\tag{9.2}
\]

Dann gilt exakt

\[
\boxed{V(x,y)=\sum_{\gamma\in Z(X)}m_\gamma
             \overline{\psi_\gamma(x)}\psi_\gamma(y).}
\tag{9.3}
\]

### Beweis und Konvergenz

Partielle Integration liefert auf kompakten x-Intervallen psi_gamma=O(1/|gamma|). Die Summanden in (9.3) sind deshalb nach (9.1) absolut und lokal gleichmäßig summierbar. Außerdem gilt

\[
\psi_\gamma'(x)=-f(x)+i\gamma\psi_\gamma(x).
\tag{9.4}
\]

Im Fourier-Sinn ist

\[
\widehat{\psi_\gamma}(y)=i\frac{\widehat f(y)}{y-\gamma}.
\tag{9.5}
\]

Die Fourier-Transformierte des einseitigen Exponentials enthält zunächst einen Delta-Anteil und einen Hauptwert. Der Delta-Anteil verschwindet wegen hat f(gamma)=0, der Quotient ist an gamma fortsetzbar. Somit sind keine Singularitäten versteckt.

Die gepaarte logarithmische Ableitung von (9.1) ergibt

\[
\sum_\gamma^{\rm paired}m_\gamma\psi_\gamma(x)=x f(x).
\tag{9.6}
\]

Zur Rechtfertigung: Die führenden Terme f(x)/(i gamma) und f(x)/(-i gamma) heben sich auf. Zweimalige partielle Integration gibt für jedes positive gamma

\[
|\psi_\gamma(x)+\psi_{-\gamma}(x)|
\le\frac{2}{\gamma^2}
\left(|f'(x)|+\int_x^\infty|f''(u)|\,du\right).
\]

Die gepaarte Summe ist daher lokal gleichmäßig konvergent. Auf der Fourier-Seite konvergiert dieselbe Summe distributionell zu `i hat f'`: auf |y|<=gamma/2 liefert der gepaarte Quotient einen O(gamma^-2)-Faktor; auf dem Komplement liefern der schnelle Abfall von hat f und ihren Ableitungen sowie die hebbaren Nullstellen denselben summierbaren Testfunktionsrest. Eindeutigkeit der Fourier-Transformation beweist (9.6).

Setze S(x,y)=rechte Seite von (9.3), zunächst symmetrisch endlich abgeschnitten. Mit (9.4) heben sich die i-gamma-Terme unter gleichzeitiger Translation auf. (9.6) erlaubt anschließend den Grenzübergang:

\[
\frac{d}{da}S(x+a,y+a)
=-(x+y+2a)f(x+a)f(y+a).
\]

Die partiellen Integrationsschranken zeigen S(x+a,y+a)->0 für a->infinity. Integration von a=0 bis infinity beweist exakt (9.3), mit dem Faktor x+y+2t und der Normalisierung aus (1.2).

Damit folgt für jede endliche komplexe Gewichtung

\[
\boxed{
\sum_{i,j}\bar c_iV(x_i,x_j)c_j
=\sum_{\gamma\in Z(X)}m_\gamma
 \left|\sum_jc_j\psi_\gamma(x_j)\right|^2\ge0.}
\tag{9.7}
\]

**Das ist ein Quadratausdruck der ursprünglichen V, nicht die Behauptung `||Ru||^2=V`. Er darf nicht rückwärts als unabhängiger RH-Beweis verwendet werden, weil die reellen Frequenzen gamma noch durch das globale HB-Vorzeichen bezahlt werden müssen.**

## 10. Gesamtstand ohne fünf getrennte Scheinabschlüsse

| Geforderter Teil | Tatsächliches Ergebnis dieser Runde |
|---|---|
| Vollständiger Vierpunktrest | positiver Papierbeweis für alle sigma>0 und beliebige vier Positionen; Quelllemma rational-intervallzertifiziert |
| Dimensionsunabhängige Schur-Regel | Identität und singularitätsbewusstes Kriterium bewiesen; vollständige Theta-Vorzeichenfortpflanzung (5.3) offen |
| Gesamtes HB-Vorzeichen | exakter Fourier-Verbraucher; äußerer Bereich klassisch bezahlt; innerer Bereich (7.2) offen |
| SUPPORT | aus demselben noch offenen vollen HB-Zeichen durch den Konturbeweis hergeleitet; für die tatsächliche Quelle nicht neu bewiesen |
| Ursprüngliche V | explizite bedingte Quadratdarstellung (9.3); ihre globale Voraussetzung nicht bewiesen; kein negativer V-Zeuge |

**Die unbezahlte Aussage ist nicht mehr das algebraische Vorhandensein einer Schur-Rekursion. Es ist die dominierende Wirkung der vollständigen Quellenmischung auf ihre signierten Restkerne, mit allen endlichen Punktmengen als Quantor.**

### Zwei zulässige Darstellungen des offenen Teils

**R1 — gemeinsame Schur-Rest- und Varianzabschätzung, ausgewählt.** Der unveränderte Kern wird mit drei festen Ankern nach (5.2) zerlegt. Ziel ist (5.3), unmittelbar für beliebige endliche Gewichtungen. Entscheidende Kraft 10/10; verbleibende Beweiskosten hoch, heuristisch 9/10. Kein zusätzlicher Inversenboden in wachsender Dimension wird vorausgesetzt.

**R2 — gewichtete Wigner-Kompensation.** Aus (1.4) und (6.1) folgt

\[
\widehat K_\sigma(2\tau)=A^2\int v\sinh(2\sigma v)W_\psi(v,\tau)\,dv.
\]

W_psi muss selbst Vorzeichen wechseln; das Integral kann dennoch nichtnegativ sein. Hier wäre eine Theta-spezifische, nicht profilweise Kompensationsidentität direkt am signierten Gesamtintegral nötig. Entscheidende Kraft 10/10; übrige Kosten unbekannt/hoch. Diese Form bewahrt beide Variablen und darf nicht durch einen beliebigen positiven Wigner-Ersatz verändert werden.

Das sind Forschungsdarstellungen, keine Behauptung, dass die fehlende Ungleichung dadurch leichter geworden sei. Die unmittelbar erforderliche neue Mathematik ist bei R1 eine globale Quellenabschätzung für (5.3), nicht ein weiterer neuer Name dafür. Es wurde kein CodeX-Job gestartet und keine längere Matrixsuche autorisiert.

## 11. K8A: Abhängigkeiten, Zurückweisung und Wiederaufnahme

**DOWNSTREAM_CONSUMER:** das volle HB-Vorzeichen für den identischen F, daraus Nullstellenfreiheit, ursprüngliches M/Y und ursprüngliche V.

**ACTUAL_CONSUMER_REQUIREMENT:** `H(sigma+i tau)>=0` für alle sigma>0, tau reell, äquivalent zu voller K-Gram-Positivität. Der äußere Bereich ist bereits klassisch bekannt; die Quelle muss den inneren Bereich (7.2) ohne RH-Prämisse bezahlen.

**ORIGINAL_REQUESTED_OBJECT:** voller Vierpunktrest plus beliebigdimensionale Vorzeichenfortpflanzung.

**ORIGINAL_OBJECT_IS:** der Vierpunktrest ist notwendig für die volle Gram-Aussage, nicht hinreichend. Die speziellen Krümmungsschranken sind ein hinreichender, nicht als notwendig behaupteter Beweisweg. Die profilweise all-dimensionale Positivität ist kein notwendiger Zwischenschritt und sogar inkompatibel mit der exakten Quelle.

**KNOWN_WEAKER_INTERFACES:** die gekoppelte vollständige Restungleichung (5.3), oder direkt das gewichtete Wigner-Gesamtintegral >=0, reicht. Einzelne Profilreste müssen nicht positiv sein. Ein direkter HB-Beweis kann die Schur-Zerlegung vollständig umgehen.

**FAILURE_TYPE / EPISTEMIC_STATUS:** Für die volle Mischung `NO_DERIVATION / RESEARCH_DEBT`; kein Unmöglichkeitsbeweis. Für die explizite profilweise all-dimensionale Aussage `INCOMPATIBILITY / MATHEMATICALLY_DEAD_FOR_THIS_STATEMENT_ONLY`, Beleg Abschnitt 6 plus S3. KILL_SCOPE ist nur THEOREM_SHAPE, nicht ROUTE_FAMILY.

**REOPEN_TRIGGER:** Eine neue quellenseitige vollständige Quadrat-/Restidentität, ein bewiesener Vergleich, der (5.3) schließt, oder ein streng negativer oberer Einschluss für eine quadratische Form des vollständigen K. Mehr Profil-Dimensionen allein sind nach Abschnitt 6 kein Wiederaufnahmegrund für die zurückgewiesene universelle Profilforderung.

**NOVELTY_AXIS:** aktuelle exakte Quellschranken und ihre Vierpunktanwendung; Vollmischungs-Schurorganisation. Es wird keine Priorität in der mathematischen Literatur beansprucht. Hudson, Hadamard und der bekannte xi-Positivitätsverbraucher sind ausdrücklich Importe.

## 12. Vorregistrierungen und Abschluss

Die beiden Registrierungsdateien entstanden vor den jeweiligen Tests und bleiben unverändert:

- P_MIXTURE_SCHUR, 0.90: bestätigt durch (4.3), (5.2).
- P_PROFILE_ALLDIM, 0.85: bestätigt als Unvereinbarkeit des exakten Profilansatzes durch Abschnitt 6. Dies ist kein negativer Zeuge für den v-Mittelwert.
- P_FULL_4, 0.70: bestätigt auf dem gesamten registrierten Vierpunktbereich durch Abschnitte 2–4, vorbehaltlich unabhängiger Prüfung des hier vorgelegten Papierbeweises.
- P_SOURCE_CLOSURE, 0.95: bestätigt in der registrierten methodischen Bedeutung: bloße Schur-Algebra bezahlt nicht ihr eigenes Vorzeichen; der fehlende volle Quelleninput bleibt sichtbar.
- Zweite Registrierung, Quelle (2.1), 0.65: bestätigt durch die vollständige kompakte Intervallabdeckung plus unbeschränkten analytischen Schwanz. Kein Austausch der Zielkonstanten nach den Tests.

Die ältere Hoffnung auf einen vollständigen Theta-Quadratzerlegungsbeweis ist **nicht** durch den Vierpunktbeweis bestätigt; ihr globaler Teil bleibt offen.

**Was wurde geschlossen?** Der gesamte Vierpunktrest, nicht nur eine Zelle oder ein Abstandsregime.

**Was wurde ausgeschlossen?** Die all-dimensionale Positivität jedes einzelnen tatsächlichen Theta-Profils.

**Was wird nicht wiederholt?** Die Gleichsetzung von positiver Mischung mit positiven Einzelprofilen in jeder Dimension; endlose kleine-Matrizen-Fortsetzung als Ersatz für den Quantor.

**Kleinster klar benannter offener Gegenstand:** die gemeinsame Quellenrest-Dominierung (5.3) auf beliebigen endlichen Punktmengen. Der Name bezeichnet hier einen Arbeitsgegenstand, keinen neu eingetragenen Produktionskatalogknoten.

**Strategieeintrag:** `PROOF_PROGRESS; REPRESENTATION_SHIFT; finite profile order four paid; all-order profile lift incompatible; preserve the complete midpoint mixture and its cross terms; do not promote a Schur identity to source positivity.`

**Ausführung:** Keine Repository-Schreiboperation, kein Lean-Code, keine Zustandsänderung, kein RH-Export. Daher keine Git-Commit- oder Kernel-Quittung. Sämtliche Dateien in diesem Paket sind lokale Forschungsartefakte.

## 13. Referenzen und genaue Pins

**S1.** `Malaeu/chen_q3`, `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Commit `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`, Blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`; Abschnitte 1–2 wurden für Definitionen und Quellenregularität gelesen. Der Bericht trägt selbst `PAPER_AUDIT_PENDING_INDEPENDENT_CHECK`; keine neue unabhängige Gesamtaufnahme hier.

**S2.** `Malaeu/chen_q3`, `docs/Codex/REPORT_2026-09-17_BOUNDARY_ENERGY_CAUSALITY_AUDIT.md`, Commit `3f3a5b496a01d10a3399313a27916a43f0f70183`, Blob `7259c3164515c79678d6d09009da157df763c3e3`; A0–A5 für ursprüngliche Multiplikatoren, Träger und deren begrenzten Annahmestatus.

**S3.** R. L. Hudson, *When is the Wigner quasi-probability density non-negative?*, Reports on Mathematical Physics 6 (1974), 249–252, DOI `10.1016/0034-4877(74)90007-X`. Originalsatz in Abschnitt 4, gedruckte Seite 251. Primär-PDF: `https://denebola.if.usp.br/~jbarata/leituras-recomendadas/Hudson-WignerFunctionPositivity.pdf`.

**S4.** Jeffrey C. Lagarias, *On a Positivity Property of the Riemann xi-Function*, Autoren-PDF, Einleitung, Gleichungen (1.1)–(1.5). Originalseite visuell gelesen. `https://websites.umich.edu/~lagarias/doc/positivity.pdf`.

**S5.** Vorheriges lokales Artefakt `FULL_THETA_THREE_POINT_CLOSURE_2026-09-17.md`; seine exakten algebraischen Checks wurden erneut ausgeführt. Der vorliegende stärkere Ableitungs- und Vierpunktbeweis ist eigenständig im folgenden Programmblock reproduzierbar.

**Projektprotokoll.** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, Branch `rh_clean`, gelesener Blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Aktuelle Aufgabe ist die direkte Fortsetzung des Eigentümer-Auftrags, nicht die Verarbeitung eines neuen CodeX-Bus-Pakets.

## 14. Reproduktion des rationalen Zertifikats

Die folgenden vier Programme werden im **selben Ordner** gespeichert. `BASE` bzw. `Path(__file__).parent` bedeutet genau den Ordner des jeweiligen Programms; es ist kein anzupassender Repository-Pfad. Die beiden Generatoren und der Symbolcheck benötigen Python mit SymPy. Der zentrale Intervallchecker selbst benutzt nur die Standardbibliothek.

Aus diesem Ordner wurden die folgenden Befehle ausgeführt:

```bash
python build_tail.py
python build_source_polys.py
python cert_source_final.py
python check_final_algebra.py
```

Die Generatoren erzeugen ausschließlich die neben ihnen liegenden JSON-Tabellen. Der Intervallchecker erzeugt alle Zellenquittungen; der letzte Check kontrolliert exakte positive Grenzen, vollständige Deckung, äußeren Schwanz, die W4-Identität und beide Vierpunkt-Paritätsblöcke. Dezimalausgaben im Protokoll werden nicht in Beweisvergleichen verwendet.

Die Integrations- und Chebyshev-Argumente aus Abschnitten 1–9 sind der analytische Teil des Beweises. Die Programme prüfen nicht automatisch diesen gesamten Text.

### 14.1 `build_tail.py`

```python
import sympy as s,json
from pathlib import Path
x,m,y,z=s.symbols('x m y z')
B=m*(2*m*x-3)/(2*x-3)
res={}
for x0,n0,E,name in [(s.Rational(31,10),4,22,'tail_n4'),(s.Integer(8),2,2980,'tail_x8')]:
 assert sum(x0**k/s.factorial(k) for k in range(40))>E
 C=B;rows=[]
 for j in range(7):
  P=s.Poly(s.factor((-1)**j*C.subs(x,x0)),m)
  p=n0*n0; cc=sum(abs(co)*p**power[0] for power,co in P.terms())
  # n^degree exponential tail ratio at n>=n0; check <1/2
  rat=s.Rational(n0+1,n0)**(2*(j+2))/s.Integer(E)**(2*n0+1)
  assert rat<s.Rational(1,2)
  ub=2*cc/s.Integer(E)**(p-1)
  rows.append(str(ub));print(name,j,float(ub))
  C=s.factor(2*x*(s.diff(C,x)-(m-1)*C))
 res[name]=rows
# sign-polys Tj(z+24)
T=s.Integer(1)
for j in range(8):
 assert all(co>0 for co in s.Poly(s.expand(T.subs(z,y+24)),y).all_coeffs())
 T=s.expand(z*(T-s.diff(T,z)))
q=4*x+24*x/(2*x-3)**2
D=lambda f:2*x*s.diff(f,x)
dq=D(q);ddq=s.factor(D(dq));d4q=s.factor(D(D(ddq)))
for name,f in [('dq',dq),('2q_dq',2*q-dq),('ddq_16x',ddq-16*x),('8q_ddq',8*q-ddq),('d4q',d4q)]:
 num,den=s.fraction(s.factor(f));coeff=s.Poly(s.expand(num.subs(x,y+8)),y).all_coeffs()
 print(name,'positive',all(co>=0 for co in coeff),s.factor(f))
 assert all(co>=0 for co in coeff) and any(co>0 for co in coeff)
 dc=s.Poly(s.expand(den.subs(x,y+8)),y).all_coeffs()
 assert all(co>=0 for co in dc) and any(co>0 for co in dc)
res['tail_x8_use_e8_lower']=2980
assert sum(s.Integer(8)**k/s.factorial(k) for k in range(40))>2980
Path(__file__).with_name('tail_bounds.json').write_text(json.dumps(res,indent=2)+'\n')
```

### 14.2 `build_source_polys.py`

```python
"""Generate exact rational polynomials for the certified full-source derivatives."""
import sympy as s,json
from pathlib import Path
x,y=s.symbols('x y')
D=lambda f:2*x*s.diff(f,x)
def pdata(f):
 n,d=s.fraction(s.factor(f))
 return [[str(c) for c in s.Poly(s.expand(v.subs(x,y+3)),y).all_coeffs()] for v in [n,d]]
res={'eps':{},'qone':{}}
for m in [4,9]:
 f=m*(2*m*x-3)/(2*x-3)
 res['eps'][str(m)]=[]
 for j in range(7):
  res['eps'][str(m)].append(pdata(f))
  f=s.factor(2*x*(s.diff(f,x)-(m-1)*f))
f=4*x+24*x/(2*x-3)**2
for j in range(5):
 if j in [0,1,2,4]:res['qone'][str(j)]=pdata(f)
 f=s.factor(D(f))
Path(__file__).with_name('source_polys.json').write_text(json.dumps(res,indent=2)+'\n')
```

### 14.3 `cert_source_final.py`

```python
"""Outward-rounded rational fixed-point interval certificate, not Arb or Lean.
All transcendental enclosures use finite Taylor sums with a proved remainder sign.
"""
from fractions import Fraction as F
from math import factorial
import json,time,hashlib
from pathlib import Path
P=144; S=1<<P
class I:
 __slots__=('lo','hi')
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.lo=a;self.hi=b;return
  a=F(a);b=a if b is None else F(b)
  self.lo=(a.numerator*S)//a.denominator
  self.hi=-((-b.numerator*S)//b.denominator)
 @staticmethod
 def c(x): return x if isinstance(x,I) else I(x)
 def __add__(self,x):
  x=I.c(x);return I(self.lo+x.lo,self.hi+x.hi,True)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo,True)
 def __sub__(self,x):return self+-I.c(x)
 def __rsub__(self,x):return I.c(x)+-self
 def __mul__(self,x):
  x=I.c(x);a=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
  return I(min(a)//S,-((-max(a))//S),True)
 __rmul__=__mul__
 def __truediv__(self,x):
  x=I.c(x)
  if x.lo<=0<=x.hi:raise ZeroDivisionError((x.lo,x.hi))
  vv=[F(a*S,b) for a in [self.lo,self.hi] for b in [x.lo,x.hi]]
  ll=min(vv);uu=max(vv)
  return I(ll.numerator//ll.denominator,-((-uu.numerator)//uu.denominator),True)
 def __rtruediv__(self,x):return I.c(x)/self
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  out=I(1);b=self
  while n:
   if n&1:out=out*b
   n//=2
   if n:b=b*b
  return out
 def floats(self):return [float(F(self.lo,S)),float(F(self.hi,S))]
 def exact(self):return [str(F(self.lo,S)),str(F(self.hi,S))]

def exp_endpoint_minus(a):
 assert a>=0
 k=max(0,a.bit_length()-P)
 y=I(F(a,S*(1<<k)))
 assert y.hi<=S
 term=I(1);sm=I(1);low=None
 for j in range(1,41):
  term=term*(-y)/j;sm=sm+term
  if j==39:low=sm.lo
 out=I(max(0,low),sm.hi,True)
 for j in range(k):out=out*out
 return out

def exp_minus(x):
 assert x.lo>=0
 return I(exp_endpoint_minus(x.hi).lo,exp_endpoint_minus(x.lo).hi,True)
N=6

def Jconst(x):return [I.c(x)]+[I(0) for _ in range(N)]
def Jadd(a,b):return [x+y for x,y in zip(a,b)]
def Jscale(a,c):return [x*c for x in a]
def Jmul(a,b):return [sum((a[j]*b[n-j] for j in range(n+1)),I(0)) for n in range(N+1)]
def Jinv(a):
 b=[1/a[0]]
 for n in range(1,N+1):b.append(-sum((a[j]*b[n-j] for j in range(1,n+1)),I(0))/a[0])
 return b
def JexpnegX(x,b):
 a=[-b*x*F(2**j,factorial(j)) for j in range(N+1)]
 e=[exp_minus(x*b)]
 for n in range(1,N+1):e.append(sum((j*a[j]*e[n-j] for j in range(1,n+1)),I(0))/n)
 return e
def Jlog(a):
 # Constant logarithm never used; higher coefficients use only rational arithmetic.
 l=[I(0)]
 for n in range(1,N+1):
  l.append((n*a[n]-sum((j*l[j]*a[n-j] for j in range(1,n)),I(0)))/(n*a[0]))
 return l
BASE=Path(__file__).parent
bounds=json.loads((BASE/'tail_bounds.json').read_text())
tail=[F(a) for a in bounds['tail_n4']]

POLYS=json.loads((BASE/'source_polys.json').read_text())
def horner(coeff,z):
 out=I(0)
 for c in coeff:out=out*z+F(c)
 return out
def rat_eval(data,z):return horner(data[0],z)/horner(data[1],z)
def source(x):
 z=x-3
 es={m:exp_minus(x*(m-1)) for m in [4,9]}
 ej=[]
 for j in range(N+1):
  v=sum((rat_eval(POLYS['eps'][str(m)][j],z)*es[m] for m in [4,9]),I(0))
  v=v+(I(0,tail[j]) if j%2==0 else I(-tail[j],0))
  ej.append(v/factorial(j))
 ej[0]=ej[0]+1
 L=Jlog(ej)
 vals=[]
 for j in [0,1,2,4]:vals.append(rat_eval(POLYS['qone'][str(j)],z)-L[j+2]*factorial(j+2))
 return tuple(vals)
names=['q-18','3q-qp','3q+qp','qpp','10q-qpp','q4+200q']
mins=[None]*6;fails=[];rows=[]
start=F(31,10);end=F(8);cells=2048;t0=time.time()
for i in range(cells):
 l=start+(end-start)*F(i,cells);u=start+(end-start)*F(i+1,cells)
 q,qp,qpp,q4=source(I(l,u))
 margins=[q-18,3*q-qp,3*q+qp,qpp,10*q-qpp,q4+200*q]
 vals=[x.lo for x in margins]
 for j,val in enumerate(vals):mins[j]=val if mins[j] is None else min(mins[j],val)
 if min(vals)<=0:fails.append({'cell':i,'x':[str(l),str(u)],'lower':[float(F(z,S)) for z in vals]})
 rows.append([str(l),str(u)]+[str(z) for z in vals])
# Semi-infinite x >= 8: all omitted epsilon derivatives are sign-alternating.
eb=[F(a) for a in bounds['tail_x8']]
eps=[I(0,a/factorial(j)) if j%2==0 else I(-a/factorial(j),0) for j,a in enumerate(eb)]
eps[0]=eps[0]+1
Lg=Jlog(eps)
Labs={j:max(abs(Lg[j].lo),abs(Lg[j].hi))*F(factorial(j),S) for j in [2,3,4,6]}
outer=[14-Labs[2],32-3*Labs[2]-Labs[3],32-3*Labs[2]-Labs[3],128-Labs[4],64-10*Labs[2]-Labs[4],6400-200*Labs[2]-Labs[6]]
report={'verifier':'exact outward-rounded dyadic intervals + rational Taylor bounds; not Arb or Lean','precision_bits':P,'domain':'[31/10,8] plus analytic tail x>=8','cells':cells,'finite_pass':not fails,'failed_cells':fails,'finite_min_lower_bounds':dict(zip(names,[float(F(z,S)) for z in mins])),'outer_log_derivative_abs':{str(k):str(v) for k,v in Labs.items()},'outer_positive_margins':dict(zip(names,[str(v) for v in outer])),'outer_pass':all(v>0 for v in outer),'elapsed_seconds':time.time()-t0}
(BASE/'source_cert_results.json').write_text(json.dumps(report,indent=2)+'\n')
(BASE/'source_cert_rows.json').write_text(json.dumps(rows)+'\n')
print(json.dumps(report,indent=2))
```

### 14.4 `check_final_algebra.py`

```python
import sympy as s,json,hashlib
from fractions import Fraction as F
from pathlib import Path
B=Path(__file__).parent
q,r,t,u,v=s.symbols('q r t u v')
W=12*q**6-24*q**4*t+24*q**3*r**2+2*q**3*v-12*q**2*r*u+7*q**2*t**2+12*q*r**2*t-q*t*v+q*u**2-9*r**4+r**2*v-2*r*t*u+t**3
A,C,D,E=s.symbols('A C D E',real=True)
normal=s.expand(W.subs({r:A*q**s.Rational(3,2),t:C*q**2,u:D*q**s.Rational(5,2),v:E*q**3})/q**6)
complete=(D-A*(6+C))**2+12-24*C+7*C**2+C**3+E*(2-C+A**2)-A**2*(12+C**2)-9*A**4
assert s.simplify(normal-complete)==0
lower=s.Rational(130,27)-s.Rational(9,16)-s.Rational(109,36)-s.Rational(9,16)
assert lower==s.Rational(143,216)>0
# Direct symbolic local derivative/Hankel determinants with the l1 gauge removed.
l=s.symbols('l1:7');P=[s.Integer(1)]
for _ in range(6):P.append(s.expand(sum(s.diff(P[-1],l[j])*l[j+1] for j in range(5))-l[0]*P[-1]))
H=s.Matrix(4,4,lambda i,j:P[i+j].subs(l[0],0))
assert s.expand(H.det()-W.subs({q:l[1],r:l[2],t:l[3],u:l[4],v:l[5]}))==0
# Certificate cover and exact positive endpoint checks, not floating point comparisons.
rep=json.loads((B/'source_cert_results.json').read_text());rows=json.loads((B/'source_cert_rows.json').read_text())
assert rep['finite_pass'] and rep['outer_pass'] and not rep['failed_cells']
assert len(rows)==2048
assert F(rows[0][0])==F(31,10) and F(rows[-1][1])==8
for a,b in zip(rows,rows[1:]):assert F(a[1])==F(b[0])
threshold=[F(13,20),F(35),F(54),F(120),F(38),F(862)]
S=1<<144
for row in rows:
 assert F(row[0])<F(row[1])
 for z,c in zip(row[2:],threshold):assert F(int(z),S)>c
for z in rep['outer_positive_margins'].values():assert F(z)>0
# Pair block determinants for equispaced points.
a,b,c=s.symbols('a b c')
G=s.Matrix([[1,a,b,c],[a,1,a,b],[b,a,1,a],[c,b,a,1]])
Eblock=s.Matrix([[1+c,a+b],[a+b,1+a]])
Oblock=s.Matrix([[1-c,a-b],[a-b,1-a]])
assert s.expand(G.det()-Eblock.det()*Oblock.det())==0
out={'status':'PASS','W4_normalized_lower':'143/216','full_interval_cover_cells':len(rows),'no_failed_cells':True,'finite_exact_margin_thresholds':list(map(str,threshold)),'outer_positive':True,'prior_three_point_check':'separately rerun; not a dependency of this four-point certificate','scope':'symbolic identities and complete rational interval scalar certificate, not Lean or independent analytic review'}
(B/'final_algebra_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```

## 15. Ausgeführte Endchecks und SHA-256-Quittungen

```json
{
  "status": "PASS",
  "W4_normalized_lower": "143/216",
  "full_interval_cover_cells": 2048,
  "no_failed_cells": true,
  "finite_exact_margin_thresholds": [
    "13/20",
    "35",
    "54",
    "120",
    "38",
    "862"
  ],
  "outer_positive": true,
  "prior_three_point_check": "separately rerun; not a dependency of this four-point certificate",
  "scope": "symbolic identities and complete rational interval scalar certificate, not Lean or independent analytic review"
}
```

```json
{
  "python": "3.13.5",
  "sympy": "1.14.0",
  "files": {
    "registration.json": "3c319d492aa335ea4930d6ba14ed9269236817b0132bf90070cc1c0cff46efe6",
    "registration_w4.json": "b69b07e1aeb28ff0dd693120c8dd0c3aa712d3f7b9f5b874861dee0ba5b79354",
    "build_tail.py": "81843872144a81a2b7382c2b652bbb5eb1ebab89c25dd65200a157f1e0630dd4",
    "build_source_polys.py": "9247c76969d3798f9d6a110a822dd6f2e81adf3be428491ce6b23f950bd732ff",
    "cert_source_final.py": "0f978ed53f2f6fd4c5ac98a3949222b3e9efff308dcf0053dda90f08d8b04435",
    "check_final_algebra.py": "e73380460f718cf968f6caba631d60ff608a189ec041f800f9d3d3978ce2f5d4",
    "tail_bounds.json": "f71b34790b96f67c4cf5a5253bb006f740e410ccd3b491e54e3d2db1eef8e3a9",
    "source_polys.json": "307db761dff577bb9ae33b6b8e9667c568c70311d2339104225244248a656b70",
    "source_cert_results.json": "cb85d6b649ee7de18aaadf25ade6440a3798545bf4133a6120b2de0c65c4b7f4",
    "source_cert_rows.json": "7adc182292cf7f09b0b40bb4b2254fa99c30f2a4aeac0c4257a9d2c04c47b5e1",
    "final_algebra_checks.json": "e3ac88002d2b79cecc300429b037c709904ba8a158866af1781452d24aee5460"
  },
  "prior_artifacts": {
    "/mnt/data/theta_hb_three_point/FULL_THETA_THREE_POINT_CLOSURE_2026-09-17.md": "ab1a2fa31d323279712dfd3d1500ddf764af880f4f27e9f4014d804bba87c72d",
    "/mnt/data/theta_hb_next_step/NEXT_STEP_FULL_THETA_GRAM_2026-09-17.md": "10a98284ea1894d4aefc7699878e04f4fe44709dc64ec7c0ca406e646714f116",
    "/mnt/data/theta_hb_audit/THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md": "e22e7f92b55b301cfc38f17d1e8ace04dde56608848c7f43e18372e38cb15990"
  }
}
```

Die große Zellentabelle wird beim Ausführen der Programme vollständig neu erzeugt. Der hier dokumentierte Hash bindet den ausgeführten Lauf, ersetzt aber weder die mathematische Herleitung des Checkers noch dessen Nachrechnung. Eine veränderte Laufzeit verändert den Hash der Ergebnis-Zusammenfassung, nicht die mathematischen Zellen oder die symbolischen Identitäten.
