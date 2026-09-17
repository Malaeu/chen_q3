# STATUS: TRY_FOLDED_FULL_MIXTURE_WITH_TRANSLATION_GUARD
```yaml
OPERATIVE_CLASS: TRY_FOLDED_FULL_MIXTURE_WITH_TRANSLATION_GUARD
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-17
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: PARTIAL_ANALYTIC_RESULT_WITH_EXECUTED_RATIONAL_AND_SYMBOLIC_CHECKS
INDEPENDENT_ANALYTIC_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
PROGRESS_CLASS: PROOF_PROGRESS
GLOBAL_SIGN_CLOSED: false
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
NEW_RESULTS:
  - FULL_MIXTURE_MOMENT_RECURSION_WITH_CONSTANT_36
  - HB_LOWER_ENVELOPE_ON_ALL_sigma_GT_0_AND_tau_SQUARED_LE_20
  - FIXED_ANCHOR_VARIANCE_TRANSLATION_DECAY_AND_TRACE_BOUND
  - RAW_WHOLE_LINE_THETA_DIAGONAL_INTEGRAL_DIVERGENCE
  - ABSOLUTELY_CONVERGENT_FOLDED_DOUBLE_SOURCE_SERIES
NOT_CLOSED:
  - FULL_MIXTURE_SIGN_AT_ALL_FREQUENCIES
  - GLOBAL_HB_SIGN
  - ORIGINAL_SUPPORT
  - ORIGINAL_V_SIGN
SCOPED_REJECTIONS:
  - statement: A_FIXED_FINITE_ANCHOR_VARIANCE_HAS_A_UNIFORM_POSITIVE_FORM_FLOOR
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    evidence: SECTION_3_COMMON_TRANSLATION
  - statement: RAW_WHOLE_LINE_THETA_DIAGONALS_FORM_A_FINITE_POSITIVE_RESERVE
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: INCOMPATIBILITY
    evidence: SECTION_4_POSITIVE_DIAGONAL_DIVERGENCE
  - statement: THE_MOMENT_MAJORANTS_ALONE_FORCE_ALL_FREQUENCY_POSITIVITY
    KILL_SCOPE: THEOREM_SHAPE
    FAILURE_TYPE: COUNTEREXAMPLE
    evidence: SECTION_7_EXACT_NEGATIVE_UPPER_BOUND
FULL_MIXTURE_REFUTED: false
ORIGINAL_V_NEGATIVE_WITNESS: false
SOURCE_DERIVATIVE_CERTIFICATE_RERUN: true
REPOSITORY_CHANGED: false
CODEX_DISPATCHED: false
PRODUCTION_STATE_CHANGED: false
RH_CLAIM: false
```

## 0. Was der Versuch tatsächlich erreicht

**Die globale Kompensation der vollständigen Mischung ist hier nicht bewiesen.** Der Angriff liefert eine neue, ausdrückliche untere Schranke für die vollständige Mischung auf einem Frequenzband. Gleichzeitig entscheidet er zwei konkrete Hindernisse für vermeintlich allgemeine Kompensationsbeweise.

Das neue positive Resultat lautet, mit unverändertem `F(p)=xi(1/2+p)`:

\[
\boxed{
\mathscr H(\sigma+i\tau)
\ge 4F(\sigma)F'(\sigma)
\left[1-s+\frac{s^2}{6}-\frac{s^3}{18}\right]
\ge \frac{121}{6561}\,4F(\sigma)F'(\sigma)>0,
\quad s=\frac{\tau^2}{18},\quad \sigma>0,\quad \tau^2\le20.
}
\tag{0.1}
\]

Es ist kein Test einzelner Punkte oder kleiner Matrizen. Es gilt für jede positive Verschiebung sigma und das gesamte angegebene Frequenzband. Die globale Hochfrequenzfrage wird damit **nicht** gelöst. Die neue Abschätzung wird insbesondere nicht als Beweis dafür ausgegeben, dass negative einzelne Wigner-Beiträge bei allen Frequenzen durch die Mischung bezahlt werden.

Die Ankeranalyse korrigiert die Bewertung der vorherigen Restdarstellung: Ihre Matrixvarianz ist ein positiver, räumlich lokalisierter, sogar spurklassiger Korrekturterm. Sie kann lokale durch Anker verursachte Defekte ausgleichen. Sie kann aber nicht als gleichmäßige positive Reserve für alle übersetzten Testpakete dienen. Der stationäre Vorzeicheninhalt bleibt in der vollständigen Mischung.

Die rohe Theta-Expansion auf der ganzen Integrationsgeraden besitzt ferner bereits bei w=0 eine divergierende positive Diagonalsumme. Eine Zerlegung in separat integrierte positive Diagonalen plus endliche Korrekturen wäre deshalb unzulässig. Eine exakte Faltung mittels Geradheit repariert die absolute Konvergenz; sie bezahlt nicht automatisch das Fourier-Vorzeichen.

Alle neuen analytischen Aussagen sind **PAPER**, nicht Lean-zertifiziert. Die vorausgesetzten rationalen Quellenchecks sowie neue algebraische und rationale Gegenchecks wurden in dieser Runde tatsächlich ausgeführt.

## 1. Quellenbindung und unveränderte Objekte

**[ABSTRACT][PAPER: Definitionen und übernommene Quellenregularität]**

Grundlage ist das vollständige lokale Dokument
`FULL_THETA_FOUR_POINT_AND_GLOBAL_BOUNDARY_2026-09-17.md`,
SHA-256 `fd45b05b1f0135881961fb4d9c6c92c61060dd7d764398af5cbae5453299cc75`.
Es wurde für Definitionen, die gemeinsame Restidentität und die Quellenabschätzung gelesen. Seine Vierpunkt- und bedingten SUPPORT/V-Beweise werden hier nicht als erneut unabhängig abgenommen bezeichnet.

Die ursprünglichen Definitionen wurden außerdem in S1, Abschnitte 1–2, am angegebenen GitHub-Commit gelesen. Der Quellenbericht selbst trägt den Status `PAPER_AUDIT_PENDING_INDEPENDENT_CHECK`; dieser historische Status wird nicht aufgewertet.

Unsere Fourier-Konvention ist

\[
\widehat g(\omega)=\int_{\mathbb R}g(w)e^{-i\omega w}\,dw.
\]

Setze

\[
\phi_n(t)=
(4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2})e^{-\pi n^2e^{2t}},
\quad \Phi(t)=\sum_{n\ge1}\phi_n(t).
\]

Die vollständige Quelle Phi ist positiv, gerade, glatt und einschließlich jeder festen Ableitung schneller als jede Exponentialfunktion fallend. Geradheit folgt aus der Jacobi-Identität. **Ein einzelnes phi_n ist nicht gerade und ist auf der ganzen Geraden nicht positiv.** Für t>=0 ist dagegen jedes phi_n(t)>0.

\[
F(p)=\xi(1/2+p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt,
\qquad
\mathscr H(p)=4\Re(F'(p)\overline{F(p)}).
\]

Mit \(\omega_\sigma(v)=v\sinh(2\sigma v)\ge0\):

\[
K_\sigma(w)=\int_{\mathbb R}\omega_\sigma(v)
                  \Phi(v+w)\Phi(v-w)\,dv,
\quad k_\sigma(w)=K_\sigma(w)/K_\sigma(0).
\]

Es gilt exakt

\[
\mathscr H(\sigma+i\tau)=8\widehat K_\sigma(2\tau).
\tag{1.1}
\]

Die ursprüngliche Form ist weiterhin

\[
f=\Phi/\|\Phi\|_2,
\qquad
V(x,y)=\int_0^\infty(x+y+2t)f(x+t)f(y+t)\,dt.
\]

Eine positive Aussage über den Faltungskern K wird nicht ohne den vollständigen Übergang als Aussage über V bezeichnet.

### 1.1 Ausgeführte Quellenkontrolle

Aus dem Grundlagenbericht wurden seine vier Programme unverändert extrahiert und ausgeführt:

```
python build_tail.py
python build_source_polys.py
python cert_source_final.py
python check_final_algebra.py
```

Ergebnis: vollständige rationale Abdeckung mit 2048 Zellen, keine fehlgeschlagene Zelle, äußerer analytischer Rest positiv. Insbesondere wird die hier benötigte Schranke bestätigt:

\[
q(t):=-(\log\Phi(t))''>18\quad(t\in\mathbb R).
\tag{1.2}
\]

Der Name q bezeichnet hier nur die logarithmische Krümmung, nicht den anderswo q genannten normierten Quellenkern der SUPPORT-Gleichung.

Die Prüfausgabe des übernommenen letzten Programms enthält eine historische Textzeile über einen früher separat geprüften Dreipunktcheck. **In dieser Runde wurden nur die hier aufgelisteten Programme ausgeführt; diese übernommene Textzeile ist keine neue Ausführungsquittung.**

Der rationale Checker überprüft seine endliche Domänenabdeckung und die algebraischen Schranken. Die analytische Ableitung der vollständigen Theta-Restmajoranten gehört zum gelesenen Grundlagenbeweis; keine unabhängige Begutachtung dieses Textes wird behauptet.

## 2. Gemeinsamer Schurrest: die Identität ist korrekt, aber erzeugt kein eigenes Vorzeichen

**[ABSTRACT][PAPER]**

Schreibe wie bisher

\[
C_v(w)=\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}=e^{-R_v(w)},
\quad
k_\sigma(w)=\mathbb E_{\mu_\sigma} C_v(w),
\]

\[
d\mu_\sigma(v)=\frac{\omega_\sigma(v)\Phi(v)^2}{K_\sigma(0)}\,dv.
\]

Aus (1.2) folgt

\[
R_v''(w)=q(v+w)+q(v-w)>36,
\quad R_v(0)=R_v'(0)=0,
\quad 0<C_v(w)\le e^{-18w^2}.
\tag{2.1}
\]

Für den folgenden Angriff dürfen wir konkrete Anker wählen, weil im vorherigen Ergebnis keine besonderen Anker festgeschrieben waren. Fixiere einmalig

\[
(a_1,a_2,a_3)=(-1,0,1).
\]

Definiere

\[
A_v=[C_v(a_i-a_j)]_{i,j=1}^3,\quad
b_v(x)=(C_v(a_i-x))_{i=1}^3,
\]
\[
A=\mathbb E A_v,\quad b(x)=\mathbb E b_v(x),
\quad z_v(x)=A_v^{-1}b_v(x),\quad z(x)=A^{-1}b(x).
\]

Die außerdiagonalen Zeilensummen sind höchstens 2e^-18. Da e^18>19,

\[
A_v\succeq\frac{17}{19}I,\quad A\succeq\frac{17}{19}I,
\quad \|A_v^{-1}\|,\|A^{-1}\|\le\frac{19}{17}.
\tag{2.2}
\]

Hier genügt der elementare Zeilensummenbeweis: gemischte Produkte werden durch
`2|u_i u_j| <= |u_i|^2+|u_j|^2` kontrolliert. Ein all-dimensionaler Positivitätssatz wird nicht benutzt. Für diese Anker wird auch nicht der vorherige schwierige Vierpunktbeweis als Voraussetzung benötigt.

Setze

\[
S(x,y)=\mathbb E[b_v(x)^*A_v^{-1}b_v(y)],
\quad B(x,y)=b(x)^*A^{-1}b(y),
\]
\[
\mathcal M(x,y)=\mathbb E[(z_v(x)-z(x))^*A_v(z_v(y)-z(y))].
\]

Durch Ausmultiplizieren und \(\mathbb E A_vz_v(x)=b(x)\) folgt

\[
\boxed{\mathcal M=S-B\succeq0.}
\tag{2.3}
\]

Somit ist die vorige gemeinsame Restidentität genau

\[
\boxed{
\mathbb E r_v+\mathcal M=(k_\sigma-S)+(S-B)=k_\sigma-B.
}
\tag{2.4}
\]

Das ist keine Entwertung der Identität: sie legt die Auslöschung exakt offen. Es wäre aber falsch, ihre positive Varianz als zusätzliches, unabhängiges Vorzeichenbudget zu behandeln. Derselbe S-Term steht mit umgekehrtem Vorzeichen im mittleren Profilrest.

Ein exakter rational-komplexer Gegencheck mit nichtkommutierenden Ankermatrizen wurde ausgeführt. Die allgemeine Identität wird durch die vorstehende Rechnung bewiesen, nicht durch das einzelne Kontrollbeispiel.

## 3. Ein ganzer Testklassen-Angriff: feste Anker verschwinden bei gemeinsamer Translation

**[ABSTRACT][PAPER]**

Seien x_1,...,x_N und c_1,...,c_N beliebig, endlich. Verschiebe die gesamte Konfiguration um T, ohne die Anker zu bewegen. Die ungekürzte Quellenenergie

\[
Q_\sigma(c,x+T)=\sum_{i,j}\bar c_i k_\sigma(x_i-x_j)c_j
=Q_\sigma(c,x)
\tag{3.1}
\]

ändert sich nicht. Das ist die Translationsinvarianz des unveränderten Kernes.

Setze

\[
d(T)=\min_{i,j}|x_i+T-a_j|\longrightarrow\infty.
\]

Mit (2.1)–(2.3) folgt dagegen

\[
\boxed{
0\le\sum_{i,j}\bar c_i\mathcal M(x_i+T,x_j+T)c_j
\le\frac{57}{17}\|c\|_1^2e^{-36d(T)^2}\longrightarrow0.
}
\tag{3.2}
\]

Denn \(S_v=\sum_i c_i b_v(x_i+T)\) erfüllt
\(\|S_v\|^2\le3\|c\|_1^2e^{-36d(T)^2}\).
Die Varianzform ist höchstens \(\mathbb E S_v^*A_v^{-1}S_v\).
Dies beweist (3.2). Auch die B- und S-Formen gehen mit derselben Schranke gegen null.

**Folgerung:** Es gibt keinen positiven, für alle Positionen gültigen Varianzboden
`M[c,x] >= delta * ||c||_2^2`, delta>0. Ein einzelnes nichttriviales Paket, das beliebig weit verschoben wird, widerlegt dies. Ein negatives hypothetisches stationäres Quellenpaket würde bei dieser Verschiebung negativ bleiben. Ein solches Paket wird hier nicht behauptet oder konstruiert.

Die Aussage betrifft die gewählten festen Anker und jede andere feste endliche Ankerkonfiguration, für die die entsprechenden Inversen beschränkt sind. Sie verbietet keine sorgfältige adaptive Zerlegung. Eine mit jedem Paket neu gewählte Ankerfamilie benötigt aber eine neue, eigenständig bewiesene globale Quellenungleichung; das Vorzeichen wird nicht von (3.2) geliefert.

### 3.1 Stärkere Operatorfassung

Die positive Varianz ist sogar ein spurklassiger Kern auf L2(R). Tatsächlich:

\[
0\le\mathcal M(x,x)\le\frac{19}{17}\sum_{j=1}^3e^{-36(x-a_j)^2},
\]
\[
\boxed{\operatorname{Tr}\mathcal M\le\frac{19\sqrt\pi}{34}.}
\tag{3.3}
\]

Zum Nachweis definiert man den Feature-Operator mit
`h_v(x)=A_v^(1/2)(z_v(x)-z(x))`.
Seine Hilbert-Schmidt-Norm zum Quadrat ist das Integral der linken Diagonale; (3.3) macht es endlich. Der Varianzoperator ist sein adjungiertes Quadrat und daher positiv, spurklassig und kompakt.

Ein elementarer allgemeiner Satz erläutert die Grenze: Ist T ein beschränkter translationsinvarianter Operator auf L2(R) und C kompakt selbstadjungiert, dann

\[
T+C\succeq0\ \Longrightarrow\ T\succeq0.
\tag{3.4}
\]

Beweis: Für festes u gehen seine Translationen u_R schwach gegen null. Das folgt erst für kompakt getragene Testfunktionen und dann durch L2-Dichte. Kompaktheit gibt `<u_R,Cu_R> -> 0`, während `<u_R,Tu_R>=<u,Tu>`. Der Grenzwert der nichtnegativen Formen beweist (3.4). Für C>=0 gilt auch die triviale Umkehrung.

**Nicht behauptet wird, dass die Schurzerlegung überhaupt keinen Beweis liefern könnte.** Sie kann einen wirklichen Quellenvergleich organisieren. Widerlegt ist die Behandlung ihrer festen positiven Ankerkorrektur als globaler Ersatz für das stationäre Vorzeichen.

## 4. Die rohe positive Theta-Diagonale ist unendlich

**[ABSTRACT][PAPER]**

Ein weiterer konkreter Ansatz wäre, Phi^2 auf der ganzen v-Geraden in Theta-Diagonalen und gemischte Beiträge zu zerlegen und jede Diagonale separat zu integrieren. Schon bei w=0 ist dieser Schritt nicht absolut zulässig.

Mit phi=phi_1 gilt die exakte Skalierungsidentität

\[
\boxed{\phi_n(v)=n^{-1/2}\phi(v+\log n).}
\tag{4.1}
\]

Sie wurde zusätzlich symbolisch kontrolliert. Definiere die nichtnegativen Diagonalintegrale

\[
D_n(\sigma)=\int_{\mathbb R}v\sinh(2\sigma v)\phi_n(v)^2\,dv.
\]

Jedes einzelne Integral existiert beispielsweise für 0<sigma<1/2, dem noch relevanten inneren Bereich; für zu große sigma können bereits einzelne Integrale divergieren, was den folgenden Befund nur verstärkt. Die untere Schranke unten verwendet in jedem Fall nur ein kompaktes Teilintervall.

Setze v=u-log n und beschränke auf 0<=u<=1. Phi_1 ist auf diesem Intervall strikt positiv. Für hinreichend große n, abhängig vom festen sigma>0, gilt

\[
(\log n-u)\sinh(2\sigma(\log n-u))
\ge\frac{e^{-2\sigma}}8(\log n)n^{2\sigma}.
\]

Somit

\[
D_n(\sigma)\ge
\underbrace{\frac{e^{-2\sigma}}8\int_0^1\phi(u)^2\,du}_{c_\sigma>0}
 n^{2\sigma-1}\log n.
\]

Die rechte Reihe divergiert für jedes sigma>0. Deshalb

\[
\boxed{\sum_{n\ge1}D_n(\sigma)=+\infty,
\qquad K_\sigma(0)<\infty.}
\tag{4.2}
\]

Im noch offenen Bereich 0<sigma<1/2 hat jedes D_n einen endlichen Wert und allein ihre Summe divergiert. Genau dort ist also bereits eine Trennung in eine endliche positive Diagonalreserve und separat endliche gemischte Korrekturen unmöglich.

Dies widerspricht nicht der pointweisen Theta-Reihe. Bei jedem festen v konvergiert sie absolut. Auf der negativen v-Halbachse enthalten ihre einzelnen Summanden aber beide Vorzeichen. Die modulare Auslöschung der vollständigen Quelle verhindert den Austausch von unbeschränktem Integral und separat positiver Diagonalsumme.

**Genaue Grenze:** Zurückgewiesen wird nur diese rohe Ganzgeraden-Zerlegung. Weder wird K negativ, noch wird eine andere, vor der Integration kompensierte Quadratdarstellung ausgeschlossen. Die rohen Summen `sum phi_n(t)` auf ganz R sind außerdem nicht dieselben endlichen approximierenden Quellen wie `sum phi_n(|t|)` aus dem früheren cosh-Ansatz.

## 5. Reparatur der Konvergenz: vollständige modulare Faltung vor der Expansion

**[ABSTRACT][PAPER]**

Geradheit von Phi erlaubt für jeden reellen w die exakte Darstellung

\[
\boxed{
K_\sigma(w)=2\int_0^\infty v\sinh(2\sigma v)
\Phi(v+|w|)\Phi(|v-|w||)\,dv.
}
\tag{5.1}
\]

Jetzt sind beide Argumente nichtnegativ. Dort ist jeder Theta-Summand positiv. Definiere

\[
L_{nm,\sigma}(w)=2\int_0^\infty v\sinh(2\sigma v)
\phi_n(v+|w|)\phi_m(|v-|w||)\,dv\ge0.
\]

Dann gilt nicht nur pointweise, sondern auch in L1:

\[
\boxed{K_\sigma=\sum_{n,m\ge1}L_{nm,\sigma},
\qquad\sum_{n,m}\|L_{nm,\sigma}\|_1=\|K_\sigma\|_1<\infty.}
\tag{5.2}
\]

Tonelli beweist beides, weil die Summanden jetzt nichtnegativ sind und der vollständige Kern integrabel ist. Folglich darf die Fourier-Transformation mit dieser **gefalteten** Reihe vertauscht werden:

\[
\widehat K_\sigma(\omega)=\sum_{n,m}\widehat L_{nm,\sigma}(\omega),
\quad\sum_{n,m}|\widehat L_{nm,\sigma}(\omega)|\le\|K_\sigma\|_1.
\tag{5.3}
\]

Das ist eine absolute Konvergenzreparatur, kein Fourier-Vorzeichensatz. Positive Werte von L_nm(w) bedeuten nicht positive Fourier-Werte.

### 5.1 Ein gültiges, aber begrenztes Fehlerbudget

Setze `K_sigma,N=sum_(n,m<=N) L_nm,sigma`, `Z_sigma=int K_sigma`, `Z_sigma,N=int K_sigma,N`. Dann

\[
0\le K_\sigma-K_{\sigma,N},\qquad
|\widehat K_\sigma(\omega)-\widehat K_{\sigma,N}(\omega)|
\le Z_\sigma-Z_{\sigma,N}.
\tag{5.4}
\]

Damit sind die echten einseitigen Hüllen

\[
\widehat K_{\sigma,N}(\omega)-(Z_\sigma-Z_{\sigma,N})
\le\widehat K_\sigma(\omega)
\le\widehat K_{\sigma,N}(\omega)+(Z_\sigma-Z_{\sigma,N}).
\]

Das Restbudget ist eine positive Quellenintegralgröße und hängt nicht vom erhofften Vorzeichen ab. Für jedes feste N ist es aber frequenzunabhängig, während der zu zertifizierende Fourier-Wert gegen null geht. Es ist deshalb **kein** vorgelegtes Zertifikat für alle Höhen. Eine bessere, gekoppelte und frequenzabhängige Restbehandlung bleibt erforderlich.

## 6. Eine neue Untergrenze der vollständigen Mischung, ohne Dimensionsbeschränkung

**[ABSTRACT][PAPER]**

Die folgende Rechnung schätzt tatsächlich den vollständigen K und nicht eine seiner endlichen Gram-Matrizen. Sie benötigt von der stärkeren Quellenkontrolle nur q>18.

Setze

\[
Z_\sigma=\int_{\mathbb R}K_\sigma(w)\,dw>0,
\quad p_\sigma(w)=K_\sigma(w)/Z_\sigma,
\quad m_{2r}=\int w^{2r}p_\sigma(w)\,dw.
\]

**Achtung auf die Normierung:** p_sigma ist eine Wahrscheinlichkeitsdichte in w; k_sigma=K_sigma/K_sigma(0) bleibt der normierte Gram-Kern. Diese beiden Normierungen werden nicht vertauscht.

Aus R_v''>36 und R_v'(0)=0 folgt
`w R_v'(w) >= 36 w^2`.
Partielle Integration gibt für r>=1

\[
(2r-1)\int w^{2r-2}C_v(w)\,dw
=\int w^{2r-1}R_v'(w)C_v(w)\,dw
\ge36\int w^{2r}C_v(w)\,dw.
\]

Alle Randterme verschwinden. Die Quellenregularität kontrolliert auch die Ableitungsintegrale. Multiplikation mit dem unveränderten positiven Gewicht `omega_sigma(v)Phi(v)^2` und Integration in v liefern

\[
\boxed{m_{2r}\le\frac{2r-1}{36}m_{2r-2}\quad(r\ge1).}
\tag{6.1}
\]

Dies ist eine Familie voller Mischungs-Momentabschätzungen. Es wird nicht behauptet, dass p_sigma selbst eine bestimmte logarithmische Krümmung besitzt; Mischungen würden diesen Schluss nicht automatisch erlauben.

Insbesondere

\[
m_2\le1/36,\qquad m_6\le(5/36)m_4,\qquad m_4\ge m_2^2.
\tag{6.2}
\]

Die letzte Ungleichung ist die Nichtnegativität der Varianz von w^2 unter p_sigma.

Für alle reellen u gilt

\[
\cos u\ge1-\frac{u^2}{2}+\frac{u^4}{24}-\frac{u^6}{720}.
\tag{6.3}
\]

Eine globale Restbegründung: Beginne mit 1-cos u>=0. Wiederholtes zweimaliges Integrieren erhält auf u>=0 abwechselnd die obere und untere Taylorhülle; nach drei Schritten entsteht (6.3). Geradheit deckt u<0 ab. Es wird keine lokale Alternierungsannahme für große u benutzt.

Damit für tau^2<=20:

\[
\begin{aligned}
\frac{\widehat K_\sigma(2\tau)}{Z_\sigma}
&\ge1-2\tau^2m_2+\frac23\tau^4m_4-\frac4{45}\tau^6m_6\\
&\ge1-2\tau^2m_2+
\frac23\tau^4\left(1-\frac{\tau^2}{54}\right)m_2^2.
\end{aligned}
\tag{6.4}
\]

Setze s=tau^2/18<=10/9 und y=2tau^2 m2, also 0<=y<=s. Der letzte Ausdruck ist

\[
Q_s(y)=1-y+\frac{1-s/3}{6}y^2.
\]

Auf diesem Bereich gilt `dQ_s/dy <= -1+10/27<0`, sodass

\[
Q_s(y)\ge Q_s(s)=P(s):=1-s+s^2/6-s^3/18.
\]

Weiter

\[
P'(s)=-\frac{(s-1)^2+5}{6}<0,
\qquad P(10/9)=\frac{121}{6561}>0.
\]

Mit (1.1) und `8Z_sigma=H(sigma)=4F(sigma)F'(sigma)` ist (0.1) bewiesen. F(sigma) und F'(sigma) sind für sigma>0 unmittelbar aus dem positiven cosh-Quellenintegral strikt positiv.

### 6.1 Was daran dimensionsunabhängig ist

Sei T_K die Faltung mit K_sigma. Für jede L2-Funktion u, deren Fourier-Transformierte im Band `[-2sqrt(20),2sqrt(20)]` getragen ist, gilt

\[
\boxed{
\langle u,T_Ku\rangle
\ge\frac{121}{6561}Z_\sigma\|u\|_2^2.
}
\tag{6.5}
\]

Dies folgt mit den festgehaltenen Fourier-Konstanten aus Plancherel. Der zulässige Raum ist unendlichdimensional. Er ist aber ein echter Teilraum; (6.5) wird nicht als Vorzeichen auf beliebigen kompakten Tests oder beliebigen endlichen Punktpaketen bezeichnet.

Eine endliche Exponentialsumme in der Fourier-Variablen hat im Allgemeinen keinen solchen Bandträger. Deshalb gibt (6.5) nicht automatisch ein neues all-dimensionales Gram-Zertifikat und keinen V-Beweis.

## 7. Exakter Gegencheck: auch alle Momentmajoranten zusammen bezahlen nicht alle Frequenzen

**[ABSTRACT][PAPER — Gegenbeispiel einer stärkeren generischen Behauptung, nicht Theta]**

Der glatte gerade Modellkern

\[
j(w)=\exp\left[-18w^2-\frac{18^2}{8}w^4\right]
\]

hat `(-log j)''>=36`. Seine normierte w-Dichte erfüllt daher **alle** Momentmajoranten (6.1). Trotzdem ist j nicht in allen Dimensionen positiv definit.

An den vier Positionen `0,h,2h,3h`, h=1/(4sqrt(18)), setze

\[
A=e^{-129/2048},\quad B=e^{-33/128},\quad C=e^{-1233/2048}.
\]

Der ungerade Zweierblock hat Determinante

\[
D=(1-C)(1-A)-(A-B)^2.
\]

Alternierende rationale Taylor-Summen der Grade 39 und 40 für exp(-x), 0<=x<=1, geben ausgeführt einen exakten oberen Einschluss

\[
\boxed{D\le U<-1/100000<0.}
\tag{7.1}
\]

Orientierungswert, nicht Beweisinput: U ist ungefähr -0.0000155512. Der genaue rationale U steht in `checks/mixture_checks.json` und wird vom mitgelieferten Programm erzeugt.

Mit r=A-B und d=1-C>0 ist sogar die konkrete Richtung

\[
c=(r,-d,d,-r)
\]

negativ:

\[
c^*[j(x_i-x_j)]c=2dD<0.
\]

Dieses Modell zeigt genau, warum (6.1) trotz seines unendlichen Momentquantors kein globaler Fourier-Vorzeichenbeweis ist. Es erfüllt nicht alle zusätzlichen Theta-Eigenschaften des Grundlagenberichts. Weder dessen Vierpunktbeweis noch die ursprüngliche V wird durch (7.1) widerlegt.

## 8. Eine weitere vollständige Darstellung und ihre Grenze

**[ABSTRACT][PAPER]**

Definiere die gekippte vollständige Quelle `u_sigma(t)=e^(sigma t)Phi(t)` und ihre Autokorrelation

\[
A_\sigma(w)=\int_{\mathbb R}u_\sigma(v+w)u_\sigma(v-w)\,dv
=\int\cosh(2\sigma v)\Phi(v+w)\Phi(v-w)\,dv.
\]

Dann

\[
\boxed{\partial_\sigma A_\sigma=2K_\sigma,
\qquad \widehat A_\sigma(2\tau)=\tfrac12|F(\sigma+i\tau)|^2.}
\tag{8.1}
\]

Für jedes sigma ist A_sigma ein positiver Autokorrelationskern. Die verlangte Positivität von K_sigma ist aber die **Monotonie dieser Familie in der Ordnung quadratischer Formen**, nicht ihre punktweise vorhandene Positivität. Positive Operatoren können eine negative Ableitung haben. Der Übergang wird deshalb nicht als geliefert betrachtet.

Eine Reihenentwicklung nach sigma führt auf die vollständigen assoziierten Kerne

\[
J_r(w)=\int v^{2r}\Phi(v+w)\Phi(v-w)\,dv,
\quad
K_\sigma(w)=\sum_{r\ge1}\frac{(2\sigma)^{2r-1}}{(2r-1)!}J_r(w).
\tag{8.2}
\]

Die Domination durch die vollständige cosh-/sinh-Quelle rechtfertigt diese Darstellung. Die all-order Vorzeichenprobleme der assoziierten Kerne sind in Csordas, Theorem 3.7, bereits als generalisierte Laguerre-Ungleichungen identifiziert. Dies ist ein **Literaturabgleich**, kein in dieser Runde gefundener Lieferant. Die positive Existenz von J_r(w) als Funktion beweist nicht ihr Fourier-Vorzeichen; die Zeichenbedingung darf nicht in die Reihenentwicklung hineingelesen werden.

## 9. Was offen bleibt und welcher nächste Angriff überhaupt zulässig ist

Der bekannte äußere Bereich sigma>1/2 wird von Lagarias, Einleitung (1.4), geliefert; Stetigkeit bezahlt die Grenze sigma=1/2. Die neue eigenständige Quellenabschätzung deckt tau^2<=20 ab. Offen bleibt für diesen direkten Nachweis

\[
\boxed{0<\sigma<1/2,\qquad |\tau|>\sqrt{20}.}
\tag{9.1}
\]

Diese Angabe behauptet nicht, dass außerhalb unseres Bandes keine weiteren klassischen Teilresultate existieren. Sie beschreibt nur den in dieser Rechnung nicht bezahlten Bereich. Ein bloßer Verweis auf bekannte Kriterien liefert dort keine Quelle.

Die weiterhin verlangte globale Ungleichung ist unverändert

\[
\int_{\mathbb R}\omega_\sigma(v)
\left[\int_{\mathbb R}\Phi(v+w)\Phi(v-w)\cos(2\tau w)\,dw\right]dv\ge0.
\tag{9.2}
\]

Der Bericht behauptet **nicht**, (9.2) durch Umbenennung kleiner gemacht zu haben. Die echte Fortschrittsbilanz ist: eine positive Teilgebiets-Unterhülle ist hinzugekommen; zwei unzulängliche Kompensationsansätze sind genau begrenzt; die absolute Quellenrepräsentation ist repariert.

### Zwei Re-Repräsentationen des weiterhin offenen Teils

**R1 — ausgewählt: modular gefaltete, vollständig gekoppelte Fourier-Reihe (5.3).** Sie ist absolut konvergent und erhält die richtige Quelle. Ein neuer Vorzeichenbeweis muss die Fourier-Vorzeichen der Summanden gemeinsam kontrollieren, mit einem frequenzabhängigen, vorzeichenbewahrenden Rest. Maximal entscheidende Kraft für den unveränderten Verbraucher; algebraische Vorbereitung niedrig, globale analytische Kosten hoch und derzeit nicht zuverlässig bezifferbar. Keine weitere profilweise Dimensionsleiter.

**R2 — vollständige Autokorrelationsfamilie (8.1).** Ein quellenspezifischer Beweis ihrer Ordnungsmonotonie würde dasselbe Ziel liefern. Maximal entscheidende Kraft; formale Identität niedrig, Beweiskosten für die zusätzliche Monotonie hoch/unbekannt. Ihre bloße Positivität darf nicht als Monotonie eingesetzt werden.

Beide sind Kandidatendarstellungen, keine behaupteten neuen mathematischen Lieferanten. Die ausgewählte nächste Arbeit wäre eine echte gekoppelte Quellenabschätzung auf (9.1), nicht die Anlage eines weiteren Katalognamens für (9.2).

### Diskriminator bei nullkompatiblen Ergebnissen

Ein Zertifikat für die ganze Funktion oder ein explizites Spektralteilgebiet muss eine gültige untere Hülle für `hat K_sigma(2tau)` tragen. Eine strikt negative obere Hülle wäre ein negatives Vollquellenzeugnis. Ein Intervall um null bleibt unentscheidend.

Alternativ isoliert ein Fourier-lokalisiertes L2-Paket eine hypothetische negative Spektralstelle. Eine anschließende räumliche Translation macht zugleich jede feste Ankerkorrektur beliebig klein, ohne seine Faltungsenergie zu ändern. Dieses Funktional unterscheidet den stationären Vollquellendefekt von einem nur lokalen Ankerartefakt. Es wurde hier kein negatives Vollquellenpaket gefunden.

## 10. K8A, Quellenepistemik und Abschluss

**DOWNSTREAM_CONSUMER:** voller HB-Zeichensatz für das unveränderte F; anschließend ursprüngliches M/Y/SUPPORT und ursprüngliche V.

**ACTUAL_CONSUMER_REQUIREMENT:** `H(sigma+i tau)>=0` auf allen benötigten sigma,tau; äquivalent zur all-dimensionalen positiven Definitheit von K_sigma.

**ORIGINAL_REQUESTED_OBJECT:** vollständige Quellenkompensation. Sie ist für den gewählten Verbraucher notwendig. **Nicht notwendig** sind ein positiver fester Ankerboden, separat endliche rohe Diagonalen oder profilweise all-order Positivität.

**KNOWN_WEAKER_INTERFACES:** Ein direkter Beweis von (9.2) kann Schur und alle Anker vollständig umgehen. Eine quantitative gekoppelte Fourier-Restidentität, welche (5.3) nach unten kontrolliert, ist ausreichend. (0.1) reicht nur auf seinem expliziten Teilgebiet.

**FAILURE_TYPE / EPISTEMIC_STATUS:** Für die volle Kompensation `NO_DERIVATION / RESEARCH_DEBT`. Keine mathematische Unmöglichkeit dieser Hauptaussage. Für die drei expliziten überstarken Aussagen im Header liegen die genauen Gegenbelege in Abschnitten 3, 4 und 7 vor; ihr `KILL_SCOPE` ist ausschließlich `THEOREM_SHAPE`.

**REOPEN_TRIGGER:** Ein neuer quellengebundener, für alle relevanten Frequenzen kontrollierter Mischungsvergleich oder ein strikt negativer oberer Einschluss des tatsächlichen Gesamtkerns. Weitere positive kleine Matrizen, engere Anker oder bloß genauere absolute Fehlergrenzen ohne neue Frequenzkontrolle sind kein globaler Vorzeichenlieferant.

**NOVELTY_AXIS:** Die hier hergeleiteten quantitativen Translations- und Bandabschätzungen sowie die Konvergenzprüfung. Keine Prioritätsbehauptung. Die Interpretation durch Fourier-Positivität und assoziierte Laguerre-Kerne ist klassisch und wird als solche zitiert.

**Vorregistrierungen:** `registration.json` entstand vor den ausgeführten Gegenchecks. P_FIXED_ANCHOR_TRANSLATION wird durch (3.2) bestätigt; P_UNFOLDED_DIAGONAL durch (4.2); P_SOURCE_BAND durch (0.1). Die globale Behauptung war dort ausdrücklich `UNRESOLVED` und bleibt es. Frühere globale Hoffnungen werden nicht nachträglich als bestätigte Vorhersagen umgeschrieben.

**Strategieeintrag:** `PROOF_PROGRESS` für ein explizites volles Quellen-Teilgebiet; `REPRESENTATION_SHIFT` weg von einem vermeintlichen festen Varianzreservoir, hin zu einer vor der Fourier-Auswertung korrekt gefalteten Gesamtquelle. Kein globales Fortschrittsprozent, kein RH-Export.

**Status der alten Ergebnisse:** Die alte Vierpunktaussage wird durch keinen dieser Gegenchecks widerlegt. Ihr ursprünglicher Status bleibt ein nicht unabhängig abgenommener rechnergestützter Papierbeweis. Die aktuelle Runde wiederholt seine scalar-source Zertifikatsrechnung, nicht automatisch jeden analytischen Schritt des alten Textes.

**Ausführung:** Keine Repository-Schreiboperation, keine Zustandsänderung, kein Lean-Code, kein CodeX-Dispatch. Die neuen Beweise sind lokale Forschungsartefakte. Der vollständige HB-Beweis, SUPPORT und das Vorzeichen von V bleiben offen. Kein negativer V-Zeuge wurde gefunden.

## 11. Referenzen und Reproduktion

**S1.** `Malaeu/chen_q3`, `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Commit `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`, Blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`, Abschnitte 1–2. In dieser Runde über den GitHub-Connector gelesen.

**S2.** Lokales Grundlagenpapier `FULL_THETA_FOUR_POINT_AND_GLOBAL_BOUNDARY_2026-09-17.md`, SHA-256 wie Abschnitt 1. Seine q-Quellabschätzung und die Schur-Identität sind die hier genannten übernommenen Eingänge. Die vier reproduzierbaren Programme befinden sich im Prüfarchiv.

**S3.** Jeffrey C. Lagarias, *On a Positivity Property of the Riemann xi-Function*, Autoren-PDF, Einleitung (1.4)–(1.5), Originalseite visuell geprüft. `https://websites.umich.edu/~lagarias/doc/positivity.pdf`.

**S4.** George Csordas, *Fourier transforms of positive definite kernels and the Riemann xi-function*, arXiv:1309.0055v2, Theorem 3.7 und (3.14), gedruckte Seite 8 visuell geprüft. `https://arxiv.org/pdf/1309.0055`.

**S5.** Aktuelles Projektprotokoll `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, Branch `rh_clean`, Blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`; vollständig über die beiden Connector-Auszüge gelesen. Diese Aufgabe ist eine direkte Eigentümer-Fortsetzung, keine neue Bus-Adjudikation.

Alle Programme laufen vom Ordner `checks` aus. Der Name bezeichnet den Unterordner des hier verlinkten Prüfarchivs, keinen beliebig anzupassenden Repository-Pfad.

```
python build_tail.py
python build_source_polys.py
python cert_source_final.py
python check_final_algebra.py
python check_mixture.py
```

SymPy wird für die symbolischen Generatoren und den letzten Check verwendet. Der skalare rationale Intervallchecker benutzt die Python-Standardbibliothek. Es wurde nichts installiert. Die Protokolle liegen neben den Programmen. `mixture_checks.json` enthält den exakten negativen oberen Einschluss des Modell-Gegenchecks, nicht eine gerundete Ersatzkonstante.

Die analytischen Argumente — insbesondere das schwache Translationslimit, die Diagonaldivergenz, Tonelli und die Momentintegration — werden von diesen Programmen nicht automatisch überprüft. Ihre Beweise stehen im Text.
