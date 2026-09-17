# STATUS: TRY_FOLDED_CONTOUR_WITH_PAID_FREQUENCY_TAIL
```yaml
OPERATIVE_CLASS: TRY_FOLDED_CONTOUR_WITH_PAID_FREQUENCY_TAIL
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-17
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_PROOF_WITH_EXACT_CONSTANT_CHECKS_AND_DIAGNOSTIC_NUMERICS
INDEPENDENT_ANALYTIC_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
PROGRESS_CLASS: PROOF_PROGRESS_ON_FREQUENCY_DEPENDENT_REMAINDER
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
NEW_PAID_STATEMENTS:
  - EXACT_PAIRED_CONTOUR_HEAD_WITH_MODULAR_DEFECT_CORRECTION
  - FULL_SOURCE_DERIVATIVE_TAIL_BOUND_FOR_ORDERS_0_1_2
  - HB_ERROR_VANISHES_LINEarly_WITH_SIGMA
  - EXPLICIT_TWO_SIDED_HB_ENCLOSURE_WITH_EXPONENTIAL_FREQUENCY_DECAY
  - EXPLICIT_ADAPTIVE_CUTOFF_FOR_ANY_PRESCRIBED_POLYNOMIAL_SCALED_ERROR
GLOBAL_NONNEGATIVE_LOWER_ENVELOPE_PROVED: false
FINITE_HEAD_UNIFORM_SIGN_PROVED: false
HB_SIGN_CLOSED: false
SUPPORT_CLOSED: false
ORIGINAL_V_SIGN_CLOSED: false
ORIGINAL_V_NEGATIVE_WITNESS: false
NUMERICAL_RESULTS_ARE_SIGN_CERTIFICATES: false
PRIOR_Q_DERIVATIVE_CERTIFICATES_USED: false
REPOSITORY_CHANGED: false
PRODUCTION_STATE_CHANGED: false
CODEX_DISPATCHED: false
RH_CLAIM: false
```

## 0. Ergebnis und Grenze

**Eine globale nichtnegative Untergrenze der gefalteten Gesamtquelle ist in dieser Runde nicht bewiesen.** Bezahlt wird die vorher fehlende frequenzabhängige Fehlerseite: eine explizite zweiseitige Einschließung des ursprünglichen HB-Defekts. Sie erhält die vollständige Quelle, verschwindet mit sigma am Rand und trägt den Exponentialfaktor exp(-pi T/2). Ihr endlicher Mittelwert ist durch eine ausdrücklich angegebene endliche Summe unvollständiger Gammafunktionen bestimmt.

Dies ist mehr als ein neuer Name für einen unbestimmten Rest: Alle Konstanten, Integrale, Quantoren und eine gültige Abschneideregel werden unten angegeben. **Es ist zugleich weniger als der verlangte globale Vorzeichenbeweis:** Die Einschließung erhält nur dann ein nichtnegatives Vorzeichen, wenn ihre untere Grenze tatsächlich nichtnegativ ist. Diese zusätzliche Behauptung wird nicht aus der Kleinheit des Fehlers abgeleitet.

Die globale Aussage wird nicht als unmöglich bezeichnet. Eine zusätzliche Prüfung zeigt lediglich, warum auch der neue endliche Hilfsausdruck nicht ohne Beweis global positiv genannt werden darf.

Die Runde benötigt weder die alten Drei-/Vierpunktsätze noch ihre q-Ableitungszertifikate. Sie nimmt deren unabhängige Prüfung nicht vorweg.

## 1. Quellenbindung, Begriffe und unveränderte Zielgröße

**[ABSTRACT][PAPER: Quellenidentität und Definitionen]**

Gelesen wurden die für diesen Angriff benötigten Abschnitte des lokalen Vorgängerberichts:

`/mnt/data/theta_full_mixture/FULL_MIXTURE_COMPENSATION_ATTEMPT_2026-09-17.md`.

Der genaue Datei-Hash steht im mitgeführten `registration.json`. Insbesondere werden seine Abschnitte 1 und 5 für Quelle und Faltung sowie 8–10 für die Grenzen der alten Ansätze verwendet. Die alten numerischen Zertifikate wurden in dieser Runde **nicht** erneut ausgeführt.

Der konkrete Repository-Input wurde zusätzlich über den GitHub-Connector gelesen:

- Repository: `Malaeu/chen_q3`.
- Datei: `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Abschnitte 1–2.
- Commit: `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`.
- Blob: `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`.

Sein historischer Status `PAPER_AUDIT_PENDING_INDEPENDENT_CHECK` wird nicht aufgewertet. Wir benötigen hier seine Quellenidentität, nicht seinen abschließenden Weil-Transfer.

Für n>=1 sei a_n=pi n^2 und

\[
\phi_n(z)=\bigl(4a_n^2e^{9z/2}-6a_ne^{5z/2}\bigr)
            e^{-a_ne^{2z}}.
\]

Die vollständige Quelle ist

\[
\Phi(t)=\sum_{n\ge1}\phi_n(t),\qquad
F(p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt
    =\xi(1/2+p).
\]

Die Jacobi-Identität gibt Phi(-t)=Phi(t). Die vollständige Quelle ist reell, positiv und einschließlich jeder festen Ableitung hinreichend schnell fallend. Die komplexe Fortsetzung der hierfür benötigten Aussagen wird in Abschnitt 2 nachgewiesen.

Schreibe p=sigma+iT. Die Zielgröße ist **ohne Division** definiert:

\[
\mathscr H(p)=4\Re(F'(p)\overline{F(p)}).
\]

Insbesondere wird F(p) nicht als nullstellenfrei vorausgesetzt.

Der unveränderte vollständige Kern lautet

\[
K_\sigma(w)=\int_{\mathbb R}v\sinh(2\sigma v)
                 \Phi(v+w)\Phi(v-w)\,dv.
\]

Bei der Fourier-Konvention hat K(omega)=int K(w)exp(-i omega w)dw gilt

\[
\boxed{\mathscr H(\sigma+iT)=8\widehat K_\sigma(2T).}
\tag{1.1}
\]

Das folgt durch Ausmultiplizieren von F' conjugate(F), Symmetrisieren in den beiden Quellenvariablen und die Änderung t=v+w, u=v-w mit Jacobi-Faktor 2. Die Geradheit von Phi ersetzt v exp(2 sigma v) durch v sinh(2 sigma v).

Der Vorgänger faltete denselben Kern als

\[
K_\sigma(w)=2\int_0^\infty v\sinh(2\sigma v)
  \Phi(v+|w|)\Phi(|v-|w||)\,dv.
\tag{1.2}
\]

**Wichtige Operationsgrenze:** Die Beträge in (1.2) werden nicht in komplexe Variablen eingesetzt. Eine Konturverschiebung direkt durch diese stückweise Schreibweise wäre nicht begründet. Wir verwenden zuerst die exakte vollständige Identität (1.1), verschieben die holomorphe Quelle und falten erst danach wieder.

Die ursprüngliche Form V, ihr normiertes f und ihr SUPPORT-Objekt Y werden nicht geändert. Diese Runde behauptet keinen neuen direkten V-Transfer.

## 2. Komplexe Verschiebung der vollständigen Quelle

**[ABSTRACT][PAPER — neue Herleitung aus der Quellenreihe]**

Die Reihe für Phi(z) konvergiert lokal gleichmäßig im offenen Streifen

\[
|\Im z|<\pi/4,
\]

weil dort Re(e^(2z))>0. Sie definiert dort eine holomorphe Funktion. Auf der reellen Achse ist sie gerade; der Identitätssatz liefert daher

\[
\Phi(-z)=\Phi(z),\qquad
\Phi(\overline z)=\overline{\Phi(z)}
\quad (|\Im z|<\pi/4).
\tag{2.1}
\]

Dies benutzt die Jacobi-Identität und keinen Nullstellensatz für xi.

Fixiere

\[
0<\vartheta<\pi/4,\qquad c=\cos(2\vartheta)>0.
\]

Für t>=0 gilt

\[
|\phi_n(t\pm i\vartheta)|
\le
\bigl(4a_n^2e^{9t/2}+6a_ne^{5t/2}\bigr)
 e^{-a_nce^{2t}}.
\tag{2.2}
\]

Diese Hülle gibt auf jedem geschlossenen Teilstreifen die nötige sehr schnelle Abnahme bei t->+infinity. (2.1) gibt dieselbe Abnahme an der negativen Seite. Die vertikalen Seiten der üblichen Rechteckkontur verschwinden deshalb, auch nach Multiplikation mit jedem festen z^j exp(pz).

Daher gilt für j=0,1,2 und tatsächlich für jede feste Ableitungsordnung

\[
F^{(j)}(p)=\int_{\mathbb R}
(x+i\vartheta)^j\Phi(x+i\vartheta)e^{p(x+i\vartheta)}\,dx.
\tag{2.3}
\]

Für p=sigma+iT, T>=0, erscheint hierbei genau der Faktor exp(-vartheta T).

Nach Aufteilung bei x=0 und Anwendung von (2.1):

\[
\boxed{
F(p)=\sum_{n\ge1}\bigl[I_n(p,\vartheta)+I_n(-p,-\vartheta)\bigr],
}
\tag{2.4}
\]

wobei

\[
I_n(p,\vartheta)=\int_0^\infty
\phi_n(t+i\vartheta)e^{p(t+i\vartheta)}\,dt.
\tag{2.5}
\]

Beide reflektierten Strahlen haben denselben Dämpfungsfaktor exp(-vartheta T). Der zweite Winkel ist **-vartheta**, nicht +vartheta.

Die unten angegebenen Majoranten beweisen auch absolute Summierbarkeit einschließlich der benötigten p-Ableitungen. Es wird kein bedingt konvergenter Ganzgeradenausdruck termweise integriert.

## 3. Expliziter endlicher Ausdruck — mit allen Mischtermen

**[ABSTRACT][PAPER]**

Für N>=0 sei

\[
J_N(p;\vartheta)=
\sum_{n=1}^{N}\bigl[I_n(p,\vartheta)+I_n(-p,-\vartheta)\bigr].
\tag{3.1}
\]

Die endliche Summe ist ein Rechenausdruck zur Einschließung von F. Sie wird nicht als neue kanonische Quelle und nicht als bereits positiv bewiesener Transform interpretiert.

Die Substitution u=a_n exp(2z) ergibt die auswertbare Formel

\[
\boxed{
I_n(p,\vartheta)=a_n^{-p/2-1/4}
\left[
2\Gamma\!\left(\frac p2+\frac94,a_ne^{2i\vartheta}\right)
-3\Gamma\!\left(\frac p2+\frac54,a_ne^{2i\vartheta}\right)
\right].}
\tag{3.2}
\]

Gamma(a,z) ist die obere unvollständige Gammafunktion. Der Logarithmus von a_n ist reell; für das zweite Argument gilt |arg(a_n exp(2i vartheta))|<pi/2. Die Integration entlang des Strahls stimmt daher ohne einen Zweigwechsel mit dem üblichen Hauptzweig überein.

Alternativ, mit b=p/2+5/4 und z=a_n exp(2i vartheta):

\[
I_n(p,\vartheta)=a_n^{-p/2-1/4}
\left[(p-1/2)\Gamma(b,z)+2z^b e^{-z}\right].
\tag{3.3}
\]

Dies folgt aus der Gamma-Rekursion, nicht aus numerischem Anpassen.

Definiere

\[
h_N(p;\vartheta)=4\Re\left(J_N'(p;\vartheta)
                                      \overline{J_N(p;\vartheta)}\right).
\tag{3.4}
\]

**Alle Kreuzprodukte der Summanden werden in (3.4) zusammenbehalten.** Eine Summe bloßer diagonaler HB-Werte wäre nicht (3.4).

### 3.1 Die entfernte Faltnaht ist exakt bezahlt

Sei g_N(z)=sum_(n<=N) phi_n(z), und sei

\[
F_N^{\mathrm{real}}(p)=2\int_0^\infty g_N(t)\cosh(pt)\,dt
\]

der frühere endliche cosh-Ausdruck. Dann gilt exakt

\[
\boxed{
J_N(p;\vartheta)=F_N^{\mathrm{real}}(p)
-\int_0^{i\vartheta}
       \bigl[g_N(z)-g_N(-z)\bigr]e^{pz}\,dz.
}
\tag{3.5}
\]

Beweis: Verschiebe den positiven Halbstrahl nach +i vartheta und den reflektierten Halbstrahl nach -i vartheta. Die zwei vertikalen Verbindungsstücke ergeben genau die Differenz in (3.5).

Die vollständige Phi erfüllt Phi(z)-Phi(-z)=0. Ein endliches g_N erfüllt dies im Allgemeinen nicht. (3.5) behält den **gesamten** endlichen modularen Defekt, nicht nur eine endliche Zahl seiner Taylor-Koeffizienten. Die Korrektur beseitigt die frühere unzulässige Behandlung der Faltnaht. Numerisch sollte man (3.2) oder (3.3) auswerten, statt zwei bei hohen Frequenzen stark kompensierende Terme aus (3.5) getrennt abzuziehen.

### 3.2 Genau die benötigte Randsymmetrie bleibt erhalten

Aus reellen Koeffizienten und dem reflektierten zweiten Strahl folgt

\[
\boxed{J_N(-\overline p;\vartheta)=\overline{J_N(p;\vartheta)}.}
\tag{3.6}
\]

Daher ist J_N(iT) reell und J_N'(iT) rein imaginär. Insbesondere

\[
h_N(iT;\vartheta)=0,\qquad \mathscr H(iT)=0.
\tag{3.7}
\]

Das gilt auch an Nullstellen und benötigt weder Einfachheit noch Nichtverschwinden.

J_N wird hier **nicht** als gerade reelle ganze Funktion ausgegeben; (3.6) ist die tatsächlich erhaltene Symmetrie. Diese Unterscheidung verhindert eine falsche Übertragung alter Realnullstellen-Sätze.

## 4. Vollständig explizite Restmajoranten für die Quelle und ihre Ableitungen

**[ABSTRACT][PAPER]**

Setze M=N+1 und

\[
\beta=\pi cM^2.
\]

Für |Re p|<=1/2, Im p=T>=0, j=0,1,2 beweisen wir

\[
\boxed{
|F^{(j)}(p)|,\ |J_N^{(j)}(p;\vartheta)|
\le D(c)e^{-\vartheta T},\qquad D(c)=4c^{-4},
}
\tag{4.1}
\]

sowie für beta>=1

\[
\boxed{
|F^{(j)}(p)-J_N^{(j)}(p;\vartheta)|
\le B(c,M)e^{-\vartheta T},\qquad
B(c,M)=448c^{-1}M^3e^{-\pi cM^2}.
}
\tag{4.2}
\]

### Vollständiger Majorantenbeweis

Für t>=0 gilt vartheta<1 und

\[
|t\pm i\vartheta|^j\le(t+1)^j\le e^{jt}.
\]

Mit |Re p|<=1/2, den beiden Strahlen und u=exp(2t) ist der Beitrag des n-ten Paars höchstens

\[
e^{-\vartheta T}
\left[
4a_n^2\int_1^\infty u^{(3+j)/2}e^{-a_ncu}\,du
+6a_n\int_1^\infty u^{(1+j)/2}e^{-a_ncu}\,du
\right].
\tag{4.3}
\]

Für j<=2 dürfen die Potenzen durch u^3 und u^2 majorisiert werden.

Für die Gesamtnorm verlängere beide Integrale nach null. Es folgt

\[
\sum_{n\ge1}\left(24a_n^{-2}c^{-4}+12a_n^{-2}c^{-3}\right)
\le36c^{-4}\pi^{-2}\sum_{n\ge1}n^{-4}<4c^{-4}.
\]

Die letzte Zahl benötigt nicht einmal die geschlossene Auswertung von zeta(4). Aus Monotonie folgt

\[
\sum n^{-4}\le1+\frac1{16}+\frac2{81},\qquad \pi>\frac{157}{50},
\]

und exakt rational

\[
36\left(1+\frac1{16}+\frac2{81}\right)\left(\frac{50}{157}\right)^2
=\frac{880625}{221841}<4.
\]

Das beweist (4.1) für die vollständige Quelle und jede partielle Summe.

Für den Schwanz sind beta_n=a_nc>=1. Exakte partielle Integration liefert

\[
\int_1^\infty u^3e^{-\beta_nu}\,du
=e^{-\beta_n}\left(\frac1{\beta_n}+\frac3{\beta_n^2}
                 +\frac6{\beta_n^3}+\frac6{\beta_n^4}\right)
\le\frac{16e^{-\beta_n}}{\beta_n},
\]

\[
\int_1^\infty u^2e^{-\beta_nu}\,du
\le\frac{5e^{-\beta_n}}{\beta_n}.
\]

(4.3) wird damit durch

\[
\frac{256}{c}e^{-\vartheta T}
                 \sum_{n=M}^{\infty} n^2 e^{-bn^2},\qquad b=\pi c,
\]

majorisiert; hier wurde nur 64pi+30<256 verwendet.

Da bM^2>=1, ist x^2 exp(-bx^2) ab M monoton fallend. Ferner

\[
\int_M^\infty x^2e^{-bx^2}\,dx
\le e^{-bM^2}\left(\frac{M}{2b}+\frac1{4b^2M}\right).
\]

Somit

\[
\sum_{n=M}^{\infty}n^2e^{-bn^2}
\le e^{-bM^2}\left(M^2+\frac{M}{2b}+\frac1{4b^2M}\right)
\le\frac74M^3e^{-bM^2}.
\]

Der Faktor 256*(7/4)=448 beweist (4.2). Kein unbestimmter O-Term und kein vermuteter Nullstellenabstand steckt in diesem Budget.

## 5. Eine echte zweiseitige Hülle des ursprünglichen HB-Defekts

**[ABSTRACT][PAPER]**

Für 0<=sigma<=1/2 ist die neue Hülle

\[
\boxed{
 h_N(\sigma+iT;\vartheta)-\mathcal E_N
 \le\mathscr H(\sigma+iT)
 \le h_N(\sigma+iT;\vartheta)+\mathcal E_N,
}
\tag{5.1}
\]

mit

\[
\boxed{
\mathcal E_N=
28672\,\sigma\,c^{-5}M^3
\exp\bigl(-\pi cM^2-2\vartheta T\bigr),
\quad \pi cM^2\ge1.
}
\tag{5.2}
\]

### Warum kein konstanter Fehler am kritischen Rand übrig bleibt

Die naive Produkthülle wäre korrekt, würde aber bei sigma->0 einen unnötigen konstanten Rest behalten. Wir benutzen stattdessen zuerst die exakte gemeinsame Randsymmetrie (3.7).

Bei festem T, vartheta und N gilt

\[
\frac14\partial_\sigma\mathscr H
=\Re(F''\overline F)+|F'|^2,
\]

und entsprechend für h_N. Schreibe E_j=F^(j)-J_N^(j). Dann

\[
F''\overline F-J_N''\overline{J_N}
=E_2\overline F+J_N''\overline{E_0},
\]

\[
\bigl||F'|^2-|J_N'|^2\bigr|
\le |E_1|\bigl(|F'|+|J_N'|\bigr).
\]

(4.1)–(4.2) ergeben deshalb

\[
|\partial_\sigma(\mathscr H-h_N)|
\le16D(c)B(c,M)e^{-2\vartheta T}.
\]

Integriere von 0 bis sigma. Der Anfangswert ist exakt null. Einsetzen von D und B gibt (5.2).

**Mischterme sind nicht weggefallen.** Sie wurden zuerst in der exakten Produktdifferenz zusammengeführt und dann mit einer bezahlten Hülle kontrolliert.

Für den gefalteten Kern selbst ist (5.1) die Hülle

\[
\frac{h_N-\mathcal E_N}{8}
\le\widehat K_\sigma(2T)
\le\frac{h_N+\mathcal E_N}{8}.
\tag{5.3}
\]

Dies ist eine Einschließung des ursprünglichen vollständigen Fourier-Werts. **(5.3) behauptet nicht, dass ihr linker Rand bereits nichtnegativ ist.**

## 6. Explizite Abschneideregel für alle hohen Frequenzen

**[ABSTRACT][PAPER]**

Für T>=1 setze

\[
\vartheta(T)=\frac\pi4-\frac1{T+1},\qquad
c(T)=\sin\frac2{T+1}.
\tag{6.1}
\]

Dann 0<vartheta<pi/4, c>=1/(T+1), und

\[
e^{-2\vartheta T}\le 8e^{-\pi T/2}.
\]

Aus (5.2) folgt

\[
\boxed{
\mathcal E_N
\le229376\,\sigma\,(T+1)^5M^3
 e^{-3M^2/(T+1)}e^{-\pi T/2}.
}
\tag{6.2}
\]

Alle Frequenzen T>=1 sind enthalten; nicht nur die unten diagnostisch ausgewerteten Punkte.

Sogar eine vollständig vorgeschriebene Fehlerordnung ist möglich. Für beliebiges r>=0 setze t=T+1 und

\[
\Lambda_r(t)=32+2(r+10)\log t,
\qquad
M_r(T)=\left\lceil\sqrt{\frac{t\Lambda_r(t)}3}\right\rceil,
\qquad N=M_r(T)-1.
\tag{6.3}
\]

Dann beta>=1 und

\[
\boxed{
\mathcal E_N\le
\sigma\,(T+1)^{-r}e^{-\pi T/2}.
}
\tag{6.4}
\]

Beweis: M^3<=8t^2 Lambda^2, da sqrt(t Lambda/3)>=1. Weiter ist Lambda>=32 und Lambda^2<=exp(Lambda/4). Die rechte Seite von (6.2), ohne sigma exp(-pi T/2), ist daher höchstens

\[
1835008\,t^7e^{-3\Lambda/4}
=1835008e^{-24}t^{-8-3r/2}
<t^{-r}.
\]

Die letzte Konstante ist sicher kleiner als eins, denn e>2 und 1835008<2^24. Damit ist (6.4) bewiesen.

Der Preis ist ein expliziter wachsender endlicher Cutoff von der Größenordnung sqrt(T log T) bei festem r. Hier wird kein endlicher N für alle Frequenzen eingefroren.

**Ableitungskonvention:** In J_N', J_N'' und h_N werden vartheta und N bei der p-Ableitung festgehalten. Erst für die Auswertung bei einer bestimmten Frequenz werden (6.1) und (6.3) gewählt. Es wird nicht durch den gerundeten Cutoff und nicht durch vartheta(T) differenziert.

Negative Frequenzen werden durch die reelle Symmetrie von F bzw. die entsprechend konjugierte Strahlenwahl abgedeckt.

## 7. Angriff auf die noch fehlende positive Seite

**[ABSTRACT][PAPER]**

Die erforderliche globale Aussage wäre jetzt beispielsweise

\[
h_N(\sigma+iT;\vartheta(T))\ge \mathcal E_N
\quad (0<\sigma<1/2,\ T>\sqrt{20}),
\tag{7.1}
\]

für eine begründete Wahl von N, oder eine stärkere direkt vorzeichenbehaftete Fehlerbehandlung, welche den kleinen positiven Puffer auf der rechten Seite nicht benötigt.

**(7.1) wurde nicht bewiesen.** Die quantitativ bezahlte Fehlerseite ersetzt nicht die Analyse des gekoppelten endlichen Ausdrucks.

Insbesondere geben die universellen Betragsmajoranten nur zweiseitige Größe, keine positive Orientierung. Für zwei beliebige komplexe Summanden a_i und ihre Ableitungen b_i ist die Hermitesche Koeffizientenform von

`4 Re((sum c_i b_i) conjugate(sum c_i a_i))`

im Allgemeinen indefinit: Ihr Zweierdeterminant ist

\[
-4|a_1b_2-a_2b_1|^2.
\]

Das widerlegt nur einen phasenunabhängigen Positivitätsschluss aus Einzelbeträgen. Die tatsächlichen Theta-Koeffizienten sind fest; ihr Vorzeichen wird hierdurch weder widerlegt noch bewiesen.

### 7.1 Auch ein korrigierter endlicher Ausdruck ist nicht automatisch ein positiver Erzeuger

Bei festem N und festem vartheta kann eine neue Faltnaht am Punkt i vartheta auftreten. Schreibe

\[
J_N(p;\vartheta)=e^{i\vartheta p}P_N(p),
\]

wobei P_N das Laplace-Integral der stückweise reflektierten endlichen Quelle auf der verschobenen Geraden ist. Der Sprung bei x=0 ist

\[
g_N(i\vartheta)-g_N(-i\vartheta)=2i a,
\qquad a=\Im g_N(i\vartheta)\in\mathbb R.
\]

Ist a!=0, liefern separate partielle Integrationen für P_N und P_N' die Entwicklungen

\[
P_N(p)=\frac{A}{p}+\frac{B}{p^2}+O(T^{-3}),\qquad
P_N'(p)=-\frac{A}{p^2}-\frac{2B}{p^3}+O(T^{-4}),
\]

mit A=-2ia rein imaginär und B reell. Alle benötigten einseitigen Ableitungen sind wegen (2.2) integrabel. Die zweite Entwicklung wird aus dem Integral mit zusätzlichem x-Faktor gewonnen, nicht durch unkontrolliertes Differenzieren eines O-Terms.

Da Re(i vartheta |P_N|^2)=0 und A conjugate(B) rein imaginär ist,

\[
\boxed{
\lim_{T\to\infty}T^4e^{2\vartheta T}
 h_N(\sigma+iT;\vartheta)=-16\sigma a^2<0
\quad(\sigma>0\text{ fest}).
}
\tag{7.2}
\]

Damit gibt es für solche festen Hilfsausdrücke auch eine strikt negative obere Hülle bei hinreichend großem T: etwa die halbe negative Grenzkonstante nach der Skalierung.

Solche Winkel existieren bereits für N=1. Denn

\[
g_1'(0)=\pi e^{-\pi}(-8\pi^2+30\pi-15)>0;
\]

das Polynom ist auf [3,22/7] fallend und hat bei 22/7 noch den Wert 13/49>0. Folglich ist Im g_1(i vartheta)>0 für genügend kleine positive vartheta.

**Das ist eine Grenze des festen endlichen Hilfsausdrucks, kein negativer Zeuge für F oder K.** Der adaptive Cutoff aus (6.3) wird durch (7.2) nicht getroffen. Die Fehlerhülle (5.1) bleibt auch bei einem negativen h_N korrekt; ein negativer Mittelpunkt ohne negativen oberen Rand ist kein Negativzertifikat für die vollständige Quelle.

Die alte reale Faltnaht wurde mit (3.5) korrekt behandelt. Bei erneutem Einfrieren eines endlichen Cutoffs darf man die verbleibende endliche Abweichung auf der verschobenen Naht ebenfalls nicht vergessen. Die vollständige Quelle besitzt keinen solchen Sprung.

## 8. Tatsächlich ausgeführte Prüfungen und ihre Aussagekraft

### 8.1 Exakte Konstanten und algebraische Kontrollen

`check_algebra_and_plants.py` hat mit rationaler Arithmetik kontrolliert:

- 880625/221841<4.
- 64*(22/7)+30<256.
- 256*(7/4)=448.
- 16*4*448=28672.
- 8*28672=229376.
- 8*229376=1835008<2^24.

SymPy hat die Stammfunktionen der beiden polynomialen Exponentialmajoranten exakt differenziert. Diese Kontrollen prüfen die Konstanten und algebraischen Teilidentitäten. Sie überprüfen nicht automatisch die analytische Konturverschiebung oder die Quellenidentität.

### 8.2 Diagnosevergleich mit einer anderen xi-Formel

Der finite Ausdruck (3.3) wurde mit der zeta/Gamma-Definition von xi verglichen. Beide Auswertungen verwenden dieselbe mpmath-Bibliothek, aber unterschiedliche Formeln. Es handelt sich nicht um unabhängige Intervallimplementierungen.

Vorregistriert waren sigma=1/4, T in {10,20,40}, vartheta wie (6.1) und M=ceil sqrt(40/c). Dieser Diagnosecutoff ist eine zulässige Wahl für (5.1), nicht die allgemeine Abschneideregel (6.3).

Mit 80 Dezimalstellen ergab sich:

| T | N | Größter beobachteter skalierter Ableitungsfehler, j=0,1,2 | Analytischer skalierter B-Rand |
|---:|---:|---:|---:|
| 10 | 14 | etwa 6.01e-53 | etwa 2.60e-49 |
| 20 | 20 | etwa 9.03e-55 | etwa 2.65e-50 |
| 40 | 28 | etwa 3.91e-53 | etwa 2.52e-48 |

Skalierung bedeutet Multiplikation des Ableitungsfehlers mit exp(vartheta T). Die beobachteten HB-Fehler lagen ebenfalls innerhalb der analytisch hergeleiteten Hülle.

Der erste T=10-Lauf mit 50 Dezimalstellen zeigte bei zwei Ableitungen numerisch null und bei der anderen einen Präzisionsboden. Er wurde als Diagnose mit 80 Stellen wiederholt. **Die gedruckten Nullen des ersten Laufs werden nicht als exakte Gleichheiten interpretiert.**

Aus diesen Rechnungen wird kein neuer positiver Frequenzbereich zertifiziert. Mpmath ist keine Intervallarithmetik. Die Universalität von (5.1) folgt ausschließlich aus dem analytischen Beweis.

### 8.3 Absichtlich falsche Kontrollen

Der gesamte vertikale Defekt in (3.5) wurde bei N=1, vartheta=1/4, p=1/4+10i numerisch integriert. Er stimmt mit F_N^real-J_N bis etwa 5.9e-67 überein; sein Betrag ist etwa 0.000127957. Ein Weglassen der Nahtkorrektur ist damit diagnostisch sichtbar, nicht von Rundungsfehlern verborgen.

Ein zweiter Plant ersetzte im zweiten Strahl -vartheta absichtlich durch +vartheta. Bei T=20 wurde die falsche Formel von der Referenz und der behaupteten korrekten Fehlerhülle eindeutig verworfen. Dieses Instrument ist also nicht so gebaut, dass jede Strahlenorientierung einen Erfolg meldet.

Auch diese beiden Kontrollen sind Diagnostik. Die exakten Identitäten und die Ablehnungsgründe stehen im analytischen Beweis.

## 9. Was dieser Versuch nicht schließt

Der ursprüngliche Wunsch war eine echte vorzeichenbewahrende Abschätzung der gefalteten Gesamtquelle für alle noch offenen Frequenzen. **Ein überall nichtnegativer linker Rand ist hier nicht geliefert.**

Geliefert ist nun der zuvor fehlende, ausdrücklich aus der Quelle berechnete Fehlerterm, mit zwei entscheidenden Eigenschaften:

1. Er trägt dieselbe konturbedingte Exponentialskala exp(-pi T/2), statt bei großen T als fester positiver Rest stehenzubleiben.
2. Er verschwindet bei sigma=0 exakt und mindestens linear, ohne dort durch unbekannte Nullstellen zu dividieren.

Die verbleibende Aussage über den gekoppelten endlichen Ausdruck ist ernsthafte nicht erledigte Mathematik. Sie wird weder als bloße Buchhaltung noch als automatisch gelöste Kleinheitsfrage bezeichnet.

**Keine Aussage dieser Runde beweist das globale HB-Vorzeichen, den einseitigen Träger von Y oder das Vorzeichen von V.** Keine negative obere Hülle der ursprünglichen vollständigen Quelle wurde gefunden.

## 10. Zwei Darstellungen des nicht geschlossenen Vorzeichenteils

**R1 — primär: endliche gepaarte Gamma-Summe mit bezahltem adaptivem Schwanz.** Der konkrete Ausdruck ist (3.2)–(3.4); die Fehlerseite ist (5.2) oder (6.4). Ein wirklicher positiver unterer Rand bzw. negativer oberer Rand wäre für den unveränderten Verbraucher entscheidend. Die endliche Auswertung ist vergleichsweise billig; ein analytischer Vorzeichenbeweis bei allen sigma,T ist nicht verfügbar und sein Aufwand wird nicht mit einer optimistischen Zahl geschätzt.

**R2 — analytische Gegenrepräsentation: vollständige vertikale Modularkorrektur vor jeder Quadratabschätzung.** (3.5) hält den endlichen Realachsen-Ausdruck und sämtliche ungeraden Defektkoeffizienten in einem einzigen exakten Integral zusammen. Eine quellenabhängige Kontrolle der daraus entstehenden gemischten HB-Terme könnte die symmetrische Fehlerhülle verbessern. Diese Darstellung ist analytisch ausdrücklich, numerisch aber bei hohen Frequenzen wegen starker Auslöschung schlechter konditioniert. Auch hier fehlt ein bewiesener globaler Vorzeichensatz.

Das sind zwei überprüfbare Darstellungen desselben ursprünglichen Problems, keine zwei behaupteten Lieferanten. Ein bloßer Wechsel zwischen ihren Namen zählt nicht als weiterer Fortschritt.

### Diskriminator

Für jedes spezifizierte Gebiet oder jeden Punkt ist der Diskriminator der tatsächliche Einschluss

\[
[L_N,U_N]=[h_N-\mathcal E_N,h_N+\mathcal E_N].
\]

Nur ein rigoros ausgewerteter L_N>=0 liefert einen positiven Nachweis auf dem zertifizierten Gebiet. Nur U_N<0 liefert einen negativen Vollquellenzeugen. Ein nullüberlappendes Intervall bleibt unentschieden; ein positiver Gleitkommawert des Mittelpunkts entscheidet nichts.

## 11. K8A und Abschluss

**DOWNSTREAM_CONSUMER:** Der globale HB-Zeichensatz für exakt F(p)=xi(1/2+p), danach die schon getrennt formulierten bedingten SUPPORT/V-Verbraucher.

**ACTUAL_CONSUMER_REQUIREMENT:** H(sigma+iT)>=0 für alle benötigten sigma,T. Keine Menge positiver endlicher Stichproben ersetzt diesen Quantor.

**ORIGINAL_REQUESTED_OBJECT:** Vorzeichenbewahrende Kontrolle der gefalteten Gesamtquelle. Für den gewählten Verbraucher ist der globale Zeicheninhalt notwendig. Die konkrete Gamma-Abschneidung ist **NOT_NECESSARY**; sie ist eine gewählte hinreichende Schnittstelle zusammen mit einem bezahlten Kopfvorzeichen.

**KNOWN_WEAKER_INTERFACES:** Ein direkter gemeinsamer Fourier-Zeichenbeweis kann die endliche Summe und alle Abschneidebudgets umgehen. Ein Beweis von h_N>=E_N mit zulässigem N(sigma,T) reicht aus. Eine exakt gerichtete Restkontrolle statt |H-h_N|<=E_N könnte schwächer sein als diese gepufferte Schnittstelle. Keine dieser unbewiesenen Aussagen wird zur Voraussetzung erklärt, die man einfach verlangen darf.

**FAILURE_TYPE / EPISTEMIC_STATUS:** Für den vollständigen Vorzeichenbeweis `NO_DERIVATION / RESEARCH_DEBT`. Keine mathematische Unmöglichkeit der Hauptroute. Der feste endliche Hilfsausdruck in Abschnitt 7.1 ist auf seinem präzisen Geltungsbereich kein global positiver Erzeuger; der adaptive und der vollständige Ausdruck sind davon getrennt.

**REOPEN_TRIGGER:** Ein echter gemeinsamer Vorzeichenvergleich für die konkret auswertbare Summe und ihren bezahlten Rest, oder ein strikt negativer oberer Einschluss der tatsächlichen Gesamtquelle. Weitere positive kleine Matrizen, bloß mehr Gleitkommapunkte und ein kleiner Betrag ohne Orientierung sind kein globaler Lieferant.

**NOVELTY_AXIS:** Die hier vollständig hergeleitete sigma-verschwindende Fehlerhülle und ihr explizites Budget im bestehenden Quellenprotokoll. Konturverschiebung und unvollständige Gammafunktionen sind klassische Werkzeuge. Eine historische Priorität oder eine neue Lösung der RH wird nicht behauptet.

**Vorhersagen:** P_CONTOUR_1 und P_CONTOUR_2 sind durch die Papierherleitung bestätigt und diagnostisch konsistent. P_CONTOUR_3 war als Warnung vor einem nicht bezahlten Kopfvorzeichen registriert; kein globales Kopfvorzeichen wurde gefunden. Dies wird nicht nachträglich als Beweis seiner Unmöglichkeit gewertet. Die zusätzlichen Naht- und Orientierungs-Plants wurden vor ihrem Lauf registriert und verworfen die vorgesehenen falschen Formeln.

**Was kleiner wurde:** Der unbestimmte hochfrequente Fehler der Quelle ist durch (5.2) und (6.3) vollständig ersetzt. Die Vorzeichenbehauptung des endlichen gekoppelten Ausdrucks bleibt offen. Diese Trennung ist die Fortschrittsbilanz; sie wird nicht als globale Schließung verkauft.

**Verbotene Wiederholung:** Nicht H_N^real, J_N, F und K vertauschen; nicht +vartheta statt -vartheta am reflektierten Strahl einsetzen; nicht bei der p-Ableitung durch den Cutoff differenzieren; nicht den bekannten Schwanzfehler anstelle des noch fehlenden Kopfvorzeichens ausgeben.

**Ausführung:** Keine Repository-Schreiboperation, keine Änderung der Bus- oder Produktionszustände, kein Lean-Code und kein Codex-Dispatch. Die Aufgabe ist eine direkte Fortsetzung des Eigentümers in diesem Gespräch, keine neue Bus-Adjudikation.

## 12. Primärquellen und Reproduktion

Die externen Inputs sind getrennt von der hier hergeleiteten Abschätzung:

- NIST DLMF, Abschnitt 20.7(viii), insbesondere 20.7.32: Jacobi-Transformation. `https://dlmf.nist.gov/20.7`
- NIST DLMF, Abschnitt 25.5: Theta-/Mellin-Integralrepräsentationen der Zeta-/xi-Funktion. `https://dlmf.nist.gov/25.5`
- NIST DLMF, Abschnitt 8.2: Definition und Zweigkonventionen der unvollständigen Gammafunktionen. `https://dlmf.nist.gov/8.2`
- Gepinnter Repository-Quellenbericht und lokaler Vorgängerbericht wie Abschnitt 1.
- Projektprotokoll: `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, Branch `rh_clean`, Blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`, in dieser Runde über den Connector gelesen.

Die Skripte befinden sich neben diesem Bericht. Es wurde kein Paket installiert. Verwendet wurden Python, SymPy und mpmath. `flint` war im aktuellen Lauf nicht installiert; kein Arb-Zertifikat wird behauptet.

Ausgeführt wurden:

```
python check_contour.py --T 10 --dps 50
python check_contour.py --T 10 --dps 80
python check_contour.py --T 20 --dps 80
python check_contour.py --T 40 --dps 80
python check_algebra_and_plants.py
```

Die Argumente `--T` und `--dps` setzen die Diagnosefrequenz bzw. die Dezimalpräzision; etwa `--T 20 --dps 80` prüft T=20 mit 80 Dezimalstellen. Sie bestimmen keine neuen analytischen Annahmen. Die vorregistrierten Tests stehen im ursprünglichen `registration.json`; die Ausgaben in `check_T*_dps*.json` und `algebra_and_plants.json`.

**Die analytischen Beweise dieses Berichts sind durch die Programme nicht automatisch zertifiziert.**
