# STATUS: TRY_MULTIPLICITY_COMPATIBLE_COUPLED_SIGN
```yaml
OPERATIVE_CLASS: TRY_MULTIPLICITY_COMPATIBLE_COUPLED_SIGN
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-17
PRIMARY: GLOBAL_MARGIN_NOT_PROVED_QUANTITATIVE_BOUNDARY_OBLIGATION_EXPOSED
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_AUDIT_WITH_EXACT_ALGEBRA_CHECKS
GLOBAL_REQUESTED_COMPARISON_PROVED: false
GLOBAL_REQUESTED_COMPARISON_REFUTED_FOR_THETA: false
THETA_MULTIPLE_ZERO_FOUND: false
HB_SIGN_CLOSED: false
SUPPORT_CLOSED: false
ORIGINAL_V_SIGN_CLOSED: false
ORIGINAL_V_NEGATIVE_WITNESS: false
NEW_ESTABLISHED_IMPLICATION:
  fixed_sigma_independent_cutoff_margin: quantitative_boundary_Laguerre_floor
  consequence_at_critical_zeros: simplicity_and_explicit_derivative_lower_bound
ERROR_BUDGET_CHANGED: false
INHERITED_ERROR_PROOF_HAS_STRICT_SLACK: true
STRICT_SLACK_BOUND: actual_HB_error_at_most_9_over_10_of_original_budget
PROGRESS_CLASS: REPRESENTATION_PROGRESS_ON_QUANTIFIER_AUDIT
GLOBAL_SIGN_PROGRESS: NO_NEW_SIGN_SUPPLIER
INDEPENDENT_MATHEMATICAL_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
REPOSITORY_CHANGED: false
PRODUCTION_STATE_CHANGED: false
CODEX_DISPATCHED: false
RH_CLAIM: false
```

## 0. Ergebnis, ohne Ersatzbehauptung

Der verlangte globale Vergleich des zuvor ausdrücklich hingeschriebenen gekoppelten Ausdrucks mit seinem Fehlerbudget ist **in dieser Runde nicht bewiesen**. Es wird auch kein Gegenbeispiel für die vollständige Theta-Quelle oder den konkreten adaptiven Ausdruck behauptet.

Die direkte Prüfung der Grenzfläche sigma=0 hat einen präzisen zusätzlichen Gehalt der gewählten Schnittstelle ergeben: Ein erfolgreicher Vergleich mit dem zuvor vorgeschriebenen **nur von T abhängigen** Cutoff würde nicht bloß das nichtnegative HB-Vorzeichen liefern. Er würde eine strikt positive quantitative Laguerre-Schranke auf der kritischen Linie beweisen und damit jede kritische Nullstelle in der untersuchten Höhenmenge als einfach nachweisen.

Das ist kein Argument gegen die mögliche Wahrheit des Vergleichs. Es ist eine Anforderung, die der frühere Vorschlag nicht ausdrücklich gemacht hatte. Der vollständige HB-Zeichensatz verlangt diese zusätzliche Einfachheit nicht. Der generische Schluss von HB-Positivität zu einer positiven linearen Randreserve wird unten durch einen exakt berechneten positiven HB-Modellfall mit doppelten Randnullstellen widerlegt.

Die neue kleine Verbesserung der bereits bekannten Betragsmajorante wird **nur verwendet, um diese logische Konsequenz nachzuweisen**. Sie wird nicht als weiterer Erfolg am offenen Quellenzeichen verkauft.

## 1. Bindung an den tatsächlich gemeinten Ausdruck

**[ABSTRACT][PAPER — Definitionen und gelesene Quellen]**

Vollständig gelesen wurde:

`/mnt/data/theta_folded_contour/FOLDED_FULL_SOURCE_CONTOUR_ENCLOSURE_2026-09-17.md`

SHA-256:

`5af1cf1a4848aec595e07c099d1193ddffd57e257ea2cdecc17f1cfdbf5409e8`.

Die zugehörige ZIP-Datei wurde für die ursprünglichen Implementierungs- und Ableitungskonventionen geöffnet. Die alten Diagnosehöhen wurden **nicht** erneut als Positivitätstest gerechnet.

Zusätzlich wurde der Quellenbericht über den GitHub-Connector gelesen:

- Repository `Malaeu/chen_q3`.
- `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, Abschnitte 1–2.
- Commit `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`.
- Blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`.

Sein eigener historischer Prüfstatus wird nicht aufgewertet. Die allgemeine terminale Weil-Äquivalenz wird hier nicht neu zertifiziert. Benötigt werden die Quellenformel und ihre genaue Normierung.

Das aktuelle Projektprotokoll wurde von `rh_clean` über den Connector gelesen; sein Blob ist `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Diese Aufgabe ist eine direkte analytische Fortsetzung des Eigentümers, keine neue Bus-Adjudikation.

Wir behalten

\[
F(p)=\xi(1/2+p),\qquad
\mathscr H(p)=4\Re(F'(p)\overline{F(p)}),
\]

\[
\phi_n(z)=(4a_n^2e^{9z/2}-6a_ne^{5z/2})e^{-a_ne^{2z}},
\qquad a_n=\pi n^2,
\]

und die vollständige Quelle \(\Phi=\sum_{n\ge1}\phi_n\). Der verwendete Integraltransform ist

\[
F(p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt.
\]

Für \(0<\vartheta<\pi/4\) sind

\[
I_n(p,\vartheta)=\int_0^\infty
\phi_n(t+i\vartheta)e^{p(t+i\vartheta)}\,dt,
\]

\[
J_N(p;\vartheta)=\sum_{n=1}^N
[I_n(p,\vartheta)+I_n(-p,-\vartheta)],
\]

\[
h_N(p;\vartheta)=4\Re(J_N'(p;\vartheta)\overline{J_N(p;\vartheta)}).
\]

Die Endlichkeit wird nicht mit dem Zeichen verwechselt. In \(h_N\) bleiben sämtliche Kreuzprodukte enthalten. Die unvollständige-Gamma-Darstellung aus dem Vorgänger ist unverändert:

\[
I_n(p,\vartheta)=a_n^{-p/2-1/4}
\left[
2\Gamma\!\left(p/2+9/4,a_ne^{2i\vartheta}\right)
-3\Gamma\!\left(p/2+5/4,a_ne^{2i\vartheta}\right)
\right].
\]

Der Hauptzweig bleibt durch \(|2\vartheta|<\pi/2\) festgelegt. Bei Ableitungen nach p werden N und vartheta festgehalten.

### 1.1 Quantoren der gefrorenen Schnittstelle

Fixiere zunächst einen realen Genauigkeitsparameter \(r\ge0\). Für \(T\ge1\) setze

\[
t=T+1,\qquad
\vartheta(T)=\pi/4-1/t,\qquad
c(T)=\cos(2\vartheta(T))=\sin(2/t),
\]

\[
\Lambda_r(t)=32+2(r+10)\log t,
\]

\[
M_r(T)=\left\lceil\sqrt{t\Lambda_r(t)/3}\right\rceil,
\qquad N_r(T)=M_r(T)-1.
\]

Das ursprüngliche, unveränderte Fehlerbudget ist

\[
\mathcal E_N(\sigma,T;\vartheta)=\sigma e_N(T;\vartheta),
\]

\[
\boxed{
e_N(T;\vartheta)=28672c^{-5}M^3
\exp[-\pi cM^2-2\vartheta T],\quad M=N+1.
}
\tag{1.1}
\]

Der hier direkt angegriffene Satz lautet

\[
\boxed{
\forall T>\sqrt{20}\ \forall\,0<\sigma<1/2:
\quad h_{N_r(T)}(\sigma+iT;\vartheta(T))
\ge\sigma e_{N_r(T)}(T;\vartheta(T)).
}
\tag{G_r}
\]

Insbesondere wird \(N_r(T)\) beim Grenzübergang \(\sigma\downarrow0\) **nicht** geändert. Rundungssprünge als Funktion von T stören diesen Grenzübergang nicht, denn T ist dabei fest.

Der Vorgänger erwähnte daneben eine freiere Wahl \(N=N(\sigma,T)\). Sie ist nicht dasselbe wie \((G_r)\). Abschnitt 7 behandelt diese andere Quantorenfolge ausdrücklich. Keine davon wird hier stillschweigend für bewiesen erklärt.

## 2. Prüfprognosen vor den Tests

Die ursprüngliche Registrierung steht in `registration.json`.

- **P_MARGIN_BOUNDARY (0.80):** Die feste Schnittstelle verlangt eine strikt positive Rand-Laguerre-Schranke und damit zusätzliche quantitative Einfachheit an kritischen Nullstellen.
- **P_MARGIN_GENERIC (0.95):** Die bezahlten Fehler-, Holomorphie- und Reflexionsabschätzungen allein erzwingen das Kopfvorzeichen nicht.
- **P_MARGIN_DIRECT (0.10):** Aus dem konkreten gekoppelten Gamma-Ausdruck gelingt in dieser Runde eine unbedingte globale positive Budgetdominanz.

Die dritte Prognose ist eine registrierte Erwartung, keine Prämisse. Nichtgefundenes wird im Abschluss nicht als mathematische Widerlegung umgedeutet.

## 3. Im alten Fehlerbudget steckt bereits strikter Spielraum

**[ABSTRACT][PAPER — neue Folgerung aus den unveränderten Majoranten]**

Im Vorgänger wurden für die Ableitungsordnungen \(j=0,1,2\) die Schranken

\[
|F^{(j)}|,\ |J_N^{(j)}|\le D e^{-\vartheta T},
\quad D=4c^{-4},
\]

\[
|F^{(j)}-J_N^{(j)}|\le B e^{-\vartheta T},
\quad B=448c^{-1}M^3e^{-\pi cM^2}
\]

hergeleitet. Die Bedingung lautet \(\pi cM^2\ge1\). Daraus folgte

\[
|\mathscr H-h_N|\le16\sigma DB e^{-2\vartheta T}=\mathcal E_N.
\]

Wir ändern weder J_N noch die verlangte rechte Seite \(\mathcal E_N\). Für die logische Prüfung behalten wir lediglich zwei bereits ausgewertete Zwischenkonstanten bei.

Die Normmajorante des Vorgängers ist tatsächlich

\[
D_* = \frac{880625}{221841}c^{-4}<4c^{-4}.
\tag{3.1}
\]

Für die Schwanzmajorante wurde der Einzelbeitrag

\[
\frac{64\pi n^2+30}{c}e^{-\pi cn^2}
\]

zunächst durch \(256n^2c^{-1}e^{-\pi cn^2}\) ersetzt. Mit \(n\ge1\) und \(\pi<22/7\) gilt stattdessen

\[
64\pi n^2+30\le(64\cdot22/7+30)n^2
=\frac{1618}{7}n^2.
\]

Die gleiche bereits bewiesene Summenabschätzung des Vorgängers kostet \(7M^3/4\). Daher ist auch

\[
B_* = \frac{809}{2}c^{-1}M^3e^{-\pi cM^2}
\tag{3.2}
\]

zulässig. Es ist keine neue Eigenschaft der Theta-Nullstellen benutzt worden.

Die exakt gleiche gekoppelte Produktrechnung und die gleiche Integration von 0 bis sigma geben

\[
|\mathscr H-h_N|\le16\sigma D_*B_*e^{-2\vartheta T}.
\]

Der Quotient zur verlangten alten Fehlerhülle ist rational:

\[
\rho_*=
\frac{880625}{4\cdot221841}\frac{809}{896}
=\frac{712425625}{795078144}<\frac9{10}.
\]

Die Differenz ist exakt

\[
\frac9{10}-\rho_*=\frac{15723523}{3975390720}>0.
\]

Damit gilt, bei unveränderter Vergleichsgröße,

\[
\boxed{|\mathscr H-h_N|\le\frac9{10}\mathcal E_N.}
\tag{3.3}
\]

Diese Konstante ist hier **kein neuer Vorzeichenlieferant**. Sie zeigt, dass der verlangte Vergleich nicht nur mit einer möglicherweise scharfen Fehlerhülle am Rand zusammenfallen würde: Er würde einen echten positiven Puffer für die vollständige Quelle erzwingen.

## 4. Satz: Der gefrorene Vergleich erzwingt eine quantitative Rand-Schranke

**[ABSTRACT][PAPER — bewiesene Implikation, nicht bewiesene Prämisse]**

Definiere mit der plus-i-Konvention

\[
X(T)=F(iT)=\xi(1/2+iT)\in\mathbb R.
\]

Die volle Quelle ist gerade und reell. Daher stimmen die plus-i- und minus-i-Versionen von X überein. Ableitungen von X werden im Folgenden nach der reellen Variablen T genommen.

Es gilt

\[
F'(iT)=-iX'(T),\qquad F''(iT)=-X''(T).
\]

Weil \(\mathscr H=2\partial_\sigma|F|^2\), folgt direkt

\[
\left.\partial_\sigma\mathscr H(\sigma+iT)\right|_{\sigma=0}
=4\bigl(X'(T)^2-X(T)X''(T)\bigr).
\]

Schreibe

\[
\mathcal L_X(T)=X'(T)^2-X(T)X''(T).
\]

**Laguerre-Ausdruck** bezeichnet hier genau diese Kombination zweier Ableitungen, keine angenommene Laguerre–Pólya-Eigenschaft. Wegen der Reflexionssymmetrie ist H ungerade in sigma. Also

\[
\boxed{
\mathscr H(\sigma+iT)=4\sigma\mathcal L_X(T)+O_T(\sigma^3).
}
\tag{4.1}
\]

Nimm jetzt an, \((G_r)\) sei bewiesen. Dann liefern \((G_r)\) und (3.3)

\[
\mathscr H(\sigma+iT)\ge
h_N(\sigma+iT)-\frac9{10}\mathcal E_N
\ge\frac1{10}\sigma e_N(T).
\]

Bei festem T, vartheta und N dürfen wir durch sigma>0 teilen und zum Rand gehen. Es folgt

\[
\boxed{
\mathcal L_X(T)\ge\frac1{40}e_{N_r(T)}(T;\vartheta(T))>0
\qquad(T>\sqrt{20}).
}
\tag{4.2}
\]

Dies ist eine **notwendige Konsequenz** des verlangten festen Vergleichs. Die rechte Seite ist endlich, ausdrücklich definiert und strikt positiv.

### 4.1 Konsequenz an einer kritischen Nullstelle

Sei \(X(\gamma)=0\) mit \(\gamma>\sqrt{20}\). Dann macht (4.2) die Aussage

\[
\boxed{
|\xi'(1/2+i\gamma)|^2=X'(\gamma)^2
\ge\frac1{40}e_{N_r(\gamma)}(\gamma;\vartheta(\gamma))>0.
}
\tag{4.3}
\]

Eine **einfache Nullstelle** ist eine Nullstelle, an der die erste Ableitung nicht verschwindet. Folglich würde \((G_r)\) alle kritischen Nullstellen in seiner Höhenmenge als einfach zertifizieren. Es wäre darüber hinaus ein ausdrücklicher quantitativer Satz über ihre Ableitungsgrößen.

(4.3) ist **hier nicht bewiesen**: Bewiesen ist die Implikation \((G_r)\Rightarrow(4.3)\). Ein Beweis des festen Vergleichs muss diese Konsequenz tatsächlich tragen können. Sie darf nicht als bereits verfügbare Hintergrundannahme eingesetzt werden.

Die ursprüngliche HB-Nichtnegativität verlangt die Einfachheit der Randnullstellen nicht. Siehe den exakten Modellfall in Abschnitt 6.

## 5. Bedingter negativer oberer Rand an jeder hypothetischen mehrfachen kritischen Nullstelle

**[ABSTRACT][CONDITIONAL — Prämisse ausdrücklich nicht als Tatsache behauptet]**

Diese Aussage betrifft dieselbe echte Quelle und denselben endlichen Konturausdruck. Die konditionale Prämisse ist

\[
F(i\gamma)=F'(i\gamma)=0.
\tag{5.1}
\]

Eine solche Nullstelle wurde nicht gefunden und wird nicht behauptet.

Fixiere ein zulässiges N und vartheta bei T=gamma. Setze

\[
e=e_N(\gamma;\vartheta)>0,
\qquad A=4c^{-4}e^{-\vartheta\gamma}.
\]

Der Quellenbeweis des Vorgängers gibt \(|F''(u+i\gamma)|\le A\) für \(0\le u\le1/2\). Unter (5.1) liefert zweimalige Integration

\[
|F'(\sigma+i\gamma)|\le A\sigma,
\qquad |F(\sigma+i\gamma)|\le\frac A2\sigma^2.
\]

Daher

\[
|\mathscr H(\sigma+i\gamma)|\le2A^2\sigma^3.
\]

Zusammen mit (3.3) ergibt sich eine **obere** Hülle des verlangten Margins:

\[
h_N-\mathcal E_N
\le2A^2\sigma^3-\frac1{10}\sigma e.
\]

Für

\[
0<\sigma\le
\min\left\{\frac12,\sqrt{\frac{e}{40A^2}}\right\}
\]

ist sie strikt negativ:

\[
\boxed{
h_N(\sigma+i\gamma;\vartheta)-\mathcal E_N
\le-\frac1{20}\sigma e<0.
}
\tag{5.2}
\]

Das ist eine saubere bedingte Falsifikation der festen positiven Reserve, nicht das bloße Scheitern einer Unterhülle. Sie zeigt genau, welche bisher nicht ausgeschlossene Nullstellenkonfiguration die feste Schnittstelle nicht akzeptieren könnte.

**Keine mathematische Widerlegung der tatsächlichen Theta-Schnittstelle wird daraus abgeleitet**, weil (5.1) für die tatsächliche Quelle nicht etabliert wurde. Auch das HB-Vorzeichen könnte unter einer mehrfachen Randnullstelle im Inneren positiv bleiben.

## 6. Exakter Modelltest: Vollständige HB-Positivität braucht keine lineare Randreserve

**[ABSTRACT][PAPER — Gegenbeispiel nur zur generischen Schlussregel]**

Betrachte

\[
F_0(p)=\cosh^2p.
\]

Dies ist eine gerade, reelle ganze Funktion der Ordnung eins. Sie ist außerdem der bilaterale Laplace-Transform der positiven geraden atomaren Maßquelle

\[
\frac12\delta_0+\frac14\delta_2+\frac14\delta_{-2}.
\]

Sie ist **nicht** die Theta-Quelle; glatte strikte Positivität der Dichte und das modulare Gesetz werden nicht behauptet.

Alle ihre Nullstellen sind rein imaginär und doppelt. Eine exakte Rechnung liefert

\[
\boxed{
\mathscr H_0(\sigma+iT)
=2\sinh(2\sigma)\,[\cosh(2\sigma)+\cos(2T)]>0
\quad(\sigma>0).
}
\tag{6.1}
\]

Bei jeder Nullstellenhöhe \(T_0=(2k+1)\pi/2\), zum Beispiel \(T_0=3\pi/2>\sqrt{20}\), gilt

\[
\mathscr H_0(\sigma+iT_0)=8\sinh^3\sigma\cosh\sigma
=8\sigma^3+O(\sigma^5).
\]

Also kann für **kein** \(e_0>0\) gelten

\[
\mathscr H_0(\sigma+iT_0)\ge\sigma e_0
\quad\text{für alle hinreichend kleinen positiven sigma}.
\]

Auch eine explizite negative obere Hülle ist verfügbar. Für \(0<\sigma\le1\) sind \(\sinh\sigma\le2\sigma\) und \(\cosh\sigma\le2\). Damit

\[
\mathscr H_0-\sigma e_0\le128\sigma^3-\sigma e_0
\le-\frac12\sigma e_0<0
\]

sobald \(0<\sigma\le\min\{1,\sqrt{e_0/256}\}\).

Sogar der exakte Hilfsausdruck J=F_0 mit wirklichem Approximationsfehler null könnte eine vorgeschriebene positive lineare Sicherheitsreserve an diesen Höhen nicht bezahlen. Die Reserve kann eine erlaubte obere Fehlerabschätzung sein und trotzdem als zu starke Positivitätsschnittstelle scheitern.

**Genau widerlegte Schlussregel:** Nichtnegative oder strikt positive HB-Energie im offenen Halbraum impliziere eine positive lineare Randreserve bei jeder Höhe.

**Nicht widerlegt:** \((G_r)\) für die Theta-Quelle, Existenz einer anderen Konturwahl, Existenz einer sigma-abhängigen Abschneidung, SUPPORT oder das Vorzeichen von V.

## 7. Auch den freieren Quantor darf man nicht mit einem Beweis verwechseln

### 7.1 Sigma-abhängiger Cutoff

**[ABSTRACT][PAPER — exakte Schnittstellenäquivalenz, kein neuer Quellenzeichenbeweis]**

Fixiere einen inneren Punkt \(p=\sigma+iT\) mit sigma>0 und einen zulässigen Konturwinkel. Bei \(N\to\infty\) gilt

\[
\mathcal E_N(p)\to0,\qquad h_N(p)\to\mathscr H(p).
\]

Wenn \(\mathscr H(p)>0\), kann man N so groß wählen, dass \(\mathcal E_N<\mathscr H(p)/2\). Dann

\[
h_N\ge\mathscr H-\mathcal E_N>\mathcal E_N.
\]

Umgekehrt ergibt \(h_N\ge\mathcal E_N\) mit (3.3) die strikte Ungleichung \(\mathscr H(p)\ge\mathcal E_N/10>0\).

Daher ist auf dem offenen Gebiet die flexible Aussage

\[
\forall p\ \exists N(p):\quad h_{N(p)}(p)\ge\mathcal E_{N(p)}(p)
\]

äquivalent zur strikten vollständigen HB-Positivität dort. Das ist **kein Beweis dieser Positivität**. Es zeigt lediglich, dass die zusätzliche Einfachheitsforderung von der zusätzlichen Uniformität des sigma-unabhängigen Cutoffs stammt und nicht vom ursprünglichen offenen Halbebenenzeichen selbst.

Bei einer Randnullstelle der Ordnung m ist

\[
\mathscr H(\sigma+i\gamma)
=4m|a_m|^2\sigma^{2m-1}+O(\sigma^{2m+1}),
\qquad a_m=F^{(m)}(i\gamma)/m!.
\]

Die feste lineare Fehlerrate ist dort nicht angepasst. Ein Cutoff mit ungefähr \(M^2\) von der Größenordnung \(\log(1/\sigma)\), bei festem T und bekannten lokalen Daten, kann die Fehlergröße dagegen entsprechend schneller senken. Diese Bemerkung behauptet keine bekannten Vielfachheiten oder lokalen Konstanten der tatsächlichen Quelle.

### 7.2 Multiplikitätsverträgliche nichtstrikte Grenzzertifikate

Eine andere, schwächere **hinreichende** Schnittstelle erlaubt eine endliche negative Sicherheitszone:

\[
h_{N_j}(p)\ge-C_p\mathcal E_{N_j}(p),
\qquad N_j\to\infty,
\qquad C_p<\infty\ \text{unabhängig von j}.
\]

Dann folgt aus dem ursprünglichen Fehlerbeweis

\[
\mathscr H(p)\ge-(C_p+1)\mathcal E_{N_j}(p)\longrightarrow0.
\]

Also \(\mathscr H(p)\ge0\). Dies ist ein legitimer Grenzschluss, nicht ein positiver endlicher PASS. **Kein solches global quellengebundenes Zertifikat wurde hier geliefert.** Die Aussage ist nur eine schwächere Spezifikation, die mögliche mehrfache Randnullstellen nicht ausschließt.

## 8. Der direkte positive Kopfbeweis ist tatsächlich an einer unbezahlten Vorzeichenzeile gestoppt

**[ABSTRACT][PAPER für die Identität; CONDITIONAL für die verlangten Vorzeichen]**

Für feste N und vartheta setze \(j(y)=J_N(iy;\vartheta)\). Diese Funktion ist für reelles y reell. Ihre holomorphe Fortsetzung erfüllt

\[
J_N(\sigma+iT;\vartheta)=j(T-i\sigma).
\]

Die vollständige gemischte Entwicklung ist

\[
|J_N(\sigma+iT)|^2
=\sum_{n\ge0}\mathcal L_n[j](T)\sigma^{2n},
\]

\[
\mathcal L_n[j](T)=
\frac{(-1)^n}{(2n)!}
\sum_{k=0}^{2n}(-1)^k\binom{2n}{k}
 j^{(k)}(T)j^{(2n-k)}(T).
\]

Damit

\[
h_N(\sigma+iT)=4\sum_{n\ge1}
n\mathcal L_n[j](T)\sigma^{2n-1}.
\tag{8.1}
\]

Die ersten beiden gemischten Koeffizienten sind

\[
\mathcal L_1[j]=j'^2-jj'',
\]

\[
\mathcal L_2[j]=
\frac{jj^{(4)}-4j'j^{(3)}+3j''^2}{12}.
\]

Die Gleichungen wurden symbolisch kontrolliert. Es wurde **nicht** behauptet, jeder Koeffizient müsse für den ursprünglichen Verbraucher separat positiv sein. Diese Forderung wäre eine weitere stärkere Schnittstelle.

Der direkt versuchte Beweisschritt müsste aus den gekoppelten Gamma-Summen insbesondere

\[
4\mathcal L_1[j](T)\ge e_N(T)
\]

herleiten und die höheren gemischten Beiträge gemeinsam kontrollieren. Der Quellen- und Fehlerbeweis gibt nur Betragsmajoranten für diese Größen. Eine signierte Dominanz wird daraus nicht gewonnen.

Schon auf der Ebene beliebiger reeller Ableitungsdaten kann \(\mathcal L_1=1>0\) und zugleich \(\mathcal L_2=-1/12\) sein, etwa für

\[
j=1,\quad j'=0,\quad j''=-1,\quad j^{(3)}=0,\quad j^{(4)}=-4.
\]

Das ist kein Theta-Gegenbeispiel. Es zeigt, warum die neue Randformel nicht selbst die gesamte vertikale Vorzeichenfortpflanzung liefert.

**Es fehlt weiterhin eine tatsächlich aus der Theta-Quelle hergeleitete Vorzeichenabschätzung dieser gekoppelten Größen.** Die Feststellung dieser Lücke ist kein neuer Abschluss des globalen Beweisziels.

## 9. Routenentscheidung und zwei verbleibende Darstellungen

Das ursprüngliche Ziel \(\mathscr H\ge0\) bleibt unverändert. Der Literaturabgleich mit Lagarias (Einleitung, Gleichungen 1.4–1.5) bestätigt die klassische Verbindung von \(\Re(\xi'/\xi)>0\) und dem vollständigen Nullstellenkriterium. Die Rolle dieser Äquivalenz ist eine **Abhängigkeitskontrolle**, kein Grund, den Beweis für unmöglich zu erklären.

| Darstellung | Exakte Verpflichtung | Diagnosewirkung und Kosten |
|---|---|---|
| **R1: sigma-abhängige gekoppelte Gamma-Summe** | N darf von sigma und T abhängen; einen tatsächlichen quellengebundenen unteren Rand für \(h_N-\mathcal E_N\) herleiten. | Hohe Wirkung: bezahlt unmittelbar den unveränderten Verbraucher. Quantorprüfung hier erledigt; globale Beweiskosten unbekannt. Endliche Auswertung vergleichsweise günstig. |
| **R2: signierter Grenznachweis** | Eine Folge mit \(h_{N_j}\ge-C\mathcal E_{N_j}\), C unabhängig von j, für jeden benötigten Punkt beweisen. | Hohe Wirkung: vermeidet unnötige strikte endliche Reserve. Globaler Quellensatz offen; Ableitung des Verbrauchers billig, Quellenbeweiskosten unbekannt. |

Beide sind **unbewiesene Kandidaten**, keine aktivierten Lieferanten. Der Wechsel ihres Namens allein zählt als NO_PROGRESS. Es wurde kein großer Rechenlauf und keine Formalisierung autorisiert.

Der notwendige Diskriminator für ein konkretes N bleibt

\[
[L_N,U_N]=[h_N-\mathcal E_N,\ h_N+\mathcal E_N].
\]

Ein rigoroser unterer Rand \(L_N\ge0\) bezahlt nur sein zertifiziertes Gebiet. Ein negativer oberer Rand \(U_N<0\) wäre ein echter vollständiger Quellenzeuge. Ein negativer Wert von \(h_N-\mathcal E_N\) allein verwirft lediglich das entsprechende hinreichende Zertifikat.

Im Grenzansatz aus Abschnitt 7.2 stammt der PASS erst aus dem bewiesenen Grenzübergang zur exakten nichtnegativen Untergrenze, nicht aus einem negativen endlichen Rand.

## 10. Abhängigkeiten, Abschluss und keine vorweggenommene Auftragserfüllung

**DOWNSTREAM_CONSUMER:** Nichtnegativität der vollständigen ursprünglichen \(\mathscr H\); die getrennt beschriebenen SUPPORT-/V-Übergänge liegen dahinter.

**ACTUAL_CONSUMER_REQUIREMENT:** \(\mathscr H(\sigma+iT)\ge0\) für die vollständige Quelle auf allen benötigten inneren Punkten. Kein beliebiges anderes positiv gemachtes Objekt darf eingesetzt werden.

**ORIGINAL_REQUESTED_OBJECT:** Globaler Vergleich \((G_r)\) des konkret ausgeschriebenen Kopfes mit seinem bekannten Fehlerbudget.

**ORIGINAL_OBJECT_IS:** `UNKNOWN` hinsichtlich mathematischer Notwendigkeit für die feststehende xi-Funktion. Als allgemeine Verbraucherschnittstelle ist der fest vorgeschriebene sigma-unabhängige Puffer nicht notwendig: Er ist hinreichend, aber verlangt die zusätzliche quantitative Randreserve (4.2). Der Modellfall widerlegt die generische Notwendigkeit, nicht eine mögliche besondere Folgerung für xi. Eine flexible N-Wahl bzw. ein nichtstriktes Grenzzertifikat sind explizit schwächere mögliche Schnittstellen.

**FAILURE_TYPE / EPISTEMIC_STATUS für die Theta-Hauptaussage:** `NO_DERIVATION / RESEARCH_DEBT`. \((G_r)\) für die tatsächliche Quelle ist weder bewiesen noch widerlegt.

**Genau widerlegter generischer Satz:** HB-Positivität im offenen Halbraum impliziere einen überall verfügbaren positiven linearen Randboden. `KILL_SCOPE: THEOREM_SHAPE`. `KILL_EVIDENCE_KIND: EXACT_ANALYTIC_COUNTEREXAMPLE`. Gepinnte Beweisreferenz: Abschnitt 6 dieses neuen Artefakts und die daneben gespeicherten exakten Kontrollen. Keine Aussage über den Tod einer Route-Familie.

**REOPEN_TRIGGER:** Eine tatsächliche quellengebundene Vorzeichenabschätzung des Kopfes und aller gemischten Terme, entweder mit voller Konsequenz (4.3) für \((G_r)\), oder in einer explizit schwächeren multiplikitätsverträglichen Schnittstelle. Weitere Betragsverkleinerung ohne Vorzeichenlieferant ist kein Reopen-Trigger.

**NOVELTY_AXIS:** Explizite Randfolgen der bereits eingeführten Kontur-Fehlerhülle; keine historische Priorität beansprucht. Das eigentliche globale Zeichen wurde nicht verkleinert oder geschlossen.

**Was wurde kleiner?** Die Aussagekraft und die zusätzliche Belastung der konkret gewählten Schnittstelle sind exakt geklärt. Das ist ein Quantoren- und Abhängigkeitsaudit, kein neuer positiver Hochfrequenzbereich.

**Was wurde widerlegt?** Nur die generische Notwendigkeit eines positiven linearen Randpuffers; nicht der konkrete Theta-Vergleich.

**Was nicht wiederholt werden darf:** Aus der beliebigen Verkleinerbarkeit des Fehlerbudgets auf ein Kopfvorzeichen schließen; die Existenz mehrerer kritischer Nullstellen als bewiesene Tatsache ausgeben; einen festen T-Cutoff unbemerkt durch N(sigma,T) ersetzen; die Rand-Laguerre-Ungleichung allein als vollständigen inneren HB-Beweis verwenden.

**Vorhersagen:**

- P_MARGIN_BOUNDARY: **bestätigt**, mit der präzisen Konsequenz (4.2)–(4.3).
- P_MARGIN_GENERIC: **bestätigt** für die überprüfte generische Schlussregel; Modelltest Abschnitt 6. Keine Widerlegung der tatsächlichen Quelle.
- P_MARGIN_DIRECT: **unentschieden als mathematische Erwartung; Beweis in dieser Runde nicht geliefert**. Nichtgefundenes wird nicht als Refutation umetikettiert.

**Memory:**

```yaml
iteration:
  target: global_coupled_head_vs_frozen_error_budget
  status: OPEN
  cognitive_operator_used: BOUNDARY_CASE
  invariant_learned: nonnegative_HB_does_not_require_simple_boundary_zeros
  forbidden_future_move: silently_freeze_sigma_independent_margin_or_assume_simplicity
  next_decisive_test: source_sign_derivation_that_is_valid_near_arbitrary_boundary_multiplicity
  global_source_sign_closed: false
```

Es wurde kein Lean-Code geschrieben, kein Kernel gestartet, kein Repository verändert und keine Produktionspromotion vorgenommen. Der beigefügte Python-Test kontrolliert rationale Konstanten und symbolische Identitäten; er ist keine automatische Prüfung der analytischen Konturargumente.

## 11. Quellen und Reproduktion

Der lokale Vorgängerbericht ist der maßgebliche Input für J_N und sein unverändertes Budget. Die neue logische Randfolgerung ist hier bewiesen, nicht aus dem Vorgänger zitiert.

Extern abgeglichen:

- NIST DLMF 25.4: Definition und Reflexionsformel der xi-Funktion.
- NIST DLMF 8.2: obere unvollständige Gammafunktion und Zweigkonventionen.
- Jeffrey C. Lagarias, *On a Positivity Property of the Riemann xi-Function*, Einleitung, Gleichungen (1.4)–(1.5). Die relevante Seite wurde visuell aus dem autorengehosteten PDF gelesen. Dieser Literaturinput wird nicht als Lieferant des fehlenden Vorzeichenbeweises benutzt.

Die Adressen zur Reproduktion sind:

```text
https://dlmf.nist.gov/25.4
https://dlmf.nist.gov/8.2
https://websites.umich.edu/~lagarias/doc/positivity.pdf
```

Die einzige in dieser Runde ausgeführte mathematische Prüfdatei lautet

```bash
python /mnt/data/theta_margin_audit/check_margin_obstruction.py
```

Sie verwendet Python-Standardbibliothek und SymPy. `exact_checks.json` enthält ihre Ausgabe. Keine neue Bibliothek wurde installiert; keine nicht ausgeführte numerische oder Intervallprüfung wird behauptet.

**Endstatus:** Der von dir verlangte globale Beweis fehlt weiterhin. Die zusätzliche Einfachheitsforderung der bisherigen festen Schnittstelle ist nachgewiesen. Diese beiden Sätze dürfen nicht gegeneinander ausgetauscht werden.
