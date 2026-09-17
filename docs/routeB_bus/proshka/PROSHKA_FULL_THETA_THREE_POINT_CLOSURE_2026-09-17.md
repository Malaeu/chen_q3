# STATUS: TRY_FULL_THETA_SCHUR_AFTER_THREE_POINT_CLOSURE
```yaml
OPERATIVE_CLASS: TRY_FULL_THETA_SCHUR_AFTER_THREE_POINT_CLOSURE
PRIMARY: FULL_THETA_ALL_THREE_POINT_GRAM_PAPER_PROOF
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION_NOT_CODEX_BUS_ADJUDICATION
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_PROOF_WITH_EXACT_ALGEBRA_CHECKS_PENDING_INDEPENDENT_REVIEW

CLOSED_IN_THIS_PAPER:
  - FULL_SOURCE_CURVATURE_q_GT_11_AND_44q_MINUS_q_SECOND_GT_526_OVER_625
  - EQUALLY_SPACED_THREE_POINT_DELTA_POSITIVE_FOR_ALL_sigma_GT_0_h_GT_0
  - ALL_THREE_POINT_CONFIGURATIONS_FOR_ALL_sigma_GT_0
  - POSITIVE_DEFINITE_THREE_POINT_GRAM_FOR_DISTINCT_POSITIONS
  - EXACT_NONNEGATIVE_DECOMPOSITION_OF_THE_THREE_POINT_REST

STILL_OPEN:
  - FULL_THETA_FOUR_POINT_SCHUR_REST
  - ARBITRARY_SIZE_DENSE_GRAM_POSITIVITY
  - DIMENSION_INDEPENDENT_SOURCE_SCHUR_RECURSION
  - FULL_HB_SIGN
  - ORIGINAL_SUPPORT
  - ORIGINAL_V_SIGN

NO_PROMOTION:
  three_point_to_all_dimensions: true
  profile_matrix_to_full_HB: true
  positive_diagonal_to_PSD: true
  exact_symbolic_checks_to_LEAN: true

GENERIC_COUNTEREXAMPLE:
  rejected_implication: ALL_THREE_POINT_GRAM_PSD_IMPLIES_ALL_FINITE_GRAM_PSD
  KILL_SCOPE: THEOREM_SHAPE
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_IMPLICATION_ONLY
  fixed_kernel: exp(-w^2-w^4/8)
  fixed_four_points: [0, 1/4, 1/2, 3/4]
  upper_envelope_for_odd_block_determinant: LESS_THAN_MINUS_1_OVER_100000
  evidence_ref: SECTIONS_7_AND_10_OF_THIS_DOCUMENT
  is_original_theta_source: false
  original_V_negative_witness: false

DISCRIMINATOR:
  next_object: D4 = det(G3)-v_star_adj(G3)_v
  pass: SOURCE_DERIVED_LOWER_ENVELOPE_L_GE_ZERO_ON_STATED_DOMAIN
  negative_witness: SOURCE_DERIVED_UPPER_ENVELOPE_U_LT_ZERO_FOR_THE_FULL_KERNEL
  zero_consistent: INCONCLUSIVE_WITHOUT_EXACT_IDENTITY_OR_ONE_SIDED_BOUND

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

Ы. **Der angekündigte Dreipunkt-Test ist im folgenden Papierbeweis geschlossen.** Der Beweis deckt sogar beliebige, nicht nur gleiche Abstände ab. Die frühere Lücke im Taylorrest entfällt durch eine globale Vergleichsidentität. Zugleich wird ausdrücklich bewiesen, dass dieser Dreipunkt-Mechanismus allein keine Induktion über die Matrixgröße rechtfertigt.

**Verifikationsgrenze:** Die analytischen Argumente stehen vollständig unten. Exakte rationale und symbolische Kontrollen wurden ausgeführt. Eine unabhängige mathematische Abnahme und eine Lean-Kernelprüfung sind nicht erfolgt. „PAPER“ bedeutet hier nicht „LEAN“ und nicht „bereits unabhängig akzeptiert“.

## 1. Quelle, Lesebelege und unveränderter Gegenstand

**[ABSTRACT][PAPER]** Als vollständige lokale Vorarbeit wurde gelesen:

- `NEXT_STEP_FULL_THETA_GRAM_2026-09-17.md`, 22 771 Bytes, SHA-256 `10a98284ea1894d4aefc7699878e04f4fe44709dc64ec7c0ca406e646714f116`.
- Die relevanten Quellen- und Kernelabschnitte aus `THETA_HB_PAIR_SQUARE_AUDIT_2026-09-17.md`, 35 122 Bytes, SHA-256 `e22e7f92b55b301cfc38f17d1e8ace04dde56608848c7f43e18372e38cb15990`. Nicht sämtliche historischen Nebenbehauptungen dieses älteren Dokuments wurden neu abgenommen.

Über den GitHub-Connector wurden das aktuelle Projektprotokoll und die Zeilen 1–85 von `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` am Commit `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`, Blob `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`, gelesen. Der letztgenannte Pfad außerhalb des Bus-Baums wurde ausschließlich für die ausdrücklich benötigte Quellendefinition geöffnet. Die älteren terminalen Transportbehauptungen des gesamten Berichts werden hier nicht erneut unabhängig zertifiziert.

Ein begrenzter externer Abgleich verwendete nur die offiziellen DLMF-Identitäten 20.7.32 und 25.5.13–14 für die Theta-Normierung und Jacobi-Symmetrie. Die neue Krümmungsschranke und der Dreipunkt-Beweis unten werden nicht aus einer externen Arbeit importiert. Eine Prioritäts- oder Neuheitsbehauptung wird nicht erhoben.

Die vollständige Quelle lautet

\[
\Phi(t)=\sum_{n\ge1}\phi_n(t),\qquad
\phi_n(t)=\left(4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2}\right)e^{-\pi n^2e^{2t}}.
\tag{1}
\]

Mit \(\vartheta(x)=\sum_{n\ge1}e^{-\pi n^2x}\) ist

\[
r_\vartheta(x)=4x\vartheta''(x)+6\vartheta'(x),\qquad
\Phi(t)=e^{5t/2}r_\vartheta(e^{2t}).
\]

Aus

\[
1+2\vartheta(x)=x^{-1/2}(1+2\vartheta(1/x))
\]

folgen durch Differentiation \(r_\vartheta(1/x)=x^{5/2}r_\vartheta(x)\) und damit \(\Phi(-t)=\Phi(t)\). Auf \(t\ge0\) sind alle Summanden in (1) positiv. Also ist die vollständige Quelle auf der ganzen Geraden positiv. Die Reihen und ihre festen Ableitungen konvergieren lokal gleichmäßig. Auf der positiven Halbgeraden dominiert für jede feste Ableitungsordnung ein Vielfaches von \(\exp[-(\pi/2)e^{2t}]\). Geradheit liefert den entsprechenden Abfall links. Insbesondere sind die folgenden Integrale für jedes feste \(\sigma>0\) endlich.

Wir behalten

\[
F(p)=\xi(1/2+p)=\int_{\mathbb R}\Phi(t)e^{pt}\,dt,
\]
\[
K_\sigma(w)=\int_{\mathbb R}v\sinh(2\sigma v)
                  \Phi(v+w)\Phi(v-w)\,dv,
\quad \sigma>0,
\tag{2}
\]
\[
k_\sigma(w)=K_\sigma(w)/K_\sigma(0).
\tag{3}
\]

Insbesondere \(0<K_\sigma(0)<\infty\). Die Normierung ändert keinen Matrixsignaturtest.

Der HB-Verbraucher bleibt

\[
\mathscr H(\sigma+i\tau)=4\operatorname{Re}(F'(\sigma+i\tau)\overline{F(\sigma+i\tau)})
                         =8\widehat K_\sigma(2\tau).
\tag{4}
\]

Hier ist \(\widehat K(\omega)=\int K(w)e^{-i\omega w}\,dw\). Die Faktoren in (4) folgen durch Symmetrisierung des Produktintegrals und \(t=v+w, u=v-w\), mit Jacobi-Determinante 2. Eine Dreipunktmatrix ist nicht die ursprüngliche vollständige Form \(V\).

## 2. Das hier bewiesene Ergebnis

### Satz T3 — vollständige Dreipunktpositivität

**[ABSTRACT][PAPER]** Für jedes \(\sigma>0\), alle reellen \(x_1,x_2,x_3\) und alle \(c\in\mathbb C^3\) gilt

\[
\boxed{
\sum_{i,j=1}^3\overline{c_i}K_\sigma(x_i-x_j)c_j\ge0.
}
\tag{5}
\]

Sind die drei Positionen verschieden, dann ist die linke Seite für jedes \(c\ne0\) strikt positiv. Wiederholte Positionen werden durch Zusammenfassen ihrer Koeffizienten behandelt.

Insbesondere schließt dies den angekündigten Rest:

\[
\boxed{\Delta_\sigma(h):=1+k_\sigma(2h)-2k_\sigma(h)^2>0
\qquad(\sigma>0,\ h>0).}
\tag{6}
\]

Der Beweis verwendet weder RH noch die Positivität von \(\widehat K_\sigma\), weder einen unbekannten positiven Spektralfaktor noch ein absolutes inverses Spektralgefälle. Es werden keine endlichen Theta-Summen als Ersatzquelle in den Verbraucher eingesetzt.

## 3. Der neue Quellenlieferant: eine globale Krümmungsvergleichung

**[ABSTRACT][PAPER]** Bezeichne

\[
q(t)=-(\log\Phi(t))''.
\]

Dieses \(q\) ist die logarithmische Krümmung aus der unmittelbaren Vorarbeit, nicht die normierte Quellendichte, die in einem älteren Kausalitätsbericht ebenfalls mit \(q\) bezeichnet wurde.

Wir beweisen die stärkere, für den Rest passende Aussage

\[
\boxed{q(t)>11,\qquad 44q(t)-q''(t)>d,\quad d=\frac{526}{625}>0,
\qquad t\in\mathbb R.}
\tag{7}
\]

### 3.1 Vollständiger Rest, nicht abgeschnittene Quelle

Auf \(t\ge0\) setze \(x=\pi e^{2t}\ge\pi>31/10\). Exakt gilt

\[
\Phi(t)=\phi_1(t)(1+\varepsilon(t)),\qquad
\varepsilon(t)=\sum_{n\ge2}
 n^2\frac{2n^2x-3}{2x-3}e^{-(n^2-1)x}.
\tag{8}
\]

Alle Striche in diesem Abschnitt bezeichnen Ableitungen nach \(t\). Die in der Vorarbeit angegebenen globalen Restschranken werden durch die folgende Rekonstruktion kontrolliert:

\[
0\le\varepsilon<3/1000,\quad
|\varepsilon'|<3/50,\quad
|\varepsilon''|<1,\quad
|\varepsilon'''|<17,\quad
|\varepsilon''''|<267.
\tag{9}
\]

Setze \(m=n^2\), \(b=m-1\), \(D=2x\,d/dx\). Ein Restterm hat die exakte Form

\[
\rho_n(x)=m^2e^{-bx}+\frac32mb\int_0^\infty e^{3u/2}e^{-(b+u)x}\,du.
\tag{10}
\]

Für \(T_0(z)=1\), \(T_{j+1}(z)=z(T_j(z)-T_j'(z))\) gilt

\[
(-1)^jD^je^{-cx}=2^jT_j(cx)e^{-cx}.
\]

Die Polynome \(T_j(y+9)\), \(0\le j\le5\), haben ausschließlich positive Koeffizienten. Ihre Koeffizientenlisten in fallenden Potenzen sind

\[
(1),\ (1,9),\ (1,17,72),\ (1,24,190,495),
\]
\[
(1,30,331,1583,2745),\ (1,35,475,3090,9451,10458).
\]

In (10) ist \((b+u)x\ge9\) für \(x\ge3\). Daher wechseln die Ableitungen bis zur Ordnung fünf ihre Vorzeichen alternierend. Die Beträge bis zur Ordnung vier nehmen mit \(x\) ab. Es genügt, ihre Summe bei \(x_0=31/10\) zu majorisieren. Ableitung unter dem Integral ist durch die exponentielle Majorante in \(u\), summiertes Differenzieren durch die exponentielle Majorante in \(n^2\) gerechtfertigt.

Definiere die rationalen Polynome

\[
P_j(m)=\left.(-1)^jD^j\!\left[m\frac{2mx-3}{2x-3}e^{-(m-1)x}\right]
                                  e^{(m-1)x}\right|_{x=31/10}.
\]

Ihr Grad ist \(j+2\). Für \(P_j(m)=\sum p_{jk}m^k\) setze \(B_j=\sum|p_{jk}|9^k\). Dann liefert \(e^{31/10}>22\), zusammen mit

\[
(4/3)^{12}/22^7<1/2,
\]

die vollständige unendliche Restschranke

\[
\sum_{n\ge2}|D^j\rho_n(x)|
\le U_j:=P_j(4)/22^3+2B_j/22^8.
\tag{11}
\]

Für \(n\ge3\) verwendet man \(|P_j(n^2)|\le B_j(n^2/9)^{j+2}\); das Verhältnis aufeinanderfolgender Majoranten ist höchstens die oben angegebene Zahl. Die Exponentialuntergrenze folgt bereits aus einer endlichen positiven Taylorpartialsumme.

Die neu ausgeführten exakten rationalen Vergleiche lauten:

| j | Exakte rationale Obergrenze \(U_j\) | Strikt kleiner als |
|---:|---:|---:|
| 0 | \(561747211/219503494144\) | \(3/1000\) |
| 1 | \(41262609117/798194524160\) | \(3/50\) |
| 2 | \(169637795564979/175602795315200\) | \(1\) |
| 3 | \(116938822678968261/7024111812608000\) | \(17\) |
| 4 | \(18687820789150780161/70241118126080000\) | \(267\) |

Damit ist (9) bezahlt, einschließlich aller Theta-Restterme.

### 3.2 Logarithmischer Rest

Setze \(L=\log(1+\varepsilon)\). Aus (9) und \(1+\varepsilon\ge1\) folgt

\[
|L''|<1+(3/50)^2=\frac{2509}{2500},
\]
\[
|L''''|<267+4(3/50)17+3+12(3/50)^2+6(3/50)^4
       =\frac{856635243}{3125000}<275.
\tag{12}
\]

Für den ersten Term ist

\[
q_1=-(\log\phi_1)''=4x+\frac{24x}{(2x-3)^2}.
\]

Mit \(y=x-3\ge0\) lauten zwei entscheidende exakte Polynomidentitäten

\[
q_1-16=
\frac{16y^3+32y^2+12y+36}{(2x-3)^2}>0,
\tag{13}
\]
\[
24q_1-q_1''=
\frac{1280y^5+11520y^4+42240y^3+77184y^2+59184y+1296}{(2x-3)^4}>0.
\tag{14}
\]

In (14) bezeichnet \(q_1''\) weiterhin die zweite Ableitung nach \(t\), also \(D^2q_1\), nicht nach \(x\).

Weil \(q=q_1-L''\), erhalten wir

\[
q>16-\frac{2509}{2500}=\frac{37491}{2500}>11,
\]
\[
\begin{aligned}
44q-q''
&=44q_1-q_1''-44L''+L''''\\
&>20q_1-44\frac{2509}{2500}-275\\
&>320-44\frac{2509}{2500}-275
=\frac{526}{625}.
\end{aligned}
\tag{15}
\]

Geradheit der vollständigen \(\Phi\) macht \(q\) und \(q''\) gerade. Somit gilt (7) auf der gesamten reellen Achse. Die Beweiskette benutzt den ersten Term lediglich zur Abschätzung der vollständigen Quelle.

## 4. Globale Vergleichsidentität statt ungleichmäßigem Taylorrest

**[ABSTRACT][PAPER]** Setze \(\ell=-\log\Phi\). Für jeden reellen Mittelpunkt \(v\) definiere

\[
R_v(w)=\ell(v+w)+\ell(v-w)-2\ell(v),
\]
\[
C_v(w)=e^{-R_v(w)}=\frac{\Phi(v+w)\Phi(v-w)}{\Phi(v)^2}.
\tag{16}
\]

Für \(w\ge0\) ist \(R_v(0)=R_v'(0)=0\), und

\[
R_v'(w)=\int_{v-w}^{v+w}q(t)\,dt,
\]
\[
R_v''(w)=q(v+w)+q(v-w)>22,
\]
\[
R_v'''(w)=\int_{v-w}^{v+w}q''(t)\,dt.
\tag{17}
\]

Daraus folgen \(R_v(w)\ge11w^2\), \(R_v'(w)>0\) für \(w>0\), und mit (7)

\[
\boxed{2R_v'R_v''-R_v'''>2dw>0\quad(w>0).}
\tag{18}
\]

Tatsächlich ist \(R_v'''<44R_v'-2dw\), während \(2R_v'R_v''\ge44R_v'\).

Nun betrachten wir den ausdrücklich gekoppelten Ausdruck

\[
B_v(w)=R_v'(w)^2-R_v''(w)(1-e^{-2R_v(w)}).
\]

Die zentrale Identität ist

\[
\boxed{
B_v'(w)=(1-e^{-2R_v(w)})
                  (2R_v'(w)R_v''(w)-R_v'''(w)).
}
\tag{19}
\]

Sie wurde symbolisch unabhängig ausdifferenziert. Sie ist auch unmittelbar auf Papier nachprüfbar. Da \(B_v(0)=0\), liefert (18) sogar die explizite untere Schranke

\[
\boxed{
B_v(w)\ge d\left[w^2-\frac{1-e^{-22w^2}}{22}\right]>0
\qquad(w>0).
}
\tag{20}
\]

Hier wurde \(1-e^{-2R_v(w)}\ge1-e^{-22w^2}\) integriert. Die eckige Klammer ist positiv, weil \(1-e^{-z}<z\) für \(z>0\). Keine \(\sigma\)-abhängige Taylorfehlerkonstante tritt auf.

### 4.1 Die Winkelkoordinate

Definiere

\[
\alpha_v(w)=\arccos C_v(w)=\arccos(e^{-R_v(w)}),\quad w\ge0.
\]

Es gilt \(\alpha_v(0)=0\), \(0<\alpha_v(w)<\pi/2\) für \(w>0\), und

\[
\alpha_v'(w)=\frac{R_v'(w)}{\sqrt{e^{2R_v(w)}-1}}>0,
\]
\[
\boxed{
\alpha_v''(w)=-\frac{e^{2R_v(w)}B_v(w)}{(e^{2R_v(w)}-1)^{3/2}}<0.
}
\tag{21}
\]

Am Ursprung existiert die endliche rechtsseitige Ableitung
\(\alpha_v'(0+)=\sqrt{2q(v)}\). Das folgt aus \(R_v(w)=q(v)w^2+O(w^4)\) und ist nur die Behandlung des Randpunkts, nicht ein Restbeweis für endliche Abstände.

Damit ist \(\alpha_v\) streng wachsend und streng konkav auf der positiven Halbgeraden. Insbesondere gilt für \(a,b>0\)

\[
\boxed{
|\alpha_v(a)-\alpha_v(b)|<\alpha_v(a+b)
                              <\alpha_v(a)+\alpha_v(b).
}
\tag{22}
\]

Die linke Seite folgt aus strikter Monotonie. Die rechte Seite folgt etwa aus
\(\int_a^{a+b}\alpha_v'(u)du<\int_0^b\alpha_v'(u)du\). Alle Aussagen gelten für jedes \(v\) und jeden Abstand, ohne eine kleine Umgebung auswählen zu müssen.

## 5. Eine echte positive Zerlegung des angekündigten Restes

**[ABSTRACT][PAPER]** Für die vollständige Quelle ist

\[
d\mu_\sigma(v)=\frac{v\sinh(2\sigma v)\Phi(v)^2}{K_\sigma(0)}\,dv
\tag{23}
\]

ein Wahrscheinlichkeitsmaß. Daher

\[
\boxed{k_\sigma(w)=\mathbb E_{\mu_\sigma}C_v(w).}
\tag{24}
\]

Die Maßdefinition und sämtliche Produkte enthalten weiterhin die vollständige Quelle.

Für jeden Mittelpunkt \(v\) gilt wegen (22)

\[
\begin{aligned}
1+C_v(2h)-2C_v(h)^2
&=\cos\alpha_v(2h)-\cos(2\alpha_v(h))\\
&=2\sin\!\left(\alpha_v(h)+\frac{\alpha_v(2h)}2\right)
       \sin\!\left(\alpha_v(h)-\frac{\alpha_v(2h)}2\right)>0.
\end{aligned}
\tag{25}
\]

Beide Sinusfaktoren sind positiv: Der zweite Winkel liegt strikt zwischen 0 und \(\pi/2\), der erste strikt zwischen 0 und \(3\pi/4\).

Für den genauen angekündigten Verbraucher folgt die Identität

\[
\boxed{
\begin{aligned}
\Delta_\sigma(h)
={}&2\int_{\mathbb R}
\sin\!\left(\alpha_v(h)+\frac{\alpha_v(2h)}2\right)
\sin\!\left(\alpha_v(h)-\frac{\alpha_v(2h)}2\right)d\mu_\sigma(v)\\
&+2\int_{\mathbb R}(C_v(h)-k_\sigma(h))^2d\mu_\sigma(v)>0.
\end{aligned}}
\tag{26}
\]

Der zweite Term ist das Zweifache der **Varianz**, also einer mittleren quadratischen Abweichung. Der erste Term ist durch den unabhängig bewiesenen Winkelvergleich strikt positiv. Alle Integranden sind beschränkt und damit integrierbar.

Dies ist eine positive Zerlegung des Dreipunkt-Restes. Wer ausdrücklich Quadrate schreiben möchte, kann im ersten Integral den positiven Ausdruck unter eine Quadratwurzel stellen. Die Nichtnegativität dieser Wurzel wurde durch (7)–(25) bezahlt; sie wird nicht als neue Hypothese vorausgesetzt.

**Untere Hülle:** Das erste Integral in (26) allein ist eine strikt positive untere Hülle \(L_\sigma(h)\le\Delta_\sigma(h)\) für jeden \(\sigma>0,h>0\). Es wird keine uniforme positive Konstante über kollidierende Punkte behauptet. Insbesondere darf \(L_\sigma(h)\to0\) bei \(h\to0\).

**Wichtige Grenze:** (26) ist nicht eine positive Zerlegung von \(\mathscr H\) oder von \(V\). Sie zerlegt ausschließlich den ausdrücklich angegebenen Rest \(\Delta\).

## 6. Derselbe Mechanismus schließt auch ungleiche Dreipunktabstände

**[ABSTRACT][PAPER]** Nach Translation und Sortierung seien die Positionen \(0,a,a+b\) mit \(a,b>0\). Für festes \(v\) hat ihre normierte Profilmatrix die Gestalt

\[
G_v=\begin{pmatrix}
1&A&C\\A&1&B\\C&B&1
\end{pmatrix},
\quad A=C_v(a),\ B=C_v(b),\ C=C_v(a+b).
\tag{27}
\]

Schreibe \(\alpha=\alpha_v(a)\), \(\beta=\alpha_v(b)\), \(\gamma=\alpha_v(a+b)\). Dann

\[
\begin{aligned}
\det G_v
&=(1-A^2)(1-B^2)-(C-AB)^2\\
&=[\cos(\alpha-\beta)-\cos\gamma]
  [\cos\gamma-\cos(\alpha+\beta)]>0.
\end{aligned}
\tag{28}
\]

Die strikten Winkelungleichungen (22) rechtfertigen beide Faktoren. Dabei sind \(0<\gamma<\pi/2\), \(0<\alpha+\beta<\pi\); somit werden keine falschen Zweige der Kosinusmonotonie verwendet. Alle Zweipunkt-Hauptminoren sind positiv, da \(0<C_v(w)<1\) für \(w\ne0\). Also ist \(G_v\) positiv definit.

Die vollständige normierte Kernmatrix ist wegen (24)

\[
G_\sigma=\int G_v\,d\mu_\sigma(v).
\tag{29}
\]

Für jedes feste \(c\ne0\) ist \(c^*G_vc>0\) für alle \(v\). Sein Integral ist deshalb strikt positiv. Damit ist Satz T3 für verschiedene Punkte bewiesen. Bei gleichen Punkten werden die entsprechenden Koeffizienten zunächst addiert; die Aussage wird semidefinit und bleibt richtig.

### Vollständige Gebietskontrolle

- **\(h=0\):** \(\Delta_\sigma(0)=0\) exakt; die Gram-Matrix hat identische Zeilen. Kein künstlicher positiver Boden.
- **Negative Abstände:** durch Geradheit der Profile und des vollständigen Kerns erfasst.
- **Ungleiche Abstände:** durch (27)–(29) erfasst, ohne ein Verhältnis der Abstände vorauszusetzen.
- **Beliebig kleine oder große positive Abstände:** (19)–(22) sind global; kein Taylorintervall bleibt offen.
- **Beliebig großes oder kleines positives \(\sigma\):** Für jedes \(\sigma>0\) ist (23) ein positives Wahrscheinlichkeitsmaß. Eine uniforme Restschranke in \(\sigma\) wird nicht benötigt.
- **\(\sigma=0\):** Die normierte Formel (3) ist dort nicht definiert, weil der unnormierte Kern null ist. Dieser Punkt gehört nicht zum behaupteten Gebiet. Ein gesonderter Grenzkern wird nicht stillschweigend eingeführt.
- **Komplexe Koeffizienten:** Die reell symmetrischen positiven Matrizen sind auch als komplexe hermitesche Matrizen positiv.
- **Keine Größe \(N\to\infty\):** Der Satz betrifft genau alle Konfigurationen bis Größe drei, nicht alle Matrixgrößen.

## 7. Stärkster Gegencheck: eine Vierpunktfalle, die alle Dreipunktprüfungen besteht

**[ABSTRACT][PAPER]** Um den gefundenen Mechanismus nicht zur falschen Induktion aufzuwerten, prüfen wir den eigenständigen Modellkern

\[
j(w)=e^{-w^2-w^4/8}.
\tag{30}
\]

Dies ist ausdrücklich nicht der vollständige Theta-Kern.

### 7.0 Kontrollen des eigentlichen Dreipunkt-Detektors

Für den Gaußkern \(g(w)=e^{-aw^2}\), \(a>0\), gilt exakt

\[
1+g(2h)-2g(h)^2=(1-e^{-2ah^2})^2>0\quad(h>0).
\]

Dagegen hat der glatte positive gerade Kern \(b(w)=e^{-w^4}\) bei \(h^4=\log(4/3)\) den exakten negativen Dreipunktrest

\[
1+b(2h)-2b(h)^2=(3/4)^{16}-1/8=-493824191/4294967296<0.
\]

Die verwendete Winkelvergleichung akzeptiert somit nicht einfach jede positive glatte Funktion. Beim zuletzt genannten Kern ist \(2R'R''-R'''\) für kleine positive Argumente negativ. Keiner dieser beiden Kontrollen wird als Theta-Quelle ausgegeben.

### 7.1 Alle seine Dreipunktmatrizen sind positiv

Setze \(R(w)=w^2+w^4/8\). Dann

\[
2R'R''-R'''=\frac w2(3w^4+16w^2+10)>0\quad(w>0).
\]

Die Vergleichsidentität (19) und die Winkelrechnung (21)–(28) gelten daher auch für \(j\). Somit sind alle seine Dreipunktmatrizen für verschiedene reelle Positionen positiv definit.

Der Modellkern kann sogar als einzelnes normalisiertes Profil einer glatten positiven geraden Quelle auftreten, die die verwendeten groben Krümmungsschranken erfüllt: Für \(\Phi_0(t)=e^{-6t^2-9t^4}\) gilt \(q_0=12+108t^2\), \(44q_0-q_0''=312+4752t^2>d\), und das Profil bei Mittelpunkt null ist \(\Phi_0(w)^2/\Phi_0(0)^2=j(\sqrt{12}\,w)\). Dies widerlegt die Erweiterung des **profilweisen** Positivitätsarguments auf beliebige Matrixgrößen. Es wird nicht behauptet, dass die mit \(\Phi_0\) integrierte \(K_\sigma\)-Familie dadurch ebenfalls widerlegt ist.

### 7.2 Vier konkrete Punkte haben eine negative Richtung

**[FINITE_CELL][PAPER]** Wähle \(h=1/4\) und die Punkte \(0,h,2h,3h\). Setze

\[
A=j(h)=e^{-129/2048},\quad
B=j(2h)=e^{-33/128},\quad
C=j(3h)=e^{-1233/2048}.
\]

Auf den Vektoren \((a,b,-b,-a)\) ist die Form das Zweifache der Form der Matrix

\[
O=\begin{pmatrix}1-C&A-B\\A-B&1-A\end{pmatrix}.
\]

Ihr Determinantenrest lautet

\[
S_-=(1-C)(1-A)-(A-B)^2.
\tag{31}
\]

Ein exakter rationaler Exponentialvergleich ergibt

\[
\boxed{S_-< -1/100000<0.}
\tag{32}
\]

Zur vollständigen Reproduzierbarkeit: Für jedes der drei rationalen \(z\) oben setze

\[
L(z)=\sum_{r=0}^{35}\frac{(-z)^r}{r!},\qquad
U(z)=\sum_{r=0}^{36}\frac{(-z)^r}{r!}.
\]

Taylor mit Integralrest gibt \(L(z)<e^{-z}<U(z)\), und diese rationalen Werte erfüllen \(0<L<U<1\). Außerdem ist \(L(z_1)-U(z_2)>0\). Folglich ist

\[
S_-\le(1-L(z_3))(1-L(z_1))-[L(z_1)-U(z_2)]^2<-1/100000.
\]

Alle Vergleiche wurden mit exakten rationalen Zahlen geprüft. Der ungefähre Wert \(-0.00001555116585485847\) ist nur eine Orientierung, nicht die Begründung des Vorzeichens.

Ein expliziter negativer Vektor ist

\[
c=(1,-\eta,\eta,-1),\qquad \eta=(A-B)/(1-A).
\]

Für ihn ist \(c^*G_4c=2S_-/(1-A)<0\). Es wird kein numerisches Eigenwertargument gebraucht.

**Exakt widerlegt:** „Alle Dreipunktmatrizen sind positiv, also alle endlichen Matrizen.“ Ebenso widerlegt ist die naive Wiederverwendung der profilweisen Winkelkonkavität als Positivitätsbeweis für jede Matrixgröße.

**Nicht widerlegt:** Die Vierpunktpositivität der vollständigen Theta-Quelle, die Existenz eines stärkeren quellenabhängigen Beweises oder die ursprüngliche Form \(V\).

## 8. Was jetzt tatsächlich als nächster Schritt übrig bleibt

**[ABSTRACT][CONDITIONAL]** Aus Satz T3 wissen wir erstmals innerhalb dieses Beweises: Für drei verschiedene alte Positionen ist die vollständige Matrix \(G_3\) invertierbar und positiv. Daher ist für eine vierte Position der echte Schurtest wohldefiniert:

\[
s_4=1-v^*G_3^{-1}v,
\qquad v_i=k_\sigma(x_i-x_4).
\]

Um keine schlecht konditionierte Inverse als neuen Lieferanten einzuführen, lautet der bevorzugte gekoppelte Ausdruck

\[
\boxed{D_4=\det G_3-v^*\operatorname{adj}(G_3)v
             =\det G_4.}
\tag{33}
\]

Die **Adjunkte** ist die Matrix der algebraischen Kofaktoren in transponierter Anordnung. Da \(\det G_3>0\), sind \(D_4\ge0\) und \(s_4\ge0\) äquivalent. Es wird keine uniforme untere Eigenwertschranke des alten Blocks vorausgesetzt.

**Genau ein nächster lokaler Arbeitsauftrag:** Den Ausdruck (33) auf derselben vollständigen Quelle in einer gekoppelten Darstellung bearbeiten. Der erste minimale, falsifizierbare Unterfall besteht aus vier gleichmäßig verteilten Punkten. Er hat wegen der Umkehrsymmetrie zwei Zweipunktblöcke:

\[
S_{\sigma,-}(h)=(1-k_\sigma(3h))(1-k_\sigma(h))
                         -(k_\sigma(h)-k_\sigma(2h))^2,
\tag{34}
\]
\[
S_{\sigma,+}(h)=(1+k_\sigma(3h))(1+k_\sigma(h))
                         -(k_\sigma(h)+k_\sigma(2h))^2.
\tag{35}
\]

Der Gegencheck in §7 scheitert genau am Minusblock (34). Daher ist (34) der erste sinnvolle Diskriminator einer vorgeschlagenen allgemeinen Schurregel; (35) darf beim vollständigen Vierpunktergebnis nicht vergessen werden.

**Kein Matrixgrößen-Sammellauf:** Ein positiver Vierpunkt-Unterfall wäre wiederum nur ein notwendiger Teiltest. Weiterarbeit zu beliebigem \(N\) wird erst als allgemeiner Lieferant gewertet, wenn der Beweis einen von \(N\) unabhängigen Erhaltungsschritt liefert. Die heutige Winkelkonkavität ist nach §7 nicht dieser Schritt.

### Zwei Repräsentationen für den verbleibenden globalen Teil

| Darstellung | Präziser Einsatz | Qualitative Entscheidungskraft / Kosten |
|---|---|---|
| Vollständiger gekoppelter Schurrest (33), mit geteilten Differenzen bei Punktkollisionen | Primär: Quelle vor der Abschätzung einsetzen; alle gemischten Beiträge behalten; (34) als erster Gegencheck | 8/10 für den Vierpunkt-Test, 4/10 Anfangskosten; eine allgemeine Rekursion ist noch nicht gefunden |
| Positive Zunahme der vollständigen Autokorrelation \(\partial_\sigma A_\sigma=2K_\sigma\) | Reserve: explizite positive Ableitungsfaktoren aus der Quelle, nicht aus bereits angenommener Fourierpositivität | 10/10 bei einem globalen Beweis, geschätzte Kosten 8/10 |

Diese Zahlen sind Arbeitsbewertungen, keine zertifizierten Erfolgsaussichten. Keine der beiden offenen Darstellungen ist bereits eine allgemeine Lösung.

Ein negativer oberer Beleg für (34) an der **vollständigen** Quelle wäre ein wirklicher Gegenbeleg für ihre Kernelpositivität. Eine negative Untergrenze wäre nur eine unbrauchbare Abschätzung. Bei einer nullüberlappenden Einhüllung bleibt der Test unentschieden.

## 9. Einordnung in den globalen Verbraucher

**[ABSTRACT][CONDITIONAL]** Die globale Voraussetzung bleibt

\[
\forall\sigma>0\ \forall N\ \forall x_1,\ldots,x_N\in\mathbb R:
[k_\sigma(x_i-x_j)]_{i,j=1}^N\succeq0.
\tag{36}
\]

Für den glatten integrierbaren Kern ist dies äquivalent zu \(\widehat K_\sigma\ge0\). Eine direkte Richtung benutzt positive Riemannsummen, anschließend den Test \(e^{i\omega x}\mathbf1_{[-T,T]}(x)\), Division durch \(2T\) und dominierte Konvergenz. Fourierinversion liefert die umgekehrte Richtung. Diese bekannten Fourier-Schritte verlangen alle Größen \(N\); Satz T3 allein reicht nicht.

Erst (36) liefert über (4) den vollständigen HB-Zeichenbeweis. Aus \(\mathscr H=2\partial_\sigma|F|^2\ge0\) würde ein Nullpunkt mit \(\sigma>0\) einen waagerechten Abschnitt von Nullpunkten erzwingen und damit \(F\equiv0\). Das ist die unveränderte bedingte Schlussrichtung, nicht eine Behauptung, (36) sei hier bewiesen.

**Was präzise kleiner geworden ist:** Negative Richtungen, die nur bis zu drei beliebige Positionen des vollständigen Kerns verwenden, sind durch den vorgelegten Papierbeweis ausgeschlossen. Ein hypothetischer endlicher negativer Kernelzeuge benötigt mindestens vier verschiedene Positionen. Das ist ein Ergebnis über diese Kerneltests, keine Behauptung über die Mindestzahl von Atomen eines bereits identifizierten \(V\)-Zeugen.

## 10. Prüfprotokoll, vorherige Vorhersagen und Grenzen der Verifikation

**[ABSTRACT][PAPER]** Vor der Prüfung der neuen Schranke wurden drei informierte, nicht verblindete Forschungsvorhersagen fixiert:

| Vorhersage | Vorab-Wert | Ergebnis |
|---|---:|---|
| P3A: Die vollständige Quelle erfüllt \(q''\le44q\) bei \(q>11\) | 0.72 | Bestätigt durch (7)–(15), sogar mit positiver Differenz \(526/625\) |
| P3B: Diese Schranken liefern einen globalen Dreipunkt-Beweis über Winkelkonkavität und positive Mischungen | 0.78 | Bestätigt durch (16)–(29), auch für ungleiche Abstände |
| P3C: Die niedrigen Krümmungsschranken allein werden nicht alle Matrixgrößen liefern | 0.90 | Präzise erledigt für die profilweise Winkelmethode und den generischen Dreipunkt-zu-allen-Größen-Schluss durch §7; keine Unmöglichkeit für die besondere vollständige Theta-Mischung bewiesen |

Die Registrierungsdatei hatte SHA-256 `8abc81587502b2826a8d5bb93b4c5d62890edac498365f278a4dfe0b808f26ab`. Die Wahl der Vergleichsschranke war bereits durch analytische Exploration motiviert. Die Vorhersagen sind keine empirische Kalibrierungsstudie.

Die frühere breite Vorhersage `P_EULER_HB_3` über einen vollständigen positiven Theta-Quadratlieferanten bleibt **UNRESOLVED**. (26) bestätigt nur den niedrigdimensionalen Rest, nicht den vollständigen HB-Defekt.

### Exakte Kontrollen

Ein eigenständiger lokaler SymPy-Check rekonstruierte:

- die Theta-Restpolynome und alle rationalen Vergleiche in (9)–(12);
- die beiden positiven Polynome (13)–(14) und den Endboden (15);
- die Ableitungsidentität (19), die Winkelableitung (21) und die Determinantenidentität (28);
- die positive Vergleichspolynomform des generischen Modells;
- die negative rationale obere Einhüllung in (32).

Endausgabe: `all_exact_checks: PASS`.

**Transparenter Fehlerbeleg aus der Hilfsprüfung:** Der erste Lauf stoppte an einem falsch erwarteten Koeffizienten der Modell-Vierpunktentwicklung. Richtig ist

\[
S_-(h)=-\frac{21}{4}h^8+\frac{165}{2}h^{10}+O(h^{12}),
\]

nicht der zunächst im Hilfscheck vermutete Koeffizient \(-21h^8\). Auch das Modell-Vergleichspolynom wurde durch direkte Differentiation auf die in §7 angegebene Form korrigiert. Der zunächst versuchte stärkere numerische Betrag \(1/10000\) ist am gewählten Punkt nicht richtig; die anschließend exakt bewiesene Aussage lautet \(S_-<-1/100000\). Diese Hilfskonstanten waren nicht die registrierte Theta-Hypothese. Keine Theta-Voraussetzung, kein Punktbereich und keine Vorhersage wurden nachträglich verändert, um den Hauptbeweis passend zu machen.

Der finale Check besitzt SHA-256 `5dedbc3b0ed80681747b7d1e2f5a7269e79ec9974e1b5b32da9f6568b419c49b`. Er ist im folgenden Anhang vollständig wiedergegeben. Symbolische Kontrolle ersetzt nicht die unabhängige Prüfung von Integrabilität, Ableitungswechseln und den analytischen Vergleichsschritten.

## 11. Dependency epistemics und Abschluss

```yaml
DOWNSTREAM_CONSUMER: ZERO_EXCLUSION_FOR_ORIGINAL_F_IN_RE_P_POSITIVE
ACTUAL_CONSUMER_REQUIREMENT: FULL_H_NONNEGATIVE_OR_ANOTHER_INDEPENDENT_ZERO_EXCLUSION_PROOF
ORIGINAL_REQUESTED_OBJECT: EQUALLY_SPACED_FULL_THETA_THREE_POINT_REST_FOR_ALL_sigma_h
ORIGINAL_OBJECT_IS: PROVED_NECESSARY_FOR_THE_SELECTED_ALL_GRAM_POSITIVITY_INTERFACE
ORIGINAL_OBJECT_SUFFICIENT_FOR_RH: false
PROVED_STRONGER_LOCAL_RESULT: ALL_THREE_POINT_CONFIGURATIONS
KNOWN_GLOBAL_SUFFICIENT_INTERFACES:
  - ALL_FINITE_FULL_KSIGMA_GRAM_MATRICES_PSD_WITH_ALL_QUANTIFIERS
  - FULL_H_NONNEGATIVE_WITHOUT_EXPLICIT_FACTORS
  - POSITIVE_KERNEL_INCREASE_OF_THE_FULL_AUTOCORRELATION
LOCAL_FAILURE_TYPE: NONE_IN_THE_PRESENTED_THREE_POINT_PAPER_PROOF
GLOBAL_FAILURE_TYPE: NO_DERIVATION
GLOBAL_EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: FULL_SOURCE_FOUR_POINT_OR_DIMENSION_INDEPENDENT_SCHUR_IDENTITY_WITH_SIGN_CONTROL
NOVELTY_AXIS: FULL_SOURCE_CURVATURE_COMPARISON_TO_GLOBAL_THREE_POINT_ANGLE_AND_VARIANCE_DECOMPOSITION
NOVELTY_ASSERTED: false
KILL_SCOPE: THEOREM_SHAPE_ONLY_FOR_GENERIC_THREE_POINT_TO_ALL_DIMENSIONS
KILL_EVIDENCE_KIND: EXACT_ANALYTIC_PLANT_AND_RATIONAL_NEGATIVE_UPPER_ENVELOPE
KILL_EVIDENCE: SECTION_7_KERNEL_j_AND_FIXED_POINTS_0_1_4_1_2_3_4
THETA_ROUTE_MATHEMATICALLY_DEAD: false
SOURCE_INDEPENDENT_REVIEW_PENDING: true
```

**Geschlossen:** Der angekündigte kleine endliche Abstand, die fehlende uniforme Taylorrestbehandlung und darüber hinaus alle ungleichen Dreipunktabstände. Die neue Vergleichsidentität erreicht dasselbe Ziel global, ohne den stärkeren und unnötigen Anspruch \(\Delta^{(4)}\ge0\) zu verwenden.

**Widerlegt:** Ausschließlich der generische Schluss von allen Dreipunktprüfungen auf alle Matrixgrößen sowie seine profilweise Wiederholung. Die vollständige Theta-Quelle bleibt davon getrennt.

**Nicht wiederholen:** Einzelne Theta-Summanden als Ersatzquelle; positive wenige Matrizen als globales Gesetz; eine negative Untergrenze als negativen Zeugen; eine Inverse mit nicht bewiesenem uniformem Spektralboden; eine neue Bezeichnung für einen unbekannten Faktor als Fortschritt.

**Nächster kleinster Rest:** (33), mit (34) als erstem gezielten Diskriminator einer vorgeschlagenen quellenabhängigen Erhaltungsregel. Ein allgemeiner Schur-Erhaltungsschritt ist nicht gefunden.

**Lieferstatus:** Genau dieses Markdown ist der Ergebnisbericht. Kein Repository wurde geändert, kein Codex-Auftrag abgesandt, kein Lean-Quelltext geschrieben und kein Produktionsstatus erhöht. Damit gibt es weder einen neuen Commit noch einen angeblich grünen Kernelbeleg.

### Externe Referenzen für die klassische Quellenbasis

1. NIST Digital Library of Mathematical Functions, §20.7, Gleichung 20.7.32: Jacobi-Transformation. https://dlmf.nist.gov/20.7#E32
2. NIST Digital Library of Mathematical Functions, §25.5, Gleichungen 25.5.13–14: Theta-Integral und verwendete Reihen-Normierung. https://dlmf.nist.gov/25.5#E13
3. Gepinnter Projektbericht: `Malaeu/chen_q3`, `ae905d0b8e290f500303f8f141e8ba4cc5e0a238`, `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, §§1–2. Seine Definition wird verwendet; sein gesamter terminaler Audit wird hier nicht erneut akzeptiert.

## Anhang: vollständiger reproduzierbarer algebraischer Check

Der Check benutzt Python und SymPy. Er prüft exakte rationale und symbolische Identitäten. Er prüft nicht den gesamten analytischen Beweis mit einem Beweiskern. Es gibt keine vom Benutzer auszufüllenden Platzhalter.

```python
"""Exact algebra checks for the full-theta three-point paper proof.
These checks do not replace analytic convergence and inequality arguments.
Run: python check_exact.py
"""
import json
from pathlib import Path
import sympy as s
x,y,z,m,h=s.symbols('x y z m h')
D=lambda f:2*x*s.diff(f,x)
x0=s.Rational(31,10)
# Exponential lower bounds and the tail comparison.
assert sum(x0**k/s.factorial(k) for k in range(15)) > 22
assert (s.Rational(4,3))**12/s.Integer(22)**7 < s.Rational(1,2)
T=s.Integer(1)
shifted=[]
for j in range(6):
    coeff=s.Poly(s.expand(T.subs(z,y+9)),y).all_coeffs()
    assert all(c>0 for c in coeff)
    shifted.append([str(c) for c in coeff])
    T=s.expand(z*(T-s.diff(T,z)))
# Derivatives after removing exp(-(m-1)*x); independent recurrence.
B=m*(2*m*x-3)/(2*x-3)
limits=[s.Rational(3,1000),s.Rational(3,50),1,17,267]
tail=[]
P=[]
for j,lim in enumerate(limits):
    pol=s.Poly(s.factor((-1)**j*B.subs(x,x0)),m)
    P.append(str(s.factor(pol.as_expr())))
    coeff_sum=sum(abs(co)*9**pow[0] for pow,co in pol.terms())
    U=s.factor(pol.eval(4)/s.Integer(22)**3+2*coeff_sum/s.Integer(22)**8)
    assert U < lim
    tail.append({'j':j,'U_exact':str(U),'U_approx':float(U),'bound':str(lim)})
    B=s.factor(2*x*(s.diff(B,x)-(m-1)*B))
# Logarithmic-rest derivative bounds.
E1=s.Rational(3,50)
L2=1+E1**2
L4=267+4*E1*17+3+12*E1**2+6*E1**4
assert L2==s.Rational(2509,2500)
assert L4==s.Rational(856635243,3125000)
assert L4 < 275
q1=4*x+24*x/(2*x-3)**2
q1pp=s.factor(D(D(q1)))
curv={}
for name,f in [('q1_minus_16',q1-16),('24q1_minus_q1pp',24*q1-q1pp)]:
    n,d=s.fraction(s.factor(f))
    pp=s.Poly(s.expand(n.subs(x,y+3)),y)
    assert all(co>0 for co in pp.all_coeffs())
    curv[name]={'shifted_numerator':str(pp.as_expr()),'denominator':str(d)}
margin=s.Rational(320)-44*L2-275
assert margin==s.Rational(526,625)>0
assert 16-L2 >11
# Independent identities for the comparison and Gram determinant.
r=s.Function('r')(h)
Bcmp=s.diff(r,h)**2-s.diff(r,h,2)*(1-s.exp(-2*r))
expected=(1-s.exp(-2*r))*(2*s.diff(r,h)*s.diff(r,h,2)-s.diff(r,h,3))
assert s.simplify(s.diff(Bcmp,h)-expected)==0
ang=s.acos(s.exp(-r))
expected2=-s.exp(2*r)*Bcmp/(s.exp(2*r)-1)**s.Rational(3,2)
# Use positive formal a=exp(r)>1 to avoid symbolic branch ambiguities.
a, rp, rpp=s.symbols('a rp rpp',positive=True)
expr=rpp/s.sqrt(a*a-1)-a*a*rp*rp/(a*a-1)**s.Rational(3,2)
expr2=-a*a*(rp*rp-rpp*(1-1/(a*a)))/(a*a-1)**s.Rational(3,2)
assert s.simplify(expr-expr2)==0
A,Bb,C=s.symbols('A B C')
G=s.Matrix([[1,A,C],[A,1,Bb],[C,Bb,1]])
assert s.expand(G.det()-((1-A*A)*(1-Bb*Bb)-(C-A*Bb)**2))==0
# Main three-point detector controls: Gaussian passes, exp(-w^4) fails.
z0=s.symbols('z0')
assert s.expand(1+z0**4-2*z0**2-(1-z0**2)**2)==0
assert s.Rational(3,4)**16-s.Rational(1,8)==-s.Rational(493824191,4294967296)
# Generic plant: all-three-point-positive does not propagate to order four.
k=lambda t:s.exp(-t*t-t**4/s.Integer(8))
kser=lambda n:s.series(k(n*h),h,0,11).removeO()
odddet=s.series((1-kser(3))*(1-kser(1))-(kser(1)-kser(2))**2,h,0,11)
assert s.expand(odddet.removeO()).coeff(h,8)==-s.Rational(21,4)
u=s.symbols('u',positive=True)
r0=u*u+u**4/s.Integer(8)
Tplant=s.factor(2*s.diff(r0,u)*s.diff(r0,u,2)-s.diff(r0,u,3))
assert Tplant==u*(3*u**4+16*u**2+10)/s.Integer(2)
# Exact rational exponential bounds at h=1/4 for the negative odd block.
# For z >= 0, odd/even Taylor partials of exp(-z) bracket its value.
def exp_bounds(z, pairs=18):
    low=sum((-z)**j/s.factorial(j) for j in range(2*pairs))
    high=low+z**(2*pairs)/s.factorial(2*pairs)
    assert low>0 and high<1
    return low,high
bounds=[exp_bounds((s.Rational(n,4))**2+(s.Rational(n,4))**4/s.Integer(8)) for n in [1,2,3]]
l1,u1=bounds[0];l2,u2=bounds[1];l3,u3=bounds[2]
assert l1-u2>0
upper=s.factor((1-l3)*(1-l1)-(l1-u2)**2)
assert upper<0
assert upper < -s.Rational(1,100000)
report={'all_exact_checks':'PASS','scope':'rational_and_symbolic_checks_not_analytic_kernel_verification',
        'T_shifted_coefficients':shifted,'tail_polynomials':P,'tail_bounds':tail,
        'log_rest_second':str(L2),'log_rest_fourth':str(L4),'curvature_polynomials':curv,
        'curvature_margin':str(margin),'plant_small_h_odd_det':str(odddet),
        'plant_comparison_polynomial':str(Tplant),'plant_h':'1/4',
        'plant_odd_det_upper_approx':float(upper),'plant_upper_lt':'-1/100000'}
Path(__file__).with_name('checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

```
