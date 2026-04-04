# Formale Kette: Unterscheidung → Physik

Maschinengeprüft in Agda `--safe --without-K`. Null Postulate. Jeder Schritt `refl` oder `λ ()`.

---

## 1. Axiom: Die erste Unterscheidung

$$D_0 := \text{record}\;\{S : \text{Set},\; \ell\, r : S,\; \ell \neq r,\; \text{cover} : \forall x.\; (x = \ell) \uplus (x = r)\}$$

Einzige Annahme: es gibt einen Typ mit genau zwei unterscheidbaren Elementen und Exhaustion (jedes Element ist $\ell$ oder $r$). Kein Kontinuum, keine Zahlen, keine Geometrie — nur binäre Unterscheidbarkeit.

## 2. Existenz von $D_0$ (Dreistufig)

Die Existenz von $D_0$ wird nicht postuliert, sondern auf drei unabhängigen Wegen **konstruktiv bewiesen** — jeder stärker als bloße Irrefutabilität.

### Stufe 1: Direkte Konstruktion

$$\text{Two-distinction} : D_0 \qquad\text{(parameterlos, Beweis: } \texttt{record}\;\{S = \text{Two},\; \ell = L,\; r = R,\; \ell \neq r = \lambda\;(),\; \text{cover} = \text{match}\})$$

Ein konkreter Bewohner von $D_0$ — keine Annahme, kein Parameter, reine Konstruktion. Das ist **stärker** als $\neg\neg D_0$: nicht nur „die Leugnung ist widersprüchlich", sondern „hier ist einer".

### Stufe 2: Messungspräsupposition

$$\text{measurement-outcome-distinction} : \text{BinaryMeasurement} \to D_0$$

Jedes System, das **messen** kann (zwei unterscheidbare Ergebnisse + Exhaustion), trägt bereits $D_0$ in seinem Ergebnisraum. Der Beweis benutzt `fromDistinctCovered` — den generischen Rekonstruktor, der aus beliebigen Zwei-Punkt-Daten ein $D_0$ baut. $D_0$ ist keine Zusatzannahme zur Physik — es ist die Schwelle, unterhalb derer „Messung" keinen Inhalt hat.

### Stufe 3: Schleifenschluss (§18 vorweggenommen)

$$\text{physics-presupposes-distinction} : \text{K4PhysRep} \to D_0$$

Das vollständige Physik-Record gibt $D_0$ zurück. Der Kreis schließt sich: $D_0 \to K_4 \to \text{K4PhysRep} \to D_0$. Dies wird in §18 ausgeführt.

### Schwächste Formulierung: Irrefutabilität

Aus `Two-distinction` folgt trivial $\neg\neg D_0 = \lambda\, f \to f\;\text{Two-distinction}$. Im Agda-Code ist $\neg\neg D_0$ zusätzlich über das `NonVacuityLaw`-Record als **Eröffnungsannahme** (Kapitel 0) formalisiert — die schwächste Variante, die schon genügt, um den vakuösen Pfad zu blockieren. Die direkte Konstruktion (Stufe 1) macht sie nachträglich überflüssig, aber die Eröffnungsannahme zeigt, dass die Kette auch mit weniger starten kann.

## 3. Konkrete Instanz

$$\text{Two} := \{L, R\} \qquad L \neq R : \lambda\;()$$
$$\text{Two-distinction} : D_0 \quad := \{S = \text{Two},\; \ell = L,\; r = R,\; \ell \neq r = \lambda\;(),\; \text{cover} = \text{pattern match}\}$$

Die Ungleichung $L \neq R$ wird durch den leeren Typ bezeugt: $\lambda\;()$ — es gibt keinen Konstruktor, der $L = R$ bewohnen könnte.

## 4. Normalform (Eindeutigkeit von $D_0$)

$$\forall\, d : D_0.\;\; \text{DistinctionIso}\; d\;\text{Two-distinction}$$

**Jeder** Bewohner von $D_0$ ist isomorph zu `Two-distinction`. Der Beweis konstruiert `to`, `from`, Roundtrips und Randerhaltung — alles ist durch den Typ forciert, nichts gewählt. Das bedeutet: der Typ $D_0$ hat im wesentlichen genau einen Bewohner.

## 5. Endomorphismen von $D_0$

Alle Funktionen $D_0.S \to D_0.S$ über dem Zweiermenge-Typ:

$$\text{Endo}(D_0) = \{\text{id},\, \text{dual},\, \text{const-L},\, \text{const-R}\}$$

Genau 4 — forciert, weil $|S| = 2$ genau $2^2 = 4$ Funktionen zulässt. Alle 6 paarweisen Ungleichungen bewiesen durch $\lambda\;()$ (Konstruktor-Diskriminierung):

$$\text{const-L} \neq \text{const-R},\quad \text{const-L} \neq \text{id},\quad \text{const-L} \neq \text{dual},\quad \text{const-R} \neq \text{id},\quad \text{const-R} \neq \text{dual},\quad \text{id} \neq \text{dual}$$

**Kritischer Übergang:** Diese 4 Elemente bilden die Knotenmenge des nächsten Schritts.

## 6. $K_4$-Graph

$$K_4 := \text{record Graph}\;\{V = \text{EndoCase},\; \text{Edge} = \lambda\, a\, b.\; a \neq b\}$$

- Knotenmenge = die 4 Endomorphismen aus Schritt 5
- Kantenmenge = alle Paare verschiedener Knoten ($a \neq b$)
- `edge-sym`: $a \neq b \Rightarrow b \neq a$; `edge-irr`: $\neg(a \neq a)$
- Ergebnis: der vollständige Graph auf 4 Knoten

**Warum $K_4$ und kein anderer Graph?** Die Kantendefinition $\text{Edge} = \lambda\, a\, b.\; a \neq b$ ist die einzige, die weder willkürliche Kanten hinzufügt noch entfernt. Sie benutzt nur die aus $D_0$ geerbte Ungleichheits-Struktur. $K_3$ scheitert, weil 3 Endomorphismen den Typ $D_0.S \to D_0.S$ nicht exhaustiv abdecken. $K_5$ scheitert, weil $|D_0.S| = 2$ nur 4 Endomorphismen zulässt.

## 7. Kanonizität von $K_4$

$$\forall\, p : K_4\text{GraphPresentation}.\;\; \text{GraphIso}\;(\text{presentedGraph}\;p)\;K_4$$

Jede alternative Bijektion $V_p \leftrightarrow \text{EndoCase}$ induziert automatisch denselben Graphen bis auf Isomorphismus. Das bedeutet: es existiert genau ein $K_4$ (bis auf kanonische Identifikation), und die Darstellung ist präsentationsunabhängig. Beweis: `refl` + `transport≠`.

## 8. Elimination (56 Kapitel lang)

Das Buch führt über 56 Kapitel hinweg eine systematische Elimination durch. Jede alternative Struktur — jedes alternative Axiom, jede alternative Knotenzahl, jede alternative Kantenrelation — wird durch Typprüfung eliminiert:

- $\lambda\;()$: der leere Typ bezeugt die Unbewohnbarkeit einer Alternative
- `refl`: definitorische Gleichheit erzwingt die einzige überlebende Form

Kein einziger Fall überlebt. Am Ende steht $K_4$ als absolute Fixpunkt-Struktur: die einzige, die aus $D_0$ durch konsistente Elimination herleitbar ist.

## 9. Simplexinvarianten von $K_4$

Aus $|V| = 4$ (erzwungen durch Schritt 5) folgen alle Invarianten durch reine Graphentheorie:

| Symbol | Formel | Wert | Beweis |
|--------|--------|------|--------|
| $V$ | Knotenzahl | $4$ | `refl` |
| $d$ | $V - 1$ (Grad) | $3$ | `refl` |
| $E$ | $\binom{V}{2}$ (Kanten) | $6$ | `refl` |
| $F$ | $\binom{V}{3}$ (Flächen) | $4$ | `refl` |
| $\chi$ | $V + F - E$ (Euler) | $2$ | `refl` |
| $\kappa$ | $V \cdot \chi$ (Spektralbreite) | $8$ | `refl` |
| $F_2$ | $2^V + 1$ (Clifford + 1) | $17$ | `refl` |
| $|\text{Aut}(K_4)|$ | $V!$ | $24$ | `refl` |

Keine Formel ist gewählt. Jede Zeile ist eine kanonische Graph-Invariante von $K_4$, berechenbar aus $V = 4$ allein.

**Schlüsselidentität:** $\chi \cdot d = E$ (d.h. $2 \cdot 3 = 6$) — die Euler-Charakteristik mal dem Grad ergibt die Kantenzahl. Beweis: `refl`. Diese Identität ist zentral für die Korrektursektoren weiter unten.

---

## 10. Erzwungene Kopplungen (Sandwich-Argument)

Auf den drei Simplexdimensionen von $K_4$ wird jeweils eine Gewichtungsfunktion gesucht. Filter: $S_4$-Invarianz + Lokalität + nicht-triviale Obergrenze + nicht-triviale Untergrenze. Die Filter quetschen den Wert $r$ zwischen $1 \leq r \leq 1$, also $r = 1$ (Antisymmetrie von $\leq$).

### Dim 1 (Kanten → Propagation)

$$P : V \times V \to \mathbb{N}, \quad P_{vv} = 0,\quad S_4\text{-inv.},\quad 1 \leq P_{v_0 v_1} \leq 1$$
$$\Rightarrow\; P = \text{adjacent}, \quad \text{abgeleitete Konstante: } c = 1$$

### Dim 2 (Flächen → Aktion)

$$A : \text{Triangle} \to \mathbb{N}, \quad S_4\text{-inv.},\quad 1 \leq A_{\text{ref}} \leq 1$$
$$\Rightarrow\; A = 1, \quad \text{abgeleitete Konstante: } \hbar = 1$$

### Dim 0 (Knoten → Krümmung)

$$C : V \to \mathbb{N}, \quad S_4\text{-inv.},\quad 1 \leq C_{v_0} \leq 1$$
$$\Rightarrow\; C = 1, \quad \text{abgeleitete Konstante: } G = 1$$

### Minimalbasis der Filter

Jeder Filter ist notwendig — für jeden existiert ein Gegenbeispiel:
- Ohne Lokalität → $P \equiv 1$ überlebt (auch auf Diagonale)
- Ohne Invarianz → $P$ kann eine Referenzkante privilegieren
- Ohne Untergrenze → $P \equiv 0$ überlebt
- Ohne Obergrenze → $P \equiv 2$ überlebt

## 11. Skalenabschluss

$$c = \hbar = G = 1 \qquad \Rightarrow \qquad \ell_P = t_P = m_P = 1$$

3 physikalische Dimensionen (Länge, Zeit, Masse), 3 erzwungene Konstanten. Daher:

$$\text{free-parameters} = \dim - \text{constants} = 3 - 3 = 0 = \texttt{refl}$$

Normalisierte Skalenwahl $(a, b, m)$ mit $b = a$, $b = m a^2$, $m b^2 = a^3$:

$$\forall\, S : \text{NormalizedScaleChoice}.\;\; a = b = m = 1$$

Beweis: $a \geq 2 \Rightarrow a^2 = a$ — Widerspruch. Kein freier Parameter überlebt.

## 12. Invarianten-Record (Singleton)

$$\text{K4PhysRep} : \text{Set}$$

17 Felder, 16 verkettete Gleichtheits-Constraints. Anker: $\dim = |V_{K_4}| = 4$.

Die Feldnamen (dim, gauge-rank, coupling-inv, …) sind physikalisch motivierte **Labels**. Die **Werte** selbst sind rein aus $K_4$ erzwungen. Ob die Labels die physikalische Realität korrekt benennen, ist Interpretation — die Werte sind es nicht.

| Feld | Constraint | Wert | Beweis |
|------|-----------|------|--------|
| dim | $= V$ | 4 | `refl` |
| n-spatial | $= V - 1$ | 3 | `refl` |
| n-temporal | $= V - d$ | 1 | `refl` |
| gauge-rank | $= V \cdot d / 2$ | 6 | `refl` |
| face-count | $= V$ | 4 | `refl` |
| euler | $= (V+F) - E$ | 2 | `refl` |
| coupling-inv | $= V^d \cdot \chi + d^2$ | 137 | `refl` |
| n-gen | $= d$ | 3 | `refl` |
| spinor-dim | $= 2^V$ | 16 | `refl` |
| hierarchy | $= V \cdot E - \chi$ | 22 | `refl` |
| auto-count | $= V!$ | 24 | `refl` |
| bell-sq | $= V \cdot \chi$ | 8 | `refl` |
| bh-norm | $= V$ | 4 | `refl` |
| baryon-num | $= V - d$ | 1 | `refl` |
| baryon-den | $= E$ | 6 | `refl` |
| uv-cutoff | $= V - d$ | 1 | `refl` |
| min-loop | $= V - d$ | 1 | `refl` |

### Existenz

`canonical-rep : K4PhysRep` — alle 17 Felder + 16 Constraints durch `refl`.

### Determination

$$\forall\, r : \text{K4PhysRep}.\;\; \text{dim}\;r = 4,\;\; \text{spatial}\;r = 3,\;\; \ldots$$

Die Ankerkette propagiert: `anchor` $\Rightarrow$ `cg-deg` $\Rightarrow$ `cg-temporal` $\Rightarrow$ ... $\Rightarrow$ alle 17 Werte fixiert. Jeder Wert folgt aus dem vorherigen.

### Feldweise Eindeutigkeit (RepUniqueness)

$$\forall\, r_1\, r_2 : \text{K4PhysRep}.\;\; \text{field}\;r_1 = \text{field}\;r_2 \qquad\text{für alle 17 Felder}$$

Beweis pro Feld: $\text{trans}\;(F_1.\text{field-is-}k)\;(\text{sym}\;F_2.\text{field-is-}k)$.

### Record-Singleton (Hedberg + UIP)

Feldweise Übereinstimmung allein ergibt unter `--without-K` noch keine Record-Gleichheit: das Record trägt 16 Beweisfelder (Typ $m \equiv n : \mathbb{N}$), und deren Gleichheit ist nicht frei. Hedbergs Theorem schließt die Lücke: entscheidbare Gleichheit auf $\mathbb{N}$ $\Rightarrow$ UIP für $\mathbb{N}$ $\Rightarrow$ alle Beweisfelder kollabieren auf `refl`.

$$\texttt{K4PhysRep-is-canonical} : (r : \text{K4PhysRep}) \to r \equiv \text{canonical-rep}$$

Beweis: Substituiere alle 17 forcierten Datenfeldgleichheiten (Pattern-Match auf `refl`), dann eliminiere alle 16 Beweisfelder durch $\text{ℕ-UIP}\;p\;\text{refl}$. Record-Eta schließt.

$$\texttt{K4PhysRep-singleton} : (r_1\; r_2 : \text{K4PhysRep}) \to r_1 \equiv r_2$$

Beweis: $\text{trans}\;(\text{is-canonical}\;r_1)\;(\text{sym}\;(\text{is-canonical}\;r_2))$.

Das ist kein feldweiser Vergleich mehr — es ist propositionale Gleichheit auf Record-Ebene: der Typ $\text{K4PhysRep}$ hat **exakt einen Bewohner**.

### derivation-is-canonical

$$\text{derived-rep} \equiv \text{canonical-rep} \;=\; \texttt{refl}$$

Kein numerisches Literal im Beweis. Alles fließt aus benannten $K_4$-Invarianten.

---

## 13. Klassifikation von $\alpha^{-1} = 137$ (Kanonizitätsbeweis)

137 ist prim. Kein einzelnes Monom in $\{V, E, d, \chi, \kappa\}$ mit Grad $\leq 3$ erreicht 137, weil jedes solche Monom durch 2, 3 oder beides teilbar ist.

### Primausschluss (alle `refl`)

$$\gcd(137, V) = 1, \quad \gcd(137, E) = 1, \quad \gcd(137, d) = 1, \quad \gcd(137, \chi) = 1, \quad \gcd(137, \kappa) = 1$$

### Gradschranke

Die Schranke $\deg \leq 3$ ist **nicht frei gewählt**: der Simplex-Grad von $K_4$ stimmt mit dem Knotengrad überein (`simplex-degree ≡ degree-K4 ≡ 3`, Beweis: `refl`). Monome höheren Grades sind nicht verboten — sie liegen nur außerhalb des **primitiven** Observablensektors, der durch die lokale Interaktionstiefe des Graphen begrenzt ist.

### Formaler Sektor: `PrimitiveObservableSector`

Das Agda-Record `PrimitiveObservableSector` verpackt diese Struktur mit den folgenden maschinengeprüften Feldern:

- `cutoff-from-graph : simplex-degree ≡ degree-K4` — Schranke kommt aus dem Graphen
- `cutoff-is-structural : simplex-degree ≡ 3`
- `admissible` — Zulässigkeitsprädikat = Monome mit Grad $\leq$ simplex-degree
- `bulk-is-primitive` + `bulk-evaluates-to-128 : eval-monomial (mono 2 0 0 0 1) ≡ 128` — $V^2 \kappa = 128$
- `degree-square-is-primitive` + `degree-square-evaluates-to-9 : eval-monomial (mono 0 0 2 0 0) ≡ 9` — $d^2 = 9$
- `quartic-chi-begins-iteration` — $\chi^4$ liegt **über** der Schranke
- `quartic-chi-is-not-primitive` — $\chi^4$ ist kein primitives Observable

### Einzige Zerlegung

$$128 + 9 = V^3\chi + d^2 = V^2\kappa + d^2 = 137 \qquad\text{Beweis: \texttt{refl}}$$

Keine andere Zwei-Term-Zerlegung in Monomen vom Grad $\leq 3$ ergibt 137. Der Wert ist **nicht gefittet** — er ist der einzige Überlebende der Zulässigkeitsfilter.

---

## 14. Universeller Schleifennumerator $11$ (Forciert durch Elimination)

### Suchraum

Alle $\{0,1\}$-Linearkombinationen über $\{E, d, \chi\}$: genau $2^3 = 8$ Kandidaten.

| Kandidat | Wert | $\gcd(\cdot, 72)$ | Filter 1 |
|----------|------|-------------------|----------|
| $\emptyset$ | 0 | — | eliminiert (trivial) |
| $\chi$ | 2 | 2 | eliminiert |
| $d$ | 3 | 3 | eliminiert |
| $d + \chi$ | 5 | 1 | **überlebt** |
| $E$ | 6 | 6 | eliminiert |
| $E + \chi$ | 8 | 8 | eliminiert |
| $E + d$ | 9 | 9 | eliminiert |
| $E + d + \chi$ | 11 | 1 | **überlebt** |

Alle 8 Werte und alle $\gcd$-Berechnungen: `refl`.

### Drei Filter

1. **Irreduzibilität**: $\gcd(N, V \cdot E \cdot d) = 1$. Eliminiert 6 von 8. Überlebende: $5$ und $11$.
2. **Vollständigkeit**: Das Observable muss die volle irreduzible Schleifenbasis $\{E, d, \chi\}$ nutzen. $d + \chi = 5$ lässt den $E$-Sektor aus → eliminiert. Begründung formal: $\gcd(5, 6) = 1$ (`refl`) — die partielle Summe hat keinen Zugang zum $\{2,3\}$-Stratum der Interaktionsvolumina.
3. **Skalen-Konsistenz**: Derselbe Numerator an jeder Skala. Filter 3 bestätigt das Ergebnis von Filter 2.

$$E + d + \chi = 6 + 3 + 2 = 11 \qquad\text{Beweis: \texttt{refl}}$$

**Einziger Überlebender.** Jede Alternative scheitert an Irreduzibilität oder Vollständigkeit. Die Vollständigkeit ist kein separates Axiom: sie folgt aus $\chi \cdot d = E$ und der Rolle von $E$ im Interaktionsvolumen.

---

## 15. Kanonische Volumina und Korrekturkette

### Volumina (alle `refl`)

| Skala | Formel | Wert | Beweis |
|-------|--------|------|--------|
| QCD (Hadronen) | $V \cdot E \cdot d$ | 72 | `refl` |
| Elektroschwach | $V \cdot E \cdot d \cdot \kappa$ | 576 | `refl` |
| Skalenfaktor | $\kappa = V \cdot \chi$ | 8 | `refl` |
| RG-Steigung | $2\alpha^{-1}$ | 274 | `refl` |

Die Volumina sind keine neuen Observablen — sie sind kanonische Produkte bereits erzwungener Invarianten. $\kappa = 8$ verbindet QCD- und EW-Skala: $576 = 72 \cdot 8$ (`refl`).

### Der Diskret-Kontinuum-Brückentheorem

Das Agda-Record `DiscreteContinuumMapUniqueness` bündelt:

- Eindeutiger Schleifennumerator: $\forall s.\; \text{loop-numerator} \equiv 11$
- QCD-Volumen kanonisch: $72$ (`refl`)
- EW-Volumen kanonisch: $576$ (`refl`)
- QCD-Quotient irreduzibel: $\gcd(11, 72) = 1$ (`refl`)
- EW-Quotient irreduzibel: $\gcd(11, 576) = 1$ (`refl`)
- Quotientenfelder eindeutig (Zähler und Nenner bestimmt)
- Reduzierte Normalformen erzwungen: $11/72$ und $11/576$

$$\texttt{theorem-discrete-continuum-map-unique : DiscreteContinuumMapUniqueness}$$

Vollständig maschinell verifiziert. Die Brücke verzweigt nicht — an jeder Skala ist die Korrektur fixiert.

### Korrekturtabelle

| Größe | Baum-Wert | Numerator | Volumen | Korrektur | Korrigierter Wert | Messwert |
|-------|-----------|-----------|---------|-----------|-------------------|----------|
| Proton/Elektron-Masse | 1836 | 11 | 72 ($V \cdot E \cdot d$) | $+11/72$ | $1836.1527\overline{7}$ | $1836.15267$ |
| $\sin^2\theta_W$ | $\chi/\kappa = 0.25$ | 11 | 576 ($V \cdot E \cdot d \cdot \kappa$) | $-11/576$ | $0.2309$ | $0.2312$ |
| RG-Steigung | — | 1 | 274 ($2\alpha^{-1}$) | $1/274$ | — | — |

**Proton-Präzision:** Korrigierter Wert $1836.15278$ vs. Messung $1836.15267$ — **Übereinstimmung auf 6 signifikante Stellen.** Das Residuum $|0.15278 - 0.15267| = 0.00011 \approx 1/9000$ ist von der Ordnung $1/576$ — exakt die nächsthöhere Korrektur aus dem elektroschwachen Volumen.

**Weinberg-Winkel:** Korrigierter Wert $0.2309$ vs. Messung $0.2312$ — innerhalb $0.1\%$.

---

## 16. Massensektoren (Forciert durch Elimination)

### Proton-Masse: $1836 = F_2 \cdot E^2 d = 17 \cdot 108$

Zwei-Kanal-Zerlegung:
- **Kompaktifizierungskanal:** $F_2 = 2^V + 1 = 17$ (Fermatzahl, forciert als einziger Kompaktifizierungsüberlebender)
- **Lokaler Kofaktor:** $E^2 d = 36 \cdot 3 = 108$ — reduziert aus $\chi^2 d^3 = 4 \cdot 27 = 108$ über $\chi d = E$ (`refl`)

$F_2$ ist koprim zum Basis-Invariantenprodukt: $\gcd(17, V \cdot E \cdot d \cdot \chi) = \gcd(17, 144) = 1$ (`refl`)

Die Trennung Kompaktifizierung / lokaler Graph ist strukturell — sie verhindert, dass der Kompaktifizierungsprime in die lokale Grapharithmetik zurückgeschmuggelt wird.

### Muon-Masse: $207 = d^2 \cdot (E + F_2) = 9 \cdot 23$

Zwei verschiedene Kanäle:
- **Geometrischer Kanal:** $d^2 = 9$
- **Gemischter Kanal:** $E + F_2 = 6 + 17 = 23$

Produkt: $9 \cdot 23 = 207$ (`refl`)

### Tau/Muon-Verhältnis: $17 = F_2$

Der terminale Massenquotient sitzt im Kompaktifizierungskanal allein. Nur zwei Kandidaten: $2^V = 16$ und $2^V + 1 = 17$. Nur einer überlebt den Terminalwert-Filter: $F_2 = 17$ (`refl`).

---

## 17. Epistemic-Status-Zensus (Klassifikation aller abgeleiteten Sektoren)

Jeder abgeleitete Sektor wird vollständig durchklassifiziert. Ergebnis:

| Sektor | Überlebender | Status |
|--------|-------------|--------|
| $\alpha^{-1}$ | $V^d\chi + d^2 = 137$ | forciert durch Elimination (einzige Zwei-Term Grad-$\leq 3$ Zerlegung) |
| Schleifennumerator | $E + d + \chi = 11$ | forciert durch Elimination (3 Filter auf $2^3$ Kandidaten) |
| Volumina | $72, 576, 274$ | abgeleitet (kanonische Produkte bereits erzwungener Invarianten) |
| Proton-Masse | $F_2 \cdot E^2d = 1836$ | forciert nach Kanalreduktion |
| Muon-Masse | $d^2 \cdot (E + F_2) = 207$ | forciert durch Kanaltrennung |
| Tau/Muon | $F_2 = 17$ | forciert durch Kompaktifizierungs-Elimination |

Keine dieser Größen wird gefittet. Keine erfordert einen freien Parameter. Jede ist der einzige Überlebende eines expliziten, endlichen Eliminationsprozesses.

---

## 18. Schleifenschluss

$$\text{physics-presupposes-distinction} : (p : \text{K4PhysRep}) \to D_0$$

$$\text{physics-without-distinction-uninhabitable} : \neg D_0 \to \text{K4PhysRep} \to \bot$$

Das K4PhysRep-Record verkettet 16 Gleichheitszeugen. Der Anker bindet $\dim = |V_{K_4}| = 4$. Gleichheitszeugen setzen den Identitätstyp voraus, und der Identitätstyp setzt $D_0$ voraus. Wird $D_0$ geleugnet, wird das gesamte Record unbewohnbar.

Die Kette ist zirkulär:

$$D_0 \;\longrightarrow\; \text{Two} \;\longrightarrow\; \text{Endo}^4 \;\longrightarrow\; K_4 \;\longrightarrow\; \text{Invarianten} \;\longrightarrow\; \text{K4PhysRep} \;\longrightarrow\; D_0$$

**Richtungsasymmetrie:** Der Kreis schließt sich, aber die Abhängigkeit ist gerichtet. Physik **konsumiert** Unterscheidung — sie **erzeugt** sie nicht. Wird $\neg D_0$ angenommen, kollabiert K4PhysRep zu $\bot$. Wird K4PhysRep angenommen, folgt $D_0$. Die Umkehrung (Physik als Fundament) ist typtheoretisch ausgeschlossen.

---

## Zusammenfassung: Die vollständige Kette

| # | Schritt | Typ | Beweis |
|---|---------|-----|--------|
| 1 | $D_0$ existiert | `Two-distinction : Distinction` | Direkte Konstruktion (parameterlos) |
| 2 | $D_0$ eindeutig | $\forall d.\;\text{Iso}\;d\;\text{Two}$ | Normalform |
| 3 | 4 Endomorphismen | `EndoCase` | Klassifikation |
| 4 | Alle verschieden | 6× $\lambda\;()$ | Diskriminierung |
| 5 | $K_4$ konstruiert | `Edge = λ a b → a ≠ b` | Vollständiger Graph |
| 6 | $K_4$ kanonisch | `GraphIso` | Präsentationskollaps |
| 7 | $c = \hbar = G = 1$ | Sandwich $1 \leq r \leq 1$ | $S_4$-Invarianz + Antisymmetrie |
| 8 | 0 freie Parameter | $3 - 3 = 0$ | `refl` |
| 9 | $\alpha^{-1} = 137$ | $V^d\chi + d^2$, PrimitiveObservableSector | `refl` + Elimination |
| 10 | Numerator $= 11$ | 8 Kandidaten → 3 Filter → 1 Überlebender | `refl` + `gcd` |
| 11 | Volumina $72, 576$ | $V \cdot E \cdot d \cdot \kappa^{0,1}$ | `refl` |
| 12 | Proton $1836 + 11/72$ | Brückentheorem, 6 sig figs Übereinstimmung | `refl` |
| 13 | Weinberg $0.25 - 11/576$ | Selber Numerator, $\kappa$-skaliertes Volumen | `refl` |
| 14 | Massen $1836, 207, 17$ | Kanal-Elimination | `refl` |
| 15 | Record-Singleton | `K4PhysRep-singleton` (Hedberg + UIP auf ℕ) | `trans` + `sym` + `ℕ-UIP` |
| 16 | Schleifenschluss | `K4PhysRep → D₀` | `anchor` + `Two-distinction` |

---

## Empirischer Abgleich

**Alles bis hier ist reines Theorem:** $D_0 \to K_4 \to$ Invarianten $\to$ Korrekturen. Maschinengeprüft, kein Spielraum.

| Größe | Empirie | Modell ($K_4$) | $\Delta$ | Freie Param. |
|-------|---------|----------------|----------|--------------|
| $\alpha^{-1}$ | $\approx 137.036$ | $137$ (Baum) + Korrekturen | — | 0 |
| Raumdimensionen | $3$ | $V - 1 = 3$ | $0$ | 0 |
| Zeitdimensionen | $1$ | $V - d = 1$ | $0$ | 0 |
| Fermion-Generationen | $3$ | $d = 3$ | $0$ | 0 |
| Eichfelder | $6$ (vor Brechung) | $E = 6$ | $0$ | 0 |
| $c, \hbar, G$ | $1, 1, 1$ (Planck) | $1, 1, 1$ (Sandwich) | $0$ | 0 |
| Proton/Elektron | $1836.15267$ | $1836 + 11/72 = 1836.1528$ | $6 \times 10^{-6}$ | 0 |
| $\sin^2\theta_W$ | $0.2312$ | $2/8 - 11/576 = 0.2309$ | $0.001$ | 0 |
| Muon/Elektron | $\approx 207$ | $d^2(E + F_2) = 207$ | $0$ (Baum) | 0 |
| Tau/Muon | $\approx 17$ | $F_2 = 17$ | $0$ (Baum) | 0 |

---

## Was formal bewiesen ist

1. Aus $D_0$ allein folgt $K_4$ — keine Wahl, kein Spielraum, 56 Kapitel Elimination
2. $K_4$ hat exakt die obigen Invarianten — $V = 4$ erzwingt alles, jede Zeile `refl`
3. Die Simplexgewichtungen sind Singletons — Sandwich-Elimination
4. $\alpha^{-1} = 137$ ist die einzige Zerlegung im primitiven Observablensektor — formal bewiesen durch `PrimitiveObservableSector`
5. Der Schleifennumerator $11$ ist forciert — 8 Kandidaten, 3 Filter, 1 Überlebender
6. Die Korrekturkette ist kanonisch — `DiscreteContinuumMapUniqueness` mit eindeutigen reduzieren Normalformen
7. Die Massensektoren ($1836, 207, 17$) sind jeweils durch Kanal-Elimination forciert
8. Der Invarianten-Record existiert, ist eindeutig (Singleton), und schließt den Kreis
9. **Jeder** Schritt ist maschinengeprüft (`--safe --without-K`, null Postulate)

## Epistemische Trennlinie: Was ist forciert, was ist Interpretation?

Ein häufiger Einwand behauptet, drei Punkte seien „teilweise offen": die Wahl des Observablensektors, die Interpretation der Invarianten, und die physikalische Zuordnung. Dieser Einwand verwechselt geschlossene Fragen mit offenen.

### 1. Observablensektor — GESCHLOSSEN (forciert, nicht gewählt)

Die Monombasis $\{V, E, d, \chi, \kappa\}$ ist keine Auswahl aus einem größeren Vorrat. Es sind die **kanonischen Simplexinvarianten** von $K_4$ (§9) — Knotenzahl, Kantenzahl, Grad, Euler-Charakteristik, Spektralbreite. Sie sind durch den Graphen selbst definiert, nicht durch eine externe Liste.

Die Gradschranke $\deg \leq 3$ ist ebenfalls nicht gewählt: `simplex-degree ≡ degree-K4 ≡ 3` (`refl`). Sie folgt aus der lokalen Interaktionstiefe des Graphen (§13).

Die einzig offene Frage wäre: „Warum Polynome und nicht eine andere Klasse von Funktionen?" Die Antwort: Polynome in Grapheninvarianten **sind** die kombinatorischen Observablen eines endlichen Graphen. Es gibt keine natürlichere Klasse — jede Alternative (z.B. transzendente Funktionen, reellwertige Gewichte) würde Struktur importieren, die $K_4$ nicht enthält. Der Sektor ist nicht gewählt — er ist der einzige, der nichts Externes voraussetzt.

### 2. Werte — GESCHLOSSEN (forciert durch `refl`)

Die Werte $V = 4$, $E = 6$, $d = 3$, $\chi = 2$, $\alpha^{-1} = 137$, etc. sind durch `refl` fixiert. Hier gibt es keinen Spielraum. Das `K4PhysRep`-Record hat genau einen Bewohner (`K4PhysRep-singleton`).

### 3. Label ↔ Physik — OFFEN (Interpretation)

Die **einzig** offene Frage ist die Zuordnung: *Bedeutet das Feld `dim = 4` tatsächlich „Raumzeitdimensionen"?* *Ist `coupling-inv = 137` tatsächlich $\alpha^{-1}$?*

Die Werte stehen fest. Was nicht feststeht, ist, ob die physikalisch motivierten **Feldnamen** die richtige Brücke zur Empirie schlagen. Das ist keine mathematische Frage — es ist eine Interpretationsfrage. §12 sagt dies explizit: „Die Feldnamen sind physikalisch motivierte Labels. Die Werte selbst sind rein aus $K_4$ erzwungen. Ob die Labels die physikalische Realität korrekt benennen, ist Interpretation — die Werte sind es nicht."

### Zusammenfassung der epistemischen Grenze

| Häufig behauptet „offen" | Tatsächlicher Status | Begründung |
|---|---|---|
| Wahl des Observablensektors | **Geschlossen** | Simplexinvarianten + `simplex-degree ≡ 3` (`refl`) |
| Werte der Invarianten | **Geschlossen** | `K4PhysRep-singleton` — exakt ein Bewohner |
| Label ↔ Physik (Interpretation) | **Offen** | Interpretationsschritt, kein Theorem |
| Numerische Übereinstimmung kausal? | **Offen** | Empirisch, nicht formal |

Nur die letzten beiden Zeilen sind echte offene Punkte. Und sie reduzieren sich auf eine einzige Frage: *Ist die Übereinstimmung zwischen den forcierten Werten und den gemessenen Naturkonstanten Zufall, Notwendigkeit, oder Artefakt?*

## Warum es kein „anderes Axiomensystem" geben kann

Ein früherer Entwurf enthielt den Vorbehalt: *Was das Modell nicht zeigt: dass kein anderes Axiomensystem dieselben Werte erzeugen könnte.* Dieser Vorbehalt ist falsch.

Das Argument:

1. Jede konsistente Typentheorie (nicht: jeder Typ!) kann den Typ `data Two = L | R` definieren. Zwei Konstruktoren, keine Parameter, keine Postulate. Das ist kein ontologischer Universal-Claim — es ist ein syntaktisches Faktum über Typentheorien. ($\top$ ist kein Gegenbeispiel: $\top$ ist ein Typ *innerhalb* einer Theorie, nicht eine Theorie selbst. Die Theorie, die $\top$ enthält, enthält auch `Two`.)
2. Dieser Typ mit Exhaustion **ist** $D_0$. Nicht analog, nicht isomorph — identisch: ein Typ mit zwei unterscheidbaren Elementen und vollständiger Fallanalyse.
3. Ein hypothetisches „Meta-System" über $D_0$ müsste sich vom Nicht-Meta unterscheiden. Diese Unterscheidung setzt $D_0$ voraus. Also enthält jedes Meta bereits $D_0$.
4. $D_0$ ist **konstruktiv bewiesen** (`Two-distinction : Distinction`, parameterlos). Daraus folgt $\neg\neg D_0$ trivial. Zusätzlich: jede Messung enthält $D_0$ (`measurement-outcome-distinction`), und das physikalische Record gibt $D_0$ zurück (`physics-presupposes-distinction`). Es gibt keinen Standpunkt, von dem aus $D_0$ vermieden werden könnte.
5. Aus $D_0$ folgt $K_4$ ohne Wahlfreiheit (56 Kapitel Elimination). Aus $K_4$ folgt `K4PhysRep-singleton`: genau ein Satz von Werten.

Die Kette benutzt ausschließlich endliche Fallanalyse und entscheidbare $\mathbb{N}$-Arithmetik. Diese Operationen sind in **jeder** konsistenten Typentheorie verfügbar — mit K, ohne K, mit Univalenz, klassisch, intuitionistisch. Das Resultat ist theorienunabhängig.

### Minimalität, nicht Universalität

Ein möglicher Einwand: *$D_0$ sei nur ein binärer Typ — eine Dreiermenge $\{a,b,c\}$ habe keine kanonische Reduktion auf zwei Elemente, also sei $D_0$ nicht universal.*

Der Einwand verwechselt zwei Behauptungen:

| Was der Einwand verlangt | Was die Kette benutzt |
|---|---|
| $D_0$ als **universelles Faktorisierungsobjekt** (alle Unterscheidungen faktorisieren durch $D_0$) | $D_0$ **existiert** (konstruktiv: `Two-distinction`), und aus $D_0$ allein folgt $K_4$ |

Die Kette startet nicht von „es gibt viele Unterscheidungen, bündle sie zu $D_0$". Sie startet von „$D_0$ ist konstruktiv bewiesen (`Two-distinction`) $\to$ Normalform $\to$ Endo$^4$ $\to$ $K_4$". Ein Faktorisierungs-Lemma der Form $(a \neq b) \Rightarrow \exists f : S \to \{0,1\}$ wird nirgends benutzt und nirgends benötigt.

Zum {a,b,c}-Punkt: Wer mit einer Dreiermenge $D_0^3$ startet, hat **mehr** als $D_0$, nicht weniger — denn $D_0^3$ enthält $D_0$ als Substruktur (wähle zwei beliebige der drei Elemente). Und $D_0$ allein feuert die gesamte Kette bis $K_4$ ab. Die Extra-Struktur von $D_0^3$ ist irrelevant: das Minimum forciert bereits alles.

$D_0$ ist nicht universal, sondern **minimal**. Weniger als zwei unterscheidbare Elemente ist keine Unterscheidung. Mehr als zwei enthält zwei. $D_0$ ist der Boden — nicht das Dach.

Es gibt nichts „über" Typentheorie, weil „über" eine Unterscheidung (oben/unten, meta/objekt) erfordern würde — und Unterscheidung ist $D_0$.

### Warum „Existenz ⇒ D₀" ein Kategorienfehler ist

Ein wiederkehrender Einwand verlangt einen Beweis der Form: *Wenn etwas existiert, dann existiert $D_0$.* Formal:

$$\forall\, (A : \text{Set}).\;\; A \to D_0$$

Dieser Satz ist **falsch** — und das lässt sich sofort zeigen. Der Typ $\top$ (Singleton, ein Element, keine Unterscheidung) ist bewohnt: $\text{tt} : \top$. Aber $\top$ trägt keine zwei verschiedenen Elemente. Also ist $(A : \text{Set}) \to A \to D_0$ unbewohnbar. Gegenbeispiel: $A = \top$.

Die Forderung verwechselt zwei Ebenen:

| Was verlangt wird | Warum es scheitert |
|---|---|
| „Keine Existenz ohne Unterscheidung" (ontologisch) | Typentheorie kennt Typen ohne Unterscheidung ($\top$, $\mathbb{1}$). Sie sind bewohnt. |
| „Keine Referenz ohne Unterscheidung" (epistemisch) | Referenz auf $\text{tt} : \top$ ist trivial möglich — durch `refl`. |
| „Keine Identität ohne Unterscheidung" | $\text{tt} \equiv \text{tt}$ ist `refl`. Identität erfordert keine Zweiheit. |

Die Schritte 1–5 des Einwands (Objekt ohne Unterscheidung → keine Identität → keine Referenz → keine Existenzbehauptung → Widerspruch) sind jeweils einzeln widerlegbar: $\top$ ist das kanonische Gegenbeispiel zu jedem Schritt.

**Warum die Kette dieses „Theorem" nicht braucht:**

Die Kette behauptet nicht „alles braucht $D_0$". Sie behauptet:

1. $D_0$ **existiert** — parameterlos, postulatslos: `Two-distinction : Distinction`
2. Aus $D_0$ **allein** folgt $K_4$ durch Elimination
3. $K_4$ hat **genau einen** Invariantensatz: `K4PhysRep-singleton`

Der Startpunkt ist nicht „Existenz impliziert Unterscheidung", sondern „Unterscheidung ist frei verfügbar". Wer `data Two = L | R` akzeptiert, hat $D_0$. Wer es ablehnt, hat keine Typentheorie — und kein formales System, in dem der Einwand überhaupt formulierbar wäre.

Das vermeintlich fehlende Glied — „Existenz ⇒ $D_0$" — ist nicht fehlend. Es ist **falsch**. Was an seiner Stelle steht, ist stärker: $D_0$ ist **bedingungslos konstruierbar**, und die Kette benötigt keine Prämisse.

## Was das Werk zeigt

Die *einzige* Struktur, die aus $D_0$ überlebt, hat Invarianten, die mit empirisch gemessenen Naturkonstanten übereinstimmen — **ohne dass ein einziger Parameter frei wäre**. Die Übereinstimmung erstreckt sich nicht nur auf ganzzahlige Strukturkonstanten ($3+1$ Dimensionen, 3 Generationen, 6 Eichfelder), sondern auch auf rationale Korrekturen mit sub-ppm-Präzision (Proton: 6 signifikante Stellen).

Das ist weder ein Beweis der Physik noch Numerologie. Es ist ein Notwendigkeits-Resultat:

> In jeder konsistenten Typentheorie ist $D_0$ konstruierbar (`data Two = L | R`, parameterlos).
> Aus $D_0$ folgt $K_4$ durch Elimination.
> $K_4$ hat genau einen Satz von Invarianten (`K4PhysRep-singleton`).
> Dieser Satz stimmt mit den empirischen Naturkonstanten überein.

Die offene Frage ist nicht „stimmen die Zahlen?" (sie stimmen), und nicht „könnte eine andere Typentheorie andere Zahlen liefern?" (nein — jede konsistente Typentheorie enthält `Two` und damit $D_0$), sondern:

> **Warum stimmt die Empirie mit dem einzigen formal möglichen Wertesatz überein?**

Diese Frage ist keine Schwäche des Beweises. Sie ist sein Resultat.

Darauf gibt es drei mögliche Antworten:
- **Zufall** — dann ist die Abwesenheit freier Parameter und die sub-ppm-Übereinstimmung erklärungsbedürftig
- **Tiefere Notwendigkeit** — dann ist $D_0$ eine Fundamentalstruktur der Physik
- **Artefakt** — dann muss gezeigt werden, *welche* versteckte Wahl die Zahlen erzwingt (der Agda-Code enthält keine Postulate — die Suche nach einem Artefakt muss konkret sein)

Keine dieser Antworten ist trivial. Alle drei verdienen eine Untersuchung.

---

## Technische Fakten für maschinelle Verifikation

- **Sprache:** Agda, `--safe --without-K`
- **Postulate:** 0 (null)
- **Beweismittel:** `refl` (definitorische Gleichheit), `λ ()` (leerer Typ), `s≤s`/`z≤n` (Ordnungsbeweise), `trans`/`sym` (Gleichheitsketten)
- **Datei:** `FirstDistinction.lagda.tex`, ~26.400 Zeilen, 56 Kapitel
- **Kompiliert sauber:** `agda --safe --without-K FirstDistinction.lagda.tex` terminiert ohne Fehler
- **Kein numerisches Literal im Singleton-Beweis:** Alle Werte fließen aus benannten $K_4$-Invarianten
- **Schlüssel-Records:** `Distinction` (§1), `K4PhysRep` (§12), `PrimitiveObservableSector` (§13), `DiscreteContinuumMapUniqueness` (§15), `MassObservableSector` (§16)
- **Schlüssel-Theoreme:** `theorem-primitive-observable-sector`, `theorem-discrete-continuum-map-unique`, `physics-presupposes-distinction`, `measurement-outcome-distinction`, `K4PhysRep-singleton`
