# Glossar: Schlüsselwörter aus Step1 bis Step4

Dieses Glossar erklärt alle nicht-trivialen Schlüsselwörter und Zeichen, die in
[Step1.lean](LeanSeminar/Step1.lean), [Step2.lean](LeanSeminar/Step2.lean),
[Step3.lean](LeanSeminar/Step3.lean) und [Step4.lean](LeanSeminar/Step4.lean) vorkommen. Die Länge der Erklärung richtet sich nach
der Schwierigkeit des Begriffs. Selbsterklärendes wie `--`, `:=`, `+` oder `Nat` fehlt.

Alle Fehlermeldungen stammen aus Lean `v4.35.0`, der Version dieses Projekts.

**Inhalt**

1. [Grundmodell: Ziel, Kontext und Beweis mit Lücken](#1-grundmodell-ziel-kontext-und-beweis-mit-lücken)
2. [Taktiken](#2-taktiken): `by`, `intro`, `constructor`, `exact`, `·`, `decide`, `induction`, `rw`
3. [Beweisterme](#3-beweisterme): `rfl`, `fun`, `⟨_, _⟩`, `.1` / `.left`, Lemmata anwenden
4. [Logik und Typen](#4-logik-und-typen): `Prop`, `→`, `∀`, `∧`, `=` / `<` / `≤`, `Bool` vs. `Prop`
5. [Deklarationen](#5-deklarationen): `def`, `theorem`, `example`, `inductive`, `namespace`
6. [Pattern Matching und Konstruktoren](#6-pattern-matching-und-konstruktoren)
7. [Kleinere Syntax](#7-kleinere-syntax): `@`, `_`, `.milch`, `(e : T)`, Kommentare
8. [Befehle für den Editor](#8-befehle-für-den-editor): `#check`, `#eval`, `#print`

---

## 1. Grundmodell: Ziel, Kontext und Beweis mit Lücken

Ohne dieses Modell bleiben `intro`, `constructor` und `exact` unverständlich.

**Ein Beweis ist ein Term.** Ein Beweis von `P ∧ Q → Q ∧ P` ist am Ende ein Programm wie
`fun h => And.intro h.right h.left`. Nur dieser Term wird vom **Kernel** geprüft. Der Kernel
ist ein kleiner, vertrauenswürdiger Typprüfer.

**Ein Taktikbeweis baut diesen Term schrittweise.** Am Anfang ist der Beweis ein einziges
Loch. Jede Taktik füllt ein Loch teilweise aus und kann dabei neue, kleinere Löcher
hinterlassen. Jedes noch offene Loch ist ein **Ziel** (engl. *goal*).

Der **Infoview** zeigt zu jedem offenen Ziel zwei Dinge:

```text
P Q : Prop          ← Kontext: was wir haben (Variablen, Annahmen)
h : P ∧ Q
⊢ Q ∧ P             ← Ziel: was wir noch zeigen müssen
```

Das Zeichen `⊢` trennt beides. Man liest es als „daraus ist zu zeigen“. Sind keine Ziele
mehr offen, meldet der Infoview *No goals* und der Beweis ist fertig.

So entsteht `und_komm_taktik` aus Step3 Schritt für Schritt. `?_` steht für ein Loch:

| Schritt        | Bisher gebauter Term                    | Offene Ziele        |
|----------------|-----------------------------------------|---------------------|
| Start          | `?_`                                    | `⊢ P ∧ Q → Q ∧ P`   |
| `intro h`      | `fun h => ?_`                           | `⊢ Q ∧ P`           |
| `constructor`  | `fun h => And.intro ?_ ?_`              | `⊢ Q` und `⊢ P`     |
| `exact h.right`| `fun h => And.intro h.right ?_`         | `⊢ P`               |
| `exact h.left` | `fun h => And.intro h.right h.left`     | keine               |

Das Ergebnis ist genau der Termbeweis `und_komm_term`. `#print und_komm_taktik` bestätigt das.

---

## 2. Taktiken

### `by`

Schaltet vom Term-Modus in den **Taktik-Modus**. Hinter `by` steht kein fertiger Term, sondern
eine Folge von Anweisungen, die den Term bauen. `by` darf auch mitten in einem Term stehen.
Ein Beispiel ist `Nat.lt_add_of_pos_right (by decide)` in Step2: Dort beweist `by decide` nur
das eine Argument `0 < 25`.

### `intro`: „Angenommen, …“

**Wann:** Das Ziel ist eine Implikation `A → B` oder eine Allaussage `∀ x, B x`.

**Was passiert:** Die Voraussetzung wandert unter einem Namen in den Kontext, und das Ziel wird
zur Schlussfolgerung.

```text
vorher:               intro h                nachher:
⊢ P ∧ Q → Q ∧ P       ───────────▶           h : P ∧ Q
                                             ⊢ Q ∧ P
```

**Mathematisch:** „Angenommen, `P ∧ Q` gilt. Nennen wir diese Annahme `h`.“ So beginnt man auf
Papier jeden Beweis einer Wenn-dann-Aussage.

**Als Term:** `intro h` erzeugt `fun h => ?_`. Ein Beweis von `A → B` ist eine Funktion (siehe
Step2). `intro` beginnt diese Funktion, indem es ihr Argument benennt. Der Rest des Beweises
ist der Funktionsrumpf.

**Varianten:** `intro hp hq` führt mehrere Annahmen auf einmal ein (in Step3 einzeln
geschrieben). Bei `∀ n : Nat, …` führt `intro n` ein *beliebiges* `n` ein: „Sei `n` eine
natürliche Zahl.“ Das wird in Arbeitsauftrag 4 wichtig.

**Fehlerfall:** Gibt es nichts einzuführen, weil das Ziel weder `→` noch `∀` ist, meldet Lean:

```text
Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
```

### `constructor`: „Wir zeigen beide Teile einzeln.“

**Wann:** Das Ziel ist ein induktiver Typ, also ein Typ, der durch Konstruktoren definiert ist
(siehe [Abschnitt 6](#6-pattern-matching-und-konstruktoren)). In unseren Dateien ist das
`Q ∧ P`.

**Was passiert:** Lean wendet den Konstruktor des Ziels an. Für `∧` gibt es genau einen,
`And.intro : a → b → a ∧ b`. Dessen Argumente fehlen noch und werden **neue Ziele**:

```text
vorher:               constructor            nachher (zwei Ziele):
h : P ∧ Q             ───────────▶           case left        case right
⊢ Q ∧ P                                      h : P ∧ Q        h : P ∧ Q
                                             ⊢ Q              ⊢ P
```

**Mathematisch:** „Um `Q ∧ P` zu zeigen, zeigen wir zuerst `Q` und dann `P`.“ Die Taktik zerlegt
das Ziel und baut dabei nichts Inhaltliches.

**Als Term:** `constructor` erzeugt `And.intro ?_ ?_`.

**Warum der Name?** Die Taktik ist nicht auf `∧` beschränkt. Sie wendet bei *jedem* induktiven
Typ einen passenden Konstruktor an, zum Beispiel bei `↔` den Konstruktor `Iff.intro`. Bei Typen
mit mehreren Konstruktoren nimmt sie den ersten, der passt. Für `∨` benutzt man deshalb besser
gezielt `left` oder `right`.

**Fehlerfall:** Ist das Ziel eine bloße Aussagenvariable wie `⊢ P`, gibt es keinen Konstruktor:

```text
Tactic `constructor` failed: target is not an inductive datatype
```

### `exact`: „Genau das ist der Beweis.“

**Wann:** Man hat einen Term zur Hand, dessen Typ **genau** das aktuelle Ziel ist.

**Was passiert:** Der Term wird in das Loch eingesetzt, und das Ziel ist geschlossen.

```text
vorher:               exact h.right          nachher:
h : P ∧ Q             ───────────▶           (Ziel geschlossen)
⊢ Q
```

**Mathematisch:** „Das ist genau unsere Annahme.“ Oder: „Das folgt direkt aus …“.

**Als Term:** `exact t` setzt `t` ein. `exact` ist damit die **Brücke vom Taktik-Modus zurück in
den Term-Modus**: Hinter `exact` steht ein ganz normaler Term. Das kann eine Annahme sein
(`exact hp`), ein Feldzugriff (`exact h.right`), eine Funktionsanwendung (`exact regel hb`) oder
ein Lemma.

**Fehlerfall:** Lean prüft den Typ streng. Passt er nicht, kommt ein Typfehler:

```text
Type mismatch
  hp
has type
  P
but is expected to have type
  Q
```

**Tipp:** `exact?` lässt Lean selbst nach einem passenden Term suchen und schlägt ihn vor
(*Try this: …*). Für die Abgabe sollte man den Vorschlag aber verstehen, bevor man ihn übernimmt.

### Zusammenfassung der drei Taktiken

| Taktik        | Wann?                          | Term-Baustein      | Auf Papier                         |
|---------------|--------------------------------|--------------------|------------------------------------|
| `intro h`     | Ziel `A → B` oder `∀ x, …`     | `fun h => ?_`      | „Angenommen `A` …“ / „Sei `x` …“   |
| `constructor` | Ziel `A ∧ B` (allg. induktiv)  | `And.intro ?_ ?_`  | „Wir zeigen `A` und `B` einzeln.“  |
| `exact t`     | `t` hat genau den Zieltyp      | `t`                | „Das folgt direkt aus `t`.“        |

### `·` (Fokuspunkt)

Erzeugt eine Taktik mehrere Ziele, etwa `constructor`, bearbeitet `·` das jeweils **erste**
offene Ziel in einem eigenen eingerückten Block. Der Block muss sein Ziel vollständig schließen,
sonst meldet Lean dort `unsolved goals`. Das macht Beweise übersichtlich und Fehler leicht zu
finden. Getippt wird `·` in VS Code als `\.`.

### `decide`

Für Aussagen, die Lean **durch Ausrechnen entscheiden** kann, etwa `0 < 25`, `2 + 2 = 5` oder
`gesamtpreis meinEinkauf ≤ 500`. Lean berechnet `true` oder `false`:

- `true`: Daraus wird ein Beweis gebaut.
- `false`: Fehler mit der Meldung *„Tactic `decide` proved that the proposition … is false“*.
  So entsteht der Fehler in Step1 und Step2 bei absichtlich falschen Aussagen.

**Grenze:** `decide` funktioniert nur, wenn ein endliches Prüfverfahren existiert (eine
`Decidable`-Instanz). Eine Aussage über **alle** natürlichen Zahlen wie `∀ n : Nat, n + 0 = n`
lässt sich nicht durchrechnen. Dann scheitert `decide` mit *„failed to synthesize Decidable …“*,
und man braucht einen echten Beweis, zum Beispiel per Induktion.

### `induction n with`: Beweis durch vollständige Induktion

**Wann:** Eine Aussage soll für **alle** `n : Nat` gelten, und `decide` oder `rfl` reichen nicht,
weil man nicht unendlich viele Fälle durchrechnen kann.

**Was passiert:** Der Beweis zerfällt in einen Fall pro Konstruktor von `Nat`:

```lean
induction n with
| zero => …          -- Basisfall:          Ziel mit 0 statt n
| succ n ih => …     -- Induktionsschritt:  Ziel mit n + 1 statt n,
                     --                     dazu ih : Aussage für n
```

Im Fall `succ` legt Lean die **Induktionsannahme** automatisch als Hypothese `ih` in den
Kontext. Den Namen wählt man selbst. Im Infoview sieht das in Step4 so aus:

```text
case succ
n : Nat
ih : double n = n + n
⊢ double (n + 1) = n + 1 + (n + 1)
```

**Mathematisch:** genau das Induktionsprinzip. „Gilt die Aussage für 0, und folgt sie für `n + 1`
aus der für `n`, dann gilt sie für alle `n`.“ Die Fälle heißen `zero`/`succ`, weil sie den
Konstruktoren `Nat.zero` und `Nat.succ` entsprechen. Induktion ist strukturell dasselbe wie
Rekursion mit Pattern Matching.

### `rw [h]`: Gleiches durch Gleiches ersetzen

**Wann:** Man hat eine Gleichung `h : a = b` (Annahme, Lemma oder Definition) und will im Ziel
`a` durch `b` ersetzen.

**Was passiert:** Jedes Vorkommen der linken Seite im Ziel wird durch die rechte Seite ersetzt.
Danach versucht `rw` das Ziel mit `rfl` zu schließen. Sind beide Seiten jetzt gleich, ist der
Beweis fertig.

```text
vorher:                                rw [ih]          nachher:
ih : double n = n + n                  ─────▶           ih : double n = n + n
⊢ (double n).succ.succ = …                              ⊢ (n + n).succ.succ = …
```

In Step4 wird `rw` mit drei Arten von Gleichungen benutzt:

| Aufruf               | Gleichung kommt aus     | Wirkung im Ziel                          |
|----------------------|-------------------------|------------------------------------------|
| `rw [double]`        | Definition von `double` | `double (n + 1)` → `succ (succ (double n))` |
| `rw [ih]`            | Induktionsannahme       | `double n` → `n + n`                     |
| `rw [Nat.succ_add]`  | Lemma der Bibliothek    | `succ n + m` → `succ (n + m)`            |

**Fehlerfall:** Kommt die linke Seite im Ziel nicht vor, meldet Lean, dass das Muster nicht
gefunden wurde. Mit `rw [← h]` ersetzt man in die andere Richtung, also `b` durch `a`.

---

## 3. Beweisterme

### `rfl`

Beweist Gleichungen der Form `a = a` („Reflexivität“). Das Besondere: Lean darf beide Seiten
vorher **ausrechnen**. `mitPfand preisMilch = 144` gilt deshalb per `rfl`, denn
`mitPfand preisMilch` rechnet sich zu `119 + 25` und dann zu `144` aus. Danach stehen auf beiden
Seiten dieselben Werte.

`rfl` klappt nur, wenn die Gleichheit durch bloßes Ausrechnen der Definitionen sichtbar wird.
Deshalb gelten auch `gesamtpreis_leer` und `gesamtpreis_cons` per `rfl`: Sie sind wörtlich die
beiden Zeilen der Definition. Für `x + y = y + x` mit Variablen reicht Ausrechnen nicht, dafür
braucht man Lemmata oder Induktion.

`rfl` gibt es als Term (`:= rfl`) und als gleichnamige Taktik (`· rfl` in Step3, Basisfall in
Step4). Beide tun dasselbe.

### `fun x => …`

Eine **anonyme Funktion** (Lambda). `fun preis => preis + 25` ist dieselbe Funktion wie
`mitPfand`, nur ohne Namen. In Beweisen ist `fun` der Term für „Angenommen …“, also das
Gegenstück zu `intro`. `fun hp _hq => hp` nimmt zwei Beweise entgegen und gibt den ersten zurück.

### `And.intro`, `⟨_, _⟩`, `.1` / `.2`, `.left` / `.right`

Ein Beweis von `P ∧ Q` ist ein **Paar** aus einem Beweis von `P` und einem von `Q`.

- **Bauen:** `And.intro hp hq` oder kurz `⟨hp, hq⟩`. Die spitzen Klammern sind eine Kurzform für
  den einzigen Konstruktor des erwarteten Typs. Getippt werden sie als `\<` und `\>`.
- **Zerlegen:** Aus `h : P ∧ Q` erhält man `h.left : P` und `h.right : Q`, kurz `h.1` und `h.2`.

### Lemmata anwenden

Ein bewiesener Satz ist eine Funktion und wird wie eine Funktion aufgerufen. Step2 benutzt

```lean
Nat.lt_add_of_pos_right : 0 < k → n < n + k
```

Gibt man diesem Lemma einen Beweis von `0 < 25`, liefert es einen Beweis von
`preis < preis + 25`. Die Werte für `n` und `k` muss man nicht angeben. Lean ermittelt sie aus
dem Ziel, denn sie sind *implizite* Argumente (siehe `@` in [Abschnitt 7](#7-kleinere-syntax)).
Genauso wird in Step3 `und_komm_term (119 + 25 = 144) (45 < 249) milch_und_apfel` benutzt.
In Step4 werden die Lemmata `Nat.succ_add` und `Nat.add_succ` nicht aufgerufen, sondern mit
`rw` als Gleichungen zum Umschreiben verwendet.

---

## 4. Logik und Typen

### `Prop` und `Type`

`Prop` ist der Typ aller **Aussagen**. `Type` ist der Typ der „normalen“ Datentypen wie `Nat`
oder `List Artikel`. `#check Nat` liefert `Nat : Type`, `#check (2 + 2 = 5)` liefert `: Prop`.
Eine Aussage zu bilden heißt nicht, dass sie wahr ist. Wahr ist sie erst, wenn es einen Term
dieses Typs gibt, also einen Beweis.

### `→`

Bei Datentypen ist `A → B` ein Funktionstyp, bei Aussagen eine Implikation. Beides ist dasselbe
(**Curry–Howard**): Ein Beweis von `P → Q` ist eine Funktion von Beweisen von `P` zu Beweisen
von `Q`. Der Pfeil ist rechtsassoziativ, `P → Q → P` bedeutet also `P → (Q → P)`. `->` ist die
ASCII-Schreibweise.

### `∀`

`∀ preis : Nat, preis < mitPfand preis` ist die Aussage „für jeden Preis gilt …“. Ein Beweis ist
eine Funktion, die **jedes** `preis` entgegennimmt und einen Beweis für genau diesen Preis
liefert. Parameter vor dem Doppelpunkt sind eine Kurzform dafür:

```lean
theorem pfand_macht_teurer (preis : Nat) : preis < mitPfand preis
-- hat den Typ  ∀ (preis : Nat), preis < mitPfand preis
```

### `∧`

„und“. Ein induktiver Typ mit dem einzigen Konstruktor `And.intro`, siehe
[Abschnitt 3](#andintro-__-1--2-left--right).

### `=`, `<`, `≤`

Vergleiche, die eine **Aussage** (`Prop`) liefern und keinen Wahrheitswert. `≤` wird als `\le`
getippt.

### `Bool` vs. `Prop`

`true`/`false` sind Werte vom Typ `Bool`, also Daten, mit denen ein Programm rechnet. Eine `Prop`
ist eine Aussage, die man beweisen muss. Deshalb ist `#check (true : Nat)` in Step1 ein
Typfehler: `true` ist ein `Bool` und kein `Nat`. `decide` verbindet beide Welten, indem es eine
Aussage durch eine `Bool`-Rechnung entscheidet.

---

## 5. Deklarationen

### `def`

Definiert eine Konstante oder Funktion mit Namen, Typ und Wert. Rekursive Definitionen wie
`double`, `pfandZurueck` oder `gesamtpreis` akzeptiert Lean nur, wenn es sieht, dass sie immer
terminieren. Das ist hier automatisch der Fall, weil jeder rekursive Aufruf ein kleineres
Argument bekommt (`n` statt `n + 1`, `rest` statt `a :: rest`).

### `theorem`

Wie `def`, aber für **Aussagen**: Der Typ ist eine `Prop`, und der Wert ist der Beweis. Der Name
macht den Satz später wiederverwendbar.

### `example`

Wie `theorem`, aber **ohne Namen**. Lean prüft den Beweis, man kann sich aber nicht mehr darauf
beziehen. Das eignet sich für Demonstrationen.

### `inductive … where`

Definiert einen neuen Datentyp durch die Liste seiner **Konstruktoren**. Jede Zeile `| milch`
ist ein Konstruktor. Weitere Werte als die so gebauten gibt es nicht. Konstruktoren können
Argumente haben, `Nat.succ` hat zum Beispiel eines.

### `deriving Repr`

Lässt Lean automatisch eine Textdarstellung (`Repr`) für den Typ erzeugen, damit `#eval` Werte
wie `[Artikel.milch, …]` anzeigen kann. In Lean `v4.35.0` würde `#eval` sich eine solche
Darstellung notfalls selbst erzeugen. Die Zeile macht es aber explizit und ist üblich.

### `namespace X` … `end X`

Fasst Namen zusammen. Innerhalb von `namespace Einkauf` heißt die Funktion einfach `preis`, von
außen `Einkauf.preis`. So kollidieren gleiche Namen in verschiedenen Dateien nicht.

---

## 6. Pattern Matching und Konstruktoren

### `match … with` und `|`

Unterscheidet Fälle danach, **mit welchem Konstruktor** ein Wert gebaut wurde:

```lean
def double (n : Nat) : Nat :=
  match n with
  | 0     => 0
  | n + 1 => double n + 2
```

Jede Zeile `| Muster => Ergebnis` behandelt einen Fall. Lean prüft, dass **alle** Konstruktoren
abgedeckt sind. Fehlt einer, gibt es den Fehler *Missing cases*. Die Kurzform ohne `match`, mit
den `|`-Zeilen direkt unter der Signatur, wie bei `preis` oder `pfandZurueck`, bedeutet genau
dasselbe.

### Konstruktoren von `Nat`: `0` / `n + 1`

`Nat.zero` (geschrieben `0`) und `Nat.succ n` (geschrieben `n + 1`). Im Muster `n + 1` wird `n`
neu gebunden: Ist das Argument `3`, dann ist `n = 2`.

### Konstruktoren von `List`: `[]` / `::`

`[]` (`List.nil`) ist die leere Liste. `a :: rest` (`List.cons`) ist das Element `a` vor der
Liste `rest`. `[x, y, z]` ist nur eine Kurzform für `x :: y :: z :: []`.

---

## 7. Kleinere Syntax

| Zeichen        | Bedeutung |
|----------------|-----------|
| `(e : T)`      | Typangabe: „`e` soll den Typ `T` haben“. Lean prüft das, siehe `(true : Nat)` in Step1. |
| `_hq`          | Ein Name mit führendem `_` markiert einen absichtlich unbenutzten Parameter. Ohne `_` gäbe es eine Linter-Warnung. |
| `_`            | Platzhalter: Lean soll den Wert selbst herausfinden, oder im Muster „egal welcher Wert“. |
| `.milch`       | Kurzform für `Artikel.milch`. Lean ergänzt den Namensraum aus dem erwarteten Typ. |
| `@f`           | Zeigt bzw. verlangt **alle** Argumente von `f`, auch die impliziten in `{…}`. `#check @And.intro` zeigt deshalb `∀ {a b : Prop}, a → b → a ∧ b`. |
| `(f)` in `#check` | `#check (mitPfand)` zeigt den reinen Funktionstyp `Nat → Nat` statt der Signatur mit Parameternamen. |
| `/- … -/`      | Mehrzeiliger Kommentar. |
| `/-! … -/`     | Modul-Dokumentation: Kommentar mit Markdown für Überschriften und Erklärtexte. |

---

## 8. Befehle für den Editor

Diese Befehle erzeugen nur Ausgaben im Infoview und beweisen nichts.

| Befehl        | Zweck |
|---------------|-------|
| `#check e`    | Zeigt den **Typ** von `e`. Bei Aussagen heißt das nur, dass sie korrekt gebildet sind, nicht, dass sie wahr sind. |
| `#eval e`     | **Rechnet** `e` aus und zeigt das Ergebnis. Ein `#eval` ist ein einzelnes Beispiel und kein Beweis für alle Fälle. |
| `#print name` | Zeigt die vollständige Definition. Bei einem Taktikbeweis sieht man so den **erzeugten Beweisterm** (siehe Step3). |
