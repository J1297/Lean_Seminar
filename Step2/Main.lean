-- # Arbeitsauftrag 2: Typ, Funktion, Proposition, Beweis

namespace Einkauf

def preisMilch : Nat := 119   -- 1,19 €

#check preisMilch
#eval preisMilch

-- def preisFalsch : Nat := "1,19 €"

-- ## 2. Funktion: `Nat → Nat`

def mitPfand (preis : Nat) : Nat :=
  preis + 25

#check mitPfand               -- mitPfand (preis : Nat) : Nat   (Signatur)
#check (mitPfand)             -- mitPfand : Nat → Nat           (reiner Funktionstyp)
#eval mitPfand preisMilch     -- 144
#eval mitPfand 0              -- 25


/-! ## 3. Proposition

Eine **Proposition** ist eine Aussage. In Lean ist jede Aussage ein Typ,
und zwar vom Typ `Prop`.

Wichtig: `#check` zeigt nur, dass die Aussage *sinnvoll gebildet* ist,
nicht, dass sie *wahr* ist. Auch eine falsche Aussage ist eine Proposition.
-/

#check (mitPfand preisMilch = 144)     -- : Prop   (wahr)
#check (mitPfand preisMilch = 100)     -- : Prop   (falsch, aber eine Aussage)
#check (∀ preis : Nat, preis < mitPfand preis)   -- : Prop


/-! ## 4. Beweis

Ein **Beweis** einer Proposition `P` ist ein Wert vom Typ `P`.
Kann man einen solchen Wert angeben, ist die Aussage bewiesen.
Der Lean-Kernel prüft, dass der Wert wirklich den behaupteten Typ hat.

### 4.1 Beweis einer konkreten Aussage
-/

theorem milch_mit_pfand : mitPfand preisMilch = 144 := rfl

-- explizit falsch:
theorem milch_mit_pfand_f : mitPfand preisMilch = 100 := by decide

-- Unterschied zu `#eval`:
--   `#eval mitPfand preisMilch` rechnet einmal ein Beispiel aus.
--   `milch_mit_pfand` ist ein geprüfter Satz, auf den man später verweisen kann.

-- Eine falsche Aussage lässt sich nicht beweisen. (Zum Ausprobieren einkommentieren.)

/-!
### 4.2 Allgemeine Aussage über alle Preise

„Mit Pfand ist *jeder* Artikel teurer als ohne Pfand.“
Das ist kein Beispiel mehr, sondern gilt für alle `preis : Nat`.
Dafür reicht kein `#eval` mehr, wir brauchen einen Beweis.

Der Beweis benutzt das Rechenlemma aus der Standardbibliothek
`Nat.lt_add_of_pos_right : 0 < k → n < n + k`
mit `k = 25`. Die Voraussetzung `0 < 25` rechnet `by decide` aus.
-/

theorem pfand_macht_teurer (preis : Nat) : preis < mitPfand preis :=
  Nat.lt_add_of_pos_right (by decide)

/-!
### 4.3 Implikation `P → Q`: Beweise sind Funktionen

Jetzt abstrakte Aussagen aus dem Alltag an der Kasse:

* `Bezahlt`     – „Ich habe an der Kasse bezahlt.“
* `BonErhalten` – „Ich habe einen Kassenbon bekommen.“
* `Umtausch`    – „Ich darf die Ware umtauschen.“

`Bezahlt → BonErhalten` ist die Aussage „Wenn ich bezahlt habe, bekomme ich einen Bon“.

Ein Beweis von `P → Q` ist eine **Funktion**: Sie bekommt einen Beweis von `P`
und liefert einen Beweis von `Q`. Das ist genau dasselbe wie bei
`mitPfand : Nat → Nat`, nur dass jetzt Beweise statt Zahlen übergeben werden.
-/

#check ∀ (Bezahlt BonErhalten : Prop), Bezahlt → BonErhalten

-- Modus ponens: Aus der Kassenregel und der Tatsache, dass ich bezahlt habe,
-- folgt, dass ich einen Bon bekomme.
-- regel: Typ Implikation, Beweis von bezahlt => BonErhalten
theorem bon_nach_bezahlung (Bezahlt BonErhalten : Prop)
    (regel : Bezahlt → BonErhalten) (hb : Bezahlt) : BonErhalten :=
  regel hb
-- Eigentlicher Beweis: Unter Annahme hb : Bezahlt,
-- gilt mit `regel` hb, dass wir auch einen Bon erhalten haben

-- Zwei Regeln hintereinander:
--   Wer bezahlt, bekommt einen Bon.   (h1 : Bezahlt → BonErhalten)
--   Wer einen Bon hat, darf umtauschen. (h2 : BonErhalten → Umtausch)
-- Also: Wer bezahlt, darf umtauschen.
-- Der Beweis: Funktion `fun hb => ...`, die zuerst `h1`, dann `h2` anwendet,
-- also eine Hintereinanderausführung von Funktionen.
theorem umtausch_nach_bezahlung (Bezahlt BonErhalten Umtausch : Prop)
    (h1 : Bezahlt → BonErhalten) (h2 : BonErhalten → Umtausch) :
    Bezahlt → Umtausch :=
  fun hb => h2 (h1 hb)


/-! ## 5. Konstruktoren und Pattern Matching

Ein induktiver Typ wird durch seine **Konstruktoren** festgelegt:
Jeder Wert des Typs entsteht durch genau einen dieser Konstruktoren.
**Pattern Matching** fragt ab, mit welchem Konstruktor ein Wert gebaut wurde,
und behandelt jeden Fall einzeln.

### 5.1 Eigener Typ: das Sortiment

Der einfachste Fall: Konstruktoren ohne Argumente (eine Aufzählung).
-/

inductive Artikel where
  | milch
  | brot
  | apfel
  deriving Repr

#check Artikel.milch          -- Artikel.milch : Artikel

-- Pattern Matching: für jeden Konstruktor genau ein Fall.
-- Fehlt ein Fall, meldet Lean einen Fehler ("missing cases").
def preis : Artikel → Nat
  | .milch => 119
  | .brot  => 249
  | .apfel => 45
-- | .neu  => 99

#eval preis .brot

/-!
### 5.2 `Nat`: zwei Konstruktoren

`Nat` ist ebenfalls ein induktiver Typ, mit genau zwei Konstruktoren:

* `Nat.zero`        – die Zahl `0`
* `Nat.succ n`      – der Nachfolger von `n`, also `n + 1`

Jede natürliche Zahl ist so gebaut, z. B. `3 = succ (succ (succ zero))`.
-/

#check Nat.zero
#check (Nat.succ)
#eval Nat.succ (Nat.succ (Nat.succ Nat.zero))

/-!
Alltag: Am Pfandautomaten gibt jede Flasche 25 Cent zurück.
Die Funktion matcht auf die beiden Konstruktoren von `Nat`:

* keine Flasche (`0`)           → 0 Cent
* eine Flasche mehr (`n + 1`)   → Pfand für `n` Flaschen plus 25 Cent

Das Muster `n + 1` ist in Lean eine Schreibweise für `Nat.succ n`.
Da `n` kleiner ist als `n + 1`, endet die Rekursion immer.
-/

def pfandZurueck : Nat → Nat
  | 0     => 0
  | n + 1 => pfandZurueck n + 25

#eval pfandZurueck 0          -- 0
#eval pfandZurueck 3          -- 75

/-!
Auswertung von `pfandZurueck 3` Schritt für Schritt:

    pfandZurueck 3
  = pfandZurueck 2 + 25
  = (pfandZurueck 1 + 25) + 25
  = ((pfandZurueck 0 + 25) + 25) + 25
  = ((0 + 25) + 25) + 25
  = 75
-/

/-!
### 5.3 `List`: der Einkaufswagen

Auch `List α` hat genau zwei Konstruktoren:

* `[]`        (`List.nil`)  – der leere Einkaufswagen
* `a :: rest` (`List.cons`) – Artikel `a` vorne, dahinter der Rest

Die Schreibweise `[.milch, .brot]` ist nur eine Abkürzung für
`.milch :: .brot :: []`.
-/

def meinEinkauf : List Artikel := [.milch, .brot, .apfel]

#check (List.nil : List Artikel)                       -- leerer Wagen
#check (Artikel.milch :: Artikel.brot :: [])           -- : List Artikel
#eval meinEinkauf

-- Der Gesamtpreis an der Kasse: Pattern Matching auf die beiden Listen-Konstruktoren.
--   leerer Wagen      → 0 Cent
--   Artikel + Rest    → Preis des Artikels plus Gesamtpreis des Rests
def gesamtpreis : List Artikel → Nat
  | []        => 0
  | a :: rest => preis a + gesamtpreis rest

#eval gesamtpreis []          -- 0
#eval gesamtpreis meinEinkauf -- 413  (= 119 + 249 + 45)

-- Die beiden Fälle der Definition gelten auch als Sätze; Lean bestätigt sie per `rfl`:
theorem gesamtpreis_leer : gesamtpreis [] = 0 := rfl

theorem gesamtpreis_cons (a : Artikel) (rest : List Artikel) :
    gesamtpreis (a :: rest) = preis a + gesamtpreis rest := rfl
