/-!
# Arbeitsauftrag 4: Rekursion und Induktion mit `double`

Vorgegeben ist die Funktion `double`, die eine natürliche Zahl verdoppelt.
Zu zeigen ist: `∀ n : Nat, double n = n + n`.
-/

namespace Verdopplung

/-! ## Definition durch Rekursion

Pattern Matching auf die beiden Konstruktoren von `Nat` (vgl. Step2, Abschnitt 5.2):

* `0`            → `0`
* `Nat.succ n`   → zweimal der Nachfolger von `double n`, also `double n + 2`

Der rekursive Aufruf `double n` bekommt ein kleineres Argument als `Nat.succ n`,
deshalb terminiert die Rekursion.
-/

def double : Nat → Nat
  | 0 => 0
  | Nat.succ n => Nat.succ (Nat.succ (double n))

#eval double 0    -- 0
#eval double 3    -- 6

/-!
Auswertung von `double 3` Schritt für Schritt (`succ` steht für „+ 1“):

    double 3
  = succ (succ (double 2))
  = succ (succ (succ (succ (double 1))))
  = succ (succ (succ (succ (succ (succ (double 0))))))
  = succ (succ (succ (succ (succ (succ 0)))))
  = 6

Die beiden `#eval` sind nur **Beispiele**. Dass `double n = n + n` für **alle** `n` gilt,
kann man nicht durch Ausprobieren zeigen, denn es gibt unendlich viele `n`.
Dafür braucht man einen Beweis per Induktion.
-/

/-! ## Induktionsbeweis

### Informelles Argument

Wir zeigen `double n = n + n` durch Induktion über `n`.

* **Basisfall** `n = 0`:
  `double 0 = 0` nach Definition, und `0 + 0 = 0`. Beide Seiten sind gleich.

* **Induktionsschritt** von `n` auf `n + 1`:
  - **Induktionsannahme (IA):** `double n = n + n` gilt bereits für dieses `n`.
  - **Zu zeigen:** `double (n + 1) = (n + 1) + (n + 1)`.

        double (n + 1)
      = succ (succ (double n))      nach Definition von double
      = succ (succ (n + n))         nach IA
      = (n + 1) + (n + 1)           Rechenregeln der Addition (siehe unten)

Für den letzten Schritt brauchen wir zwei Rechenlemmata aus der Standardbibliothek.
Sie besagen, dass man ein `+ 1` aus einem Summanden nach außen ziehen darf:

* `Nat.succ_add : succ n + m = succ (n + m)`   (`+ 1` vom **linken** Summanden)
* `Nat.add_succ : n + succ m = succ (n + m)`   (`+ 1` vom **rechten** Summanden)

Damit gilt `(n + 1) + (n + 1) = succ (n + (n + 1)) = succ (succ (n + n))`.

### Formaler Beweis

Neue Taktiken:

* `induction n with` teilt den Beweis in die zwei Fälle `zero` und `succ`, je einen pro
  Konstruktor von `Nat`. Im Fall `succ` stellt Lean die Induktionsannahme als
  Hypothese `ih` in den Kontext.
* `rw [h]` (*rewrite*) ersetzt im Ziel die linke Seite der Gleichung `h` durch ihre
  rechte Seite. Sind danach beide Seiten des Ziels gleich, schließt `rw` das Ziel
  automatisch mit `rfl`.

Hinweis zum Infoview: Lean zeigt `Nat.succ n` als `n + 1` an. Beides ist derselbe Wert.
-/

theorem double_eq_add (n : Nat) : double n = n + n := by
  induction n with
  | zero =>
    -- Basisfall
    -- Ziel: ⊢ double 0 = 0 + 0
    -- Beide Seiten rechnen sich zu 0 aus.
    rfl
  | succ n ih =>
    -- Induktionsschritt
    -- Kontext: n : Nat, ih : double n = n + n      (Induktionsannahme)
    -- Ziel:    ⊢ double (n + 1) = n + 1 + (n + 1)
    rw [double]
    -- Definition von double angewendet (Fall `Nat.succ n`):
    -- Ziel:    ⊢ (double n).succ.succ = n + 1 + (n + 1)
    rw [ih]
    -- Induktionsannahme eingesetzt: double n wird zu n + n
    -- Ziel:    ⊢ (n + n).succ.succ = n + 1 + (n + 1)
    rw [Nat.succ_add]
    -- rechte Seite: (n + 1) + m  wird zu  succ (n + m)
    -- Ziel:    ⊢ (n + n).succ.succ = (n + (n + 1)).succ
    rw [Nat.add_succ]
    -- rechte Seite: n + (n + 1)  wird zu  succ (n + n)
    -- Ziel:    ⊢ (n + n).succ.succ = (n + n).succ.succ
    -- Beide Seiten sind gleich, `rw` schließt das Ziel mit `rfl`.

/-!
### Was ist bewiesen?

`double_eq_add` gilt für **jede** natürliche Zahl `n`. Der Kernel hat den Beweis geprüft.
Annahmen gibt es keine außer der Definition von `double` und den Rechenlemmata der
Standardbibliothek. Den Satz kann man wie eine Funktion auf ein konkretes `n` anwenden:
-/

#check double_eq_add 3    -- double_eq_add 3 : double 3 = 3 + 3

end Verdopplung
