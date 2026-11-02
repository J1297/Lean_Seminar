/-!
# Schritt 1: Ein kleiner Lean-Versuch

Diese Datei zeigt die grundlegenden Editor- und Auswertungsbefehle.
Die eigentlichen Beweise folgen in den nächsten Arbeitsschritten.
-/

-- `#check` fragt den Typ eines Ausdrucks ab.
#check Nat
#check Nat -> Nat
#check (fun n : Nat => n + 1)

-- `#eval` wertet einen berechenbaren Ausdruck aus.
#eval (2 + 3 : Nat)

-- Eine kleine rekursive Funktion als erstes ausführbares Beispiel.
def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => double n + 2

#check double
#eval double 0
#eval double 3

-- Im Editor zeigt Lean innerhalb des Beweises Kontext und aktuelles Ziel an.
-- Beim Tippen nach `by` ist das Ziel `n = n` sichtbar; `rfl` schließt es.
example (n : Nat) : n = n := by
  rfl

-- Der Parameter `h` steht im Kontext und kann mit `exact` als Beweis benutzt werden.
example (p : Prop) (h : p) : p := by
  exact h
