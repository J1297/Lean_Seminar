import Mathlib

/-!
# Arbeitsauftrag 1: Editor- und Auswertungsbefehle
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

-- Idee:
-- Pattern-Matching auf n:
--  - Wenn n = 0, dann ist double n = 0
--  - Wenn n > 0, split auf n, rekursiver call mit n + 2.
-- Ausführung für double 3:
-- 3 = (2 + 1) => double 2 {+ 2}
-- 2 = (1 + 1) => double 1 {+ 2 {+ 2}}
-- 1 = (0 + 1) => double 0 {+ 2 {+ 2 {+ 2}}}
-- Effektiv: n * 1 addieren um zu verdoppeln

#check double
#eval double 0
#eval double 3

/-!
# Arbeitsauftrag 1: Fehlertypen
-/

-- Typfehler
#check 2 + (3 = 3)
#eval 2 + (3 = 3) -- Fehler: Typen stimmen nicht überein

-- offenes Beweisziel:
theorem demo (x y : ℕ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  rfl


-- falscher Satz:
theorem worth_a_try : 2 + 2 = 5 := by
  rfl  -- Taktik schlägt fehl!
