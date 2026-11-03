-- 1. Datentypen, Funktionen und Beweise

-- 1.1 Datentyp Nat: natürliche Zahl
#check Nat

-- 1.2 Funktion: Transformiert gegebene Eingabe
def double : Nat → Nat :=
  fun n => n * 2

-- 1.3 Proposition: Aussage über einen Datentyp
-- In Lean: Propositionen sind Typen.
-- Beweise sind Programme, die diese Typen erfüllen.
variable (P Q : Prop)
#check (P → Q)  -- "If P is true, then Q is true"

-- 4. Beweise: Programme, welche Propositionen und somit den Datentyp P erfüllen.
-- Beispiel: Identitätsbeweis für Proposition P
theorem id_proof : P → P :=
  fun (hp : P) => hp


-- 2. Konstruktoren und Pattern-Matching

-- Konstruktor für Nat lediglich über 2 Regeln:
--   1. Nat.zero   (0)
--   2. Nat.succ n (n + 1)

-- Pattern Matching: "Dekonstruierung" eines Wertes,
-- um auf seine Bestandteile zuzugreifen.
def isZero : Nat → Bool
  | 0          => true   -- Base Constructor (zero) [REGEL 1]
  | Nat.succ _ => false  -- Inductive Constructor (succ) [REGEL 2]

-- Example evaluation:
#eval isZero 0  -- evaluates to true
#eval isZero 3  -- evaluates to false
