/-!
# Arbeitsauftrag 3: Termbeweise und Taktikbeweise

Zwei logische Aussagen, jeweils zweimal bewiesen:

* als **Termbeweis**: Wir schreiben den Beweis direkt als Programm hin (wie in Step2).
* als **Taktikbeweis**: Wir bauen den Beweis Schritt für Schritt mit `by …`;
  der Infoview zeigt nach jedem Schritt Kontext.
-/

namespace Logik

/-! ## Aussage 1: `P → Q → P`

In Worten: „Wenn `P` gilt, dann gilt `P` auch unter der zusätzlichen Annahme `Q`.“
Alltag: „Wenn ich bezahlt habe, dann habe ich bezahlt, auch wenn ich zusätzlich einen
Bon bekommen habe.“

### 1a) Termbeweis mit `fun`

`fun hp hq => hp` ist eine Funktion mit zwei Argumenten,
`hp : P` und `hq : Q`. Sie gibt einfach `hp` zurück, das ist bereits ein Beweis von `P`.
`hq` wird nicht gebraucht, deshalb heißt er `_hq`. Der Unterstrich sagt Lean,
dass der Parameter absichtlich unbenutzt ist.

Als Programm ist das die „konstante Funktion“: Sie gibt immer ihr erstes Argument zurück.
-/

theorem konst_term (P Q : Prop) : P → Q → P :=
  fun hp _hq => hp

/-!
### 1b) Taktikbeweis mit `intro` und `exact`

* `intro h` ist das Gegenstück zu `fun h => …`: Ist das Ziel eine Implikation `A → B`,
  wird `h : A` in den Kontext aufgenommen und das Ziel wird zu `B`.
* `exact t` schließt das Ziel mit einem Term `t`, dessen Typ **genau** das Ziel ist.
  Passt der Typ nicht, meldet Lean einen Fehler.
-/

theorem konst_taktik (P Q : Prop) : P → Q → P := by
  -- Kontext: P Q : Prop                  Ziel: ⊢ P → Q → P
  intro hp
  -- Kontext: P Q : Prop, hp : P          Ziel: ⊢ Q → P
  intro _hq
  -- Kontext: …, hp : P, _hq : Q           Ziel: ⊢ P
  exact hp
  -- keine Ziele mehr: Beweis fertig

/-! ## Aussage 2: `P ∧ Q → Q ∧ P`

In Worten: „Wenn `P` und `Q` gelten, dann gelten auch `Q` und `P`.“
Die Reihenfolge bei „und“ spielt keine Rolle (Kommutativität).
Alltag: „Wenn ich bezahlt *und* einen Bon bekommen habe, dann habe ich einen Bon bekommen
*und* bezahlt.“

`P ∧ Q` ist ein induktiver Typ mit genau einem Konstruktor (vgl. Step2, Abschnitt 5):

    And.intro : P → Q → P ∧ Q

Ein Beweis von `P ∧ Q` ist also ein **Paar** aus einem Beweis von `P` und einem von `Q`.
Aus `h : P ∧ Q` holt man die Teile heraus mit

* `h.left  : P`   (kurz `h.1`)
* `h.right : Q`   (kurz `h.2`)
-/

/-!
### 2a) Termbeweis

Wir nehmen `h : P ∧ Q` entgegen und bauen mit `And.intro` ein neues Paar,
diesmal in umgekehrter Reihenfolge.
-/

theorem und_komm_term (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => And.intro h.right h.left

/-!
### 2b) Taktikbeweis mit `intro`, `constructor` und `exact`

Hier wird jeder Schritt erklärt.

* `constructor` wendet den passenden Konstruktor des Ziels an. Beim Ziel `Q ∧ P`
  ist das `And.intro`. Es fehlen noch dessen zwei Argumente, deshalb entstehen
  **zwei neue Ziele**: `⊢ Q` und `⊢ P`.
* Die Punkte `·` fokussieren jeweils auf eines dieser Ziele.
-/

theorem und_komm_taktik (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- Kontext: P Q : Prop                    Ziel: ⊢ P ∧ Q → Q ∧ P
  intro h
  -- Kontext: P Q : Prop, h : P ∧ Q         Ziel: ⊢ Q ∧ P
  constructor
  -- zwei Ziele:  (1) ⊢ Q    (2) ⊢ P
  · -- Ziel (1): ⊢ Q.   h.right hat den Typ Q.
    exact h.right
  · -- Ziel (2): ⊢ P.   h.left hat den Typ P.
    exact h.left


/-! ## Taktiken erzeugen Beweisterme

Mit `#print` sieht man, welchen Term die Taktiken tatsächlich gebaut haben.
Das ist im Wesentlichen derselbe Term wie im Termbeweis: `intro` wurde zu `fun`,
`constructor` zu `And.intro`, und `exact` hat die Argumente eingesetzt.
Nur dieser Term wird vom Kernel geprüft, nicht die Taktiken selbst.
-/

#print konst_taktik
#print und_komm_taktik

end Logik
