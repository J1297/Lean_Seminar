# Seminar Programmverifikation mit LEAN4

## Gemeinsamer Rahmen
Vorausgesetzt werden grundlegende Programmierkenntnisse sowie Vertrautheit mit mathematischen Aussagen und
Induktion. Für Thema 1 sind keine Lean-Kenntnisse nötig. Für die Themen 2 und 3 sollen Sie sich zuvor die in Thema
1 genannten Grundlagen aneignen; eine Abgabe aus Thema 1 ist dafür nicht erforderlich.
Als Vorschlag für die Seminarorganisation gelten pro Thema ein Vortrag von 20 Minuten mit etwa 5 Minuten LiveDemonstration, eine Ausarbeitung (bzw. Dokumentation) in PDF oder Markdown und ein ausführbares Lean-Projekt.
Die optionalen Erweiterungen gehören nicht zum Pflichtumfang.

## Abgaben
- Vortragsfolien und ein Lean-Projekt (in GitHub) mit README. Dokumentieren Sie die verwendete Lean-Version
in lean-toolchain sowie alle Abhängigkeiten; bei externen Paketen gehört auch die zugehörige Versionsbindung
zur Abgabe.
- Beschreiben Sie im README den Aufbau und die Befehle zum Prüfen des Projekts, etwa lake build. Binden Sie
alle abgegebenen Beweisdateien in das Build-Ziel ein. Die Abgabe muss ohne offene Beweisziele, sorry, admit
oder selbst eingeführte Axiome als Ersatz für Beweise prüfen.
- Kommentieren Sie zentrale Definitionen und Beweisideen. Geben Sie an, welche Teile selbst erarbeitet, aus
Literatur übernommen oder mit Werkzeugen erzeugt wurden. Erklären können müssen Sie alle abgegebenen
Beweise.
- Unterscheiden Sie Beispielauswertungen mit #eval von allgemeinen Korrektheitsbeweisen. Erläutern Sie, welche
Aussage bewiesen ist und welche Annahmen oder Modellgrenzen bestehen.
Bewertungsschwerpunkte sind die Präzision der Spezifikation, die Vollständigkeit der Pflichtbeweise, die Erklärung
der zentralen Beweisschritte und die Reproduzierbarkeit. Ein kleiner, vollständig erklärter Beweis ist einer
umfangreichen Sammlung unverstandener Automatisierung vorzuziehen.

## Gemeinsame Materialien
[M1] Theorem Proving in Lean 4, Jeremy Avigad, Leonardo de Moura, Soonho Kong und Sebastian Ullrich mit
Beiträgen der Lean Community. Für dieses Seminar besonders die Kapitel Propositions and Proofs, Tactics, Inductive
Types sowie Induction and Recursion. https://lean-lang.org/theorem_proving_in_lean4/
[M2] Functional Programming in Lean, David Thrane Christiansen. Für den Einstieg Getting to Know Lean sowie die
beiden Interludes zu Propositionen und Beweisen beziehungsweise Taktiken und Induktion. https://leanlang.org/functional_programming_in_lean/
[M3] The Lean Language Reference. Nachschlagewerk zu Definitionen, Taktiken, Simplifier und Build-Werkzeugen;
kein Ersatz für ein Einstiegstutorial. https://lean-lang.org/doc/reference/latest/
[M4] Offizielle Installationsanleitung mit VS Code und Lean-4-Erweiterung. https://lean-lang.org/install/
Die Online-Materialien werden fortgeschrieben. Verwenden Sie im Projekt eine festgelegte Lean-4-Version und
achten Sie bei Beispielen auf die passende Version; Lean-3-Beispiele lassen sich nicht unverändert übernehmen. Die
Pflichtaufgaben lassen sich ohne Mathlib bearbeiten.


## Thema 1: Einführung in Lean 4 und interaktives Beweisen
### Gegenstand und Lernziele
Erarbeiten Sie eine Einführung, die Mitstudierende vom Lesen einer einfachen Lean-Definition zum Verstehen eines
kleinen Induktionsbeweises führt. Zeigen Sie Lean sowohl als funktionale Programmiersprache als auch als
interaktiven Theorembeweiser.
Nach der Bearbeitung sollen Sie Typen und Propositionen unterscheiden, die Curry–Howard-Korrespondenz an
Beispielen erklären, rekursive Funktionen definieren und Beweise im Editor schrittweise entwickeln können. Sie
sollen erläutern können, wie Taktiken Beweisterme erzeugen und welche Rolle der prüfende Kernel spielt.

### Konkrete Arbeitsaufträge
1. Richten Sie ein kleines Lean-Projekt ein. Zeigen Sie #check und #eval sowie die Anzeige von Kontext und aktuellem
Beweisziel im Editor. Erklären Sie den Unterschied zwischen einem Typfehler, einem offenen Beweisziel und einem
falsch behaupteten Satz.
2. Erklären Sie an Nat, Nat → Nat und P → Q die Begriffe Typ, Funktion, Proposition und Beweis. Erläutern Sie
Konstruktoren und Pattern Matching anhand von Nat oder List. Eine Einführung in Universen und abhängige Typen
im Detail ist nicht erforderlich.
3. Beweisen Sie die beiden untenstehenden Aussagen einmal durch einen Beweisterm und einmal mit Taktiken.
Erklären Sie insbesondere fun beziehungsweise intro, constructor und exact.
4. Definieren Sie die Funktion double durch Rekursion. Berechnen Sie double 0 und double 3. Beweisen Sie double n
= n + n für beliebiges n durch Induktion über n. Erklären Sie Basisfall, Induktionsannahme und Induktionsschritt
sowie eingesetzte Rechenlemmata.
5. Demonstrieren Sie rw und simp an einem überschaubaren Gleichheitsziel. Zeigen Sie an einem bewusst
unvollständigen Beweis, wie der Editor die verbleibende Aufgabe sichtbar macht; die abgegebene Fassung muss
vollständig sein.
Vorgegebene Aussagen und Funktionsdefinition
-- Jeweils als Termbeweis und als Taktikbeweis bearbeiten:
-- (P Q : Prop) : P → Q → P
-- (P Q : Prop) : P ∧ Q → Q ∧ P
def double : Nat → Nat
 | 0 => 0
 | Nat.succ n => Nat.succ (Nat.succ (double n))
-- Zu beweisen: ∀ n : Nat, double n = n + n
Die kommentierten Aussagen sind Aufgaben, keine bereits geprüften Theoremdeklarationen. Vergeben Sie für Ihre
verschiedenen Beweisvarianten unterschiedliche Namen.


### Erwartete Ergebnisse und Demonstration
Die Dokumentation soll einen lesbaren Weg vom informellen Argument zum formalen Beweis darstellen. Geben Sie
zu jedem Beispiel die Aussage in Worten und erklären Sie bei mindestens einem Beweis jeden Schritt. In der LiveDemonstration führen Sie eine Auswertung aus, entwickeln einen kurzen logischen Beweis und erläutern den
Induktionsbeweis anhand der sichtbaren Beweisziele.
Abgrenzung und mögliche Erweiterungen
Pflichtumfang sind die zwei logischen Aussagen in je zwei Varianten und der Induktionsbeweis zu double. Keine
vollständige Einführung in Typentheorie, Taktikprogrammierung oder Mathlib ist nötig. Optional können Sie einen
weiteren Satz über Nat oder einen sehr kurzen Ausblick auf formalisierte Mathematik und KI-gestützte Beweissuche
ergänzen. Dieser Ausblick ersetzt keinen Pflichtbeweis.

## Literatur und Materialien
Nutzen Sie [M1], Kapitel 2 bis 5 sowie 7 und 8, selektiv für die genannten Begriffe und Beweistechniken. [M2] hilft
beim Einstieg in Rekursion und Pattern Matching. Verwenden Sie [M3] gezielt zum Nachschlagen von intro, exact,
constructor, rw, simp und induction; [M4] unterstützt die Einrichtung.