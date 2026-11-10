# Lean_Seminar
Seminararbeit LEAN4 Einführung anhand eines Beispiels

Das Projekt verwendet Lean `v4.35.0` und benötigt keine externen Pakete (kein Mathlib).

### Aufbau

```text
lean-toolchain          Lean-Version (v4.35.0)
lakefile.toml           Lake-Projekt: eine Bibliothek „LeanSeminar“
LeanSeminar/
  Step1.lean            Arbeitsauftrag 1: #check, #eval, Fehlerarten
  Step2.lean            Arbeitsauftrag 2: Typ, Funktion, Proposition, Beweis
  Step3.lean            Arbeitsauftrag 3: Term- und Taktikbeweise (fun/intro, constructor, exact)
  Step4.lean            Arbeitsauftrag 4: double rekursiv, Induktionsbeweis double n = n + n
```

Die Dateien sind voneinander unabhängig. Jede ist in `lakefile.toml` unter `roots`
eingetragen und wird von `lake build` mitgeprüft.

### Prüfen

Mit einer installierten Lean-Toolchain ([Installation](https://lean-lang.org/install/))
im Wurzelverzeichnis:

```text
lake build
```

Zum interaktiven Arbeiten den Repo-Ordner in VS Code öffnen (mit der Lean-4-Erweiterung).
Die Ausgaben von `#check` und `#eval` erscheinen beim Öffnen einer Datei
im Lean-Infoview. Während eines unvollständigen Beweises zeigt der Infoview
den aktuellen Kontext und das offene Beweisziel. Ein Typfehler ist dagegen ein
Fehler in einem Ausdruck, ein offenes Beweisziel ein noch nicht fertiggestellter
Beweis, und ein falsch behaupteter Satz wird vom Kernel zurückgewiesen, sobald
kein gültiger Beweisterm dafür erstellt werden kann.

# ToDo:

## Zusätzliche Befehle zur Evaluation:
-- apply/hint 
-- example
-- sorry