# Lean_Seminar
Seminararbeit LEAN4 Einführung anhand eines Beispiels

## Erster Versuch: Arbeitsauftrag 1

Das Projekt verwendet Lean `v4.19.0` und benötigt keine externen Pakete.

### Dateien und Befehle

- `Main.lean` enthält `#check`- und `#eval`-Beispiele sowie zwei kleine Beweise.
- `lean-toolchain` legt die verwendete Lean-Version fest.
- `lakefile.toml` beschreibt das ausführbare Projekt.

Mit einer installierten Lean-Toolchain lässt sich das Projekt prüfen mit:

```text
lake build
```

Die Ausgaben von `#check` und `#eval` erscheinen beim Öffnen von `Main.lean`
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