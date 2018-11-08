# Allgemeine Hinweise

Eine einheitliche Bedienung (bauen, ausführen, testen, ...) wird zu Zeit durch Makefiles realisiert:

* Nach dem Klonen definitiv mindestens einmal `make setup` im Hauptordner durchführen
* Die folgenden Befehle funktioniern sowohl in den Unterprojekten, als auch im Wurzelverzeichnis.
  Ihre Ausführung im Wurzelverzeichnis wird dann an alle Unterordner delegiert:
  * **bauen**: `make`
  * **ausführen**: `make run`
  * **Statische Analyse**: `make check`
  * **Unit tests**: `make test`
* Ein automatisierter Build mit statischer Analyse und Tests lässt sich im Wurzelverzeichnis durch `make pipeline`
  auslösen.

# Hinweise Client

## Dependencies
Seltsame "Dependency-Fehler"? `make setup`!

Um eine neue Bibliothek in den Dependencies aufzulisten, muss muss sie folgendermaßen installiert werden:
``npm install <package> --save``

## Website anzeigen

```sh
make run
```

Die Website kann im Browser unter localhost:3000 angezeigt werden

## Linting / Syntax checking

Damit Syntaxüberprüfungen etc. funktionieren, bitte Server starten

```sh
cd linting-server
make run
```
