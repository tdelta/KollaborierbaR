# Allgemeine Hinweise

Eine einheitliche Bedienung (bauen, ausführen, testen, ...) wird zur Zeit durch Makefiles realisiert:

* Nach dem Klonen definitiv mindestens einmal `make setup` im Hauptordner durchführen
* Die folgenden Befehle funktioniern sowohl in den Unterprojekten, als auch im Wurzelverzeichnis.
  Ihre Ausführung im Wurzelverzeichnis wird dann an alle Unterordner delegiert:
  * **bauen**: `make`
  * **ausführen**: `make run`
  * **statische Analyse**: `make check`
  * **statische Analyse im agressiven Modus**: `make pedantic`
  * **unit tests**: `make test`
* Ein automatisierter Build mit statischer Analyse und Tests lässt sich im Wurzelverzeichnis durch `make pipeline`
  auslösen.

## Git Hooks

Es wurden git-hook Skripte angelegt, welche einige Tests vor jedem Commit
automatisch ausführen. Der Commit kann nur gelingen, wenn alle Tests erfolgreich
verlaufen. Somit sollen die Skripte zur Vermeidung von Fehlern beitragen.

Lokales Installieren der Hooks:

```sh
hooks/helpers/install_hooks.sh
```

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
