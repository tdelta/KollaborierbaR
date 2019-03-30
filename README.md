<p align="center">
	<img width="60%" src="logo.png"/>
</p>

[![Build Status](http://hudson.se.informatik.tu-darmstadt.de/buildStatus/icon?job=BP-KollaborierbaR)](http://hudson.se.informatik.tu-darmstadt.de/job/BP-KollaborierbaR/)

*KollaborierbaR* is a web-based IDE for collaboratively editing Java source code and running automated proofs of [JML](https://en.wikipedia.org/wiki/Java_Modeling_Language) specifications. *KollaborierbaRs* automated proof system is based on the [KeY project](https://www.key-project.org/).

# Quickstart 🚀

(requires python3 for running a local webserver and Java 8 for running the backend)

1. [Download](https://git.key-project.org/dsteinhoefel/kollaborierbar/raw/syncedConsole/deliverables/KollaborierbaR.tar.gz?inline=false) `KollaborierbaR.tar.gz` from the `deliverables` folder
2. **OR** build an up to date version yourself:

```sh
make setup
make deploy
cd deliverables
```

3. Extract the archive and run KollaborierbaR
```
tar -xf KollaborierbaR.tar.gz
cd KollaborierbaR
./run.sh
```

4. If you want others to join you in KollaborierbaR, stop the server, configure your public IP address in `config.js`, and restart it.

# KollaborierbaRs build system 🛠️

KollaborierbaR consists of 2 components, a web frontend (located in the `client` folder) and a backend server (see `server` folder).

A set of makefiles abstracts from the different tooling used in those projects. The following `make` commands are available:


|command        |effect                                                                   |
|---------------|-------------------------------------------------------------------------|
|`make setup`   |Download all dependencies required for building KollaborierbaR           |
|`make check`   |Run style checks and static analysis tools                               |
|`make`         |Build client and server                                                  |
|`make test`    |Run tests on the server API                                              |
|`make pipeline`|Run all of the above                                                     |
|`make deploy`  |Build a tar.gz archive, which makes it easy to distribute KollaborierbaR |
|`make format`  |Run automatic code formatters                                            |
|`make clean`   |Clean build artifacts                                                    |

**Remember to always run `make setup` first, after downloading the repository**

You can use all of the above commands (except for `deploy`) also within the `client` or `server` folders, so that the described effects only apply to the client or server respectively.
