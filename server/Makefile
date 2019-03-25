.PHONY: setup check run test clean format deploy

all:
	./gradlew build

# install dependencies etc.
setup:

# run static analysis tools
check:
	./gradlew spotlessCheck
	./gradlew checkstyleMain
	./gradlew pmdMain
	./gradlew spotbugsMain

# auto format java code
format:
	./gradlew spotlessApply

# run project
run:
	./gradlew bootRun

# run unit and api tests
test:
	./helpers/api-test.sh

clean:
	./gradlew clean

deploy:
	./gradlew bootJar
