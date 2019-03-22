.PHONY: setup check pedantic run test clean format

all:
	./gradlew build

# install dependencies etc.
setup:
	# Specification tests need setup
	make -C specification setup

# run static analysis tools
check:
	# run PMD tool
	./gradlew pmdMain
	# run Spotless coding style checker
	./gradlew spotlessCheck

# run static analysis tools in aggressive mode
pedantic:
	# run PMD tool
	./gradlew -b pedantic.gradle pmdMain
	# run Spotless coding style checker
	./gradlew -b pedantic.gradle spotlessCheck

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
