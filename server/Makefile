.PHONY: setup check run test clean format

all:
	./gradlew build

# install dependencies etc.
setup:
	# Specification tests need setup
	make -C specification setup

# run static analysis tools
check:
	./gradlew spotlessCheck
	./gradlew checkstyleMain
	./gradlew pmdMain
	./gradlew spotbugsMain

format:
	./gradlew spotlessApply

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
