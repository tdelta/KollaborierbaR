.PHONY: setup check format run test clean

all:
	./gradlew build

# install dependencies etc.
setup:
	# Specification tests need setup
	make -C specification setup

# run static analysis tools
check:
	./gradlew spotlessCheck
	./gradlew pmdMain
	./gradlew spotbugsMain
	./gradlew checkstyleMain

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
