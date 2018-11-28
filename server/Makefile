.PHONY: setup check pedantic run test clean

all:
	./gradlew build

# install dependencies etc.
setup:
	#No setup steps right now

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

# run project
run:
	./gradlew bootRun

# run unit and api tests
test:
	./gradlew test
	make -C specification test

clean:
	./gradlew clean
