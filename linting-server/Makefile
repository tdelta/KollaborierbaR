.PHONY: setup check run test clean

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

# run project
run:
	./gradlew bootRun

# run unit tests
test:
	./gradlew test

clean:
	./gradlew clean
