.PHONY: setup check pedantic run test clean

all:
	npm run-script build

# install dependencies etc.
setup:
	npm install

# run static analysis tools
check:
	npm run-script lint

# run static analysis tools in aggressive mode
pedantic:
	#No special options here yet
	npm run-script lint

# run project
run:
	npm start

# run unit tests
test:
	CI=true npm test

clean:
	npm run-script clean
