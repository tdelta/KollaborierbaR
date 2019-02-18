.PHONY: setup check pedantic format run test clean

all:
	npm run-script build

# install dependencies etc.
setup:
	npm install

# run static analysis tools
check:
	npm run-script eslint
	npm run-script tslint

# fix linter errors automatically, if possible
fix:
	npm run-script eslint-fix
	npm run-script tslint-fix

# run static analysis tools in aggressive mode
pedantic:
	npm run-script eslint-pedantic
	npm run-script tslint

format:
	npm run-script format

# run project
run:
	npm start

# run unit tests
test:
	CI=true npm test

clean:
	npm run-script clean
