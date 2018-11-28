.PHONY: setup test

all:
	echo "There is nothing to build. Use make test to run API tests"

setup:
	(cd dredd-test && npm install)

test:
	helpers/api-test.sh
