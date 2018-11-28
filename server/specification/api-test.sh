#!/bin/bash

echo "Preparing tests on server api..."

# Ensure server is already built
echo "Building server beforehand..."
make -C ..

# Run server without output in background
echo "Running server."
nohup make -C .. run > /dev/null 2>&1 &
serverPid=$!

# Busy waiting until server is ready
echo "Waiting for server to be ready..."
until [ "$(curl -s localhost:8080/actuator/health)" = "{\"status\":\"UP\"}" ]; do
    # Exit immediately, if it died
    kill -0 $serverPid
    serverDead=$?

    if [ $serverDead -ne 0 ]
    then
        echo "Server died, before api tests could start!"
        exit 1
    fi
    sleep 1
done

echo "Server is ready! Running api tests..."

# Run tests
(cd dredd-test && npm test)

# Capture exit code
testResult=$?

# Kill server
kill $serverPid

if [ $testResult -ne 0 ]
then
  echo "API tests failed."
  exit $testResult
fi

exit 0
