#!/bin/bash

# This script essentially does the following:
#
# * build the server
# * run the server
# * wait until its ready
# * run the api tests
# * stop the server
#
# (There are some additional safety checks to avoid waiting forever.
#  It depends on the server reporting its ready status on /actuator/health
#  as "{"status":"UP"}"  (exact string match) )

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
tryCounter=0
until [ "$(helpers/get.sh localhost 8080 /actuator/health 2> /dev/null | tail -n1)" = "{\"status\":\"UP\"}" ]; do
    # Exit immediately, if it died
    kill -0 $serverPid
    serverDead=$?

    if [ $serverDead -ne 0 ]
    then
        echo "Server died, before api tests could start!"
        exit 1
    fi

    # Exit, if we tried more than 60s
    if [ $tryCounter -ge 60 ]
    then
        echo "Waiting for server more than a minute. Aborting."
        kill -9 $serverPid
        exit 1
    fi

    ((tryCounter++))

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
