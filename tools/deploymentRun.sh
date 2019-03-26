#!/bin/bash

trap ctrl_c INT

function ctrl_c() {
  echo "Stopping servers.."

  kill $backendPid
  kill $frontendPid

  echo "Stopped."
}

echo "Please configure the correct backend address in config.js if you have not done so yet."

echo

ip=$(sed -n "s/^.*http:\/\/\([^:]*\).*$/\1/p" config.js)
echo "You can use your browser to open KollaborierbaR at address $(tput bold)http://$ip:3000$(tput sgr0)"

echo

echo "Running backend server."
nohup java -jar KollaborierbaR-*.jar > /dev/null 2>&1 &
backendPid=$!

echo "Running frontend server."
nohup /usr/bin/env python3 -m http.server 3000 > /dev/null 2>&1 &
frontendPid=$!

wait $backendPid
wait $frontendPid
