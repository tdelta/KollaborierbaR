#!/bin/bash

# Since curl is not available everywhere, we have to improvise.
# This script will execute a GET request on the given host, port and URL
# Based on https://stackoverflow.com/a/5951459

host=$1
port=$2
url=$3

# Fail if any of the following commands fail
set -e

# Open socket on new file descriptor
exec 5<> "/dev/tcp/$host/$port"
# Read output from socket
cat <&5 &
catPid=$!
# Write GET request to socket
printf "GET $url HTTP/1.0\r\n\r\n\n" >&5
# wait for output to finish and close socket
wait $catPid
exec 5<&-
