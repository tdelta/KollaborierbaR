CLIENT_DIR = client
SERVER_DIR = server

# indicate, that submodules are not files
.PHONY: setup check format client linter test clean deploy

all: server client

# install dependencies etc.
# (will download submodules, if we are not running within a Jenkins instance)
setup:
	if [[ -z "${RUNNING_IN_JENKINS}" ]]; then \
		git submodule update --init --recursive; \
	fi;
	$(MAKE) -C $(CLIENT_DIR) setup
	$(MAKE) -C $(SERVER_DIR) setup

# run static analysis tools
check:
	$(MAKE) -C $(CLIENT_DIR) check
	$(MAKE) -C $(SERVER_DIR) check

# Run automatic source code formatters
format:
	$(MAKE) -C $(CLIENT_DIR) format
	$(MAKE) -C $(SERVER_DIR) format

# build
client:
	$(MAKE) -C $(CLIENT_DIR)

server:
	$(MAKE) -C $(SERVER_DIR)

# run unit tests
test:
	$(MAKE) -C $(CLIENT_DIR) test
	$(MAKE) -C $(SERVER_DIR) test

# run a complete ci pipeline, like the Jenkinsfile would
# (this needs to be updated, when the Jenkinsfile is updated)
pipeline: setup check all test

clean:
	$(MAKE) -C $(CLIENT_DIR) clean
	$(MAKE) -C $(SERVER_DIR) clean

deploy:
	$(MAKE) -C $(CLIENT_DIR) deploy
	$(MAKE) -C $(SERVER_DIR) deploy
	tools/createDeployable.sh

