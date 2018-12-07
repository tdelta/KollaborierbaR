CLIENT_DIR = client
SERVER_DIR = server

# indicate, that submodules are not files
.PHONY: setup check pedantic client linter test clean

all: server client

# install dependencies etc.
setup:
	$(MAKE) -C $(CLIENT_DIR) setup
	$(MAKE) -C $(SERVER_DIR) setup

# run static analysis tools
check:
	$(MAKE) -C $(CLIENT_DIR) check
	$(MAKE) -C $(SERVER_DIR) check

# run static analysis tools in aggressive mode
pedantic:
	$(MAKE) -C $(CLIENT_DIR) pedantic
	$(MAKE) -C $(SERVER_DIR) pedantic

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


