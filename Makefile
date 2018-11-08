CLIENT_DIR = client
SERVER_DIR = linting-server

# indicate, that submodules are not files
.PHONY: setup client linter test clean

all: server client

setup:
	$(MAKE) -C $(CLIENT_DIR) setup
	$(MAKE) -C $(SERVER_DIR) setup

# build instructions for submodules
client:
	$(MAKE) -C $(CLIENT_DIR)

server:
	$(MAKE) -C $(SERVER_DIR)

test:
	$(MAKE) -C $(CLIENT_DIR) test
	$(MAKE) -C $(SERVER_DIR) test

clean:
	$(MAKE) -C $(CLIENT_DIR) clean
	$(MAKE) -C $(SERVER_DIR) clean


